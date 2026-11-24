// @ts-check
// The programs of the workspace, each served by a `stilt lsp` of its own. A program is the
// nearest directory above a file that holds a `stilt.toml` or a `main.lt`, no higher than the
// file's workspace folder, as `stilt check` reads a directory program, so a workspace may hold
// several anywhere in it. Each server answers with the engine of its program, which the command
// line shares (goal one-engine), and a file outside any program gets highlighting alone.

"use strict";

const fs = require("fs");
const path = require("path");
const vscode = require("vscode");
const lc = require("vscode-languageclient/node");
const { middleware } = require("./middleware");

/**
 * A program: the directory that holds it, its name, and the workspace folder it is in.
 * @typedef {{ uri: vscode.Uri, name: string, folder: vscode.WorkspaceFolder | undefined }} Program
 */

/** The files whose change on disk the server hears of, so that it checks the program again. */
const WATCHED = "**/{*.lt,stilt.toml,docs.lock}";

/** @param {string} dir */
function isProgram(dir) {
  return ["main.lt", "stilt.toml"].some((name) => fs.existsSync(path.join(dir, name)));
}

/**
 * The program that holds a file, if any.
 * @param {vscode.Uri} uri
 * @returns {Program | undefined}
 */
function programOf(uri) {
  if (uri.scheme !== "file") {
    return undefined;
  }
  const folder = vscode.workspace.getWorkspaceFolder(uri);
  const top = folder ? folder.uri.fsPath : path.parse(uri.fsPath).root;
  for (let dir = path.dirname(uri.fsPath); ; dir = path.dirname(dir)) {
    if (isProgram(dir)) {
      return { uri: vscode.Uri.file(dir), name: path.basename(dir), folder };
    }
    if (dir === top || path.dirname(dir) === dir) {
      return undefined;
    }
  }
}

/**
 * The `stilt` binary that the settings name for a program.
 * @param {vscode.Uri} [scope]
 */
function binary(scope) {
  const named = vscode.workspace.getConfiguration("stilt", scope).get("path", "stilt") || "stilt";
  if (path.isAbsolute(named) || !named.includes(path.sep)) {
    return named;
  }
  const folder = scope && vscode.workspace.getWorkspaceFolder(scope);
  return folder ? path.join(folder.uri.fsPath, named) : named;
}

/** The language servers of the programs whose files are open, and the events of their states. */
class Programs {
  /** @param {vscode.LogOutputChannel} log */
  constructor(log) {
    this.log = log;
    /** @type {Map<string, { client: lc.LanguageClient, program: Program, watcher: vscode.FileSystemWatcher }>} */
    this.servers = new Map();
    this.changed = new vscode.EventEmitter();
    /** Fires when a server starts, stops or fails, with the program it serves. */
    this.onDidChange = this.changed.event;
  }

  /**
   * The server of the program that holds a document, once it runs, with the program.
   * @param {vscode.TextDocument | vscode.Uri} of
   */
  serving(of) {
    const uri = of instanceof vscode.Uri ? of : of.uri;
    const program = programOf(uri);
    const server = program && this.servers.get(program.uri.toString());
    return server && server.client.state === lc.State.Running ? server : undefined;
  }

  /**
   * The state of the server of the program that holds a document.
   * @param {vscode.TextDocument} document
   * @returns {{ program: Program, state: "starting" | "running" | "stopped", version?: string } | undefined}
   */
  state(document) {
    const program = programOf(document.uri);
    if (!program) {
      return undefined;
    }
    const server = this.servers.get(program.uri.toString());
    if (!server) {
      return { program, state: "stopped" };
    }
    const states = { [lc.State.Starting]: "starting", [lc.State.Running]: "running", [lc.State.Stopped]: "stopped" };
    const version = server.client.initializeResult?.serverInfo?.version;
    return { program, state: /** @type {any} */ (states[server.client.state]), version };
  }

  /**
   * Starts the server of the program that holds a Stilt document, if it holds one.
   * @param {vscode.TextDocument} document
   */
  open(document) {
    const program = document.languageId === "stilt" ? programOf(document.uri) : undefined;
    if (program) {
      this.start(program);
    }
  }

  /** Starts the servers of the programs of every open document and workspace folder. */
  openAll() {
    for (const folder of vscode.workspace.workspaceFolders || []) {
      if (folder.uri.scheme === "file" && isProgram(folder.uri.fsPath)) {
        this.start({ uri: folder.uri, name: folder.name, folder });
      }
    }
    vscode.workspace.textDocuments.forEach((d) => this.open(d));
  }

  /** @param {Program} program */
  start(program) {
    const key = program.uri.toString();
    if (this.servers.has(key)) {
      return;
    }
    const command = binary(program.uri);
    const run = { command, args: ["lsp"], options: { cwd: program.uri.fsPath } };
    const watcher = vscode.workspace.createFileSystemWatcher(new vscode.RelativePattern(program.uri, WATCHED));
    const client = new lc.LanguageClient("stilt", `Stilt (${program.name})`, { run, debug: run }, {
      documentSelector: [{ scheme: "file", language: "stilt", pattern: `${program.uri.fsPath}/**/*` }],
      // The server's root is the program's directory, which a workspace folder may hold.
      workspaceFolder: { uri: program.uri, name: program.name, index: program.folder ? program.folder.index : 0 },
      outputChannel: this.log,
      revealOutputChannelOn: lc.RevealOutputChannelOn.Never,
      synchronize: { fileEvents: watcher },
      middleware: middleware(),
      errorHandler: this.errors(program),
    });
    this.servers.set(key, { client, program, watcher });
    client.onDidChangeState(() => this.changed.fire(program));
    this.log.info(`starting \`${command} lsp\` for ${program.uri.fsPath}`);
    client.start().then(
      () => this.changed.fire(program),
      (/** @type {Error} */ error) => this.failed(program, command, error),
    );
  }

  /**
   * What happens when a server fails: an error is logged and the server goes on, and a server
   * that ends is started again, up to three times in three minutes.
   * @param {Program} program
   * @returns {lc.ErrorHandler}
   */
  errors(program) {
    /** @type {number[]} */
    const ends = [];
    return {
      error: (error) => {
        this.log.error(`${program.name}: ${error.message}`);
        return { action: lc.ErrorAction.Continue };
      },
      closed: () => {
        const now = Date.now();
        ends.push(now);
        while (ends.length && now - ends[0] > 3 * 60 * 1000) {
          ends.shift();
        }
        if (ends.length <= 3) {
          this.log.warn(`${program.name}: the language server ended, and starts again`);
          return { action: lc.CloseAction.Restart };
        }
        this.offerRestart(`Stilt: the language server of ${program.name} ended four times in three minutes.`);
        return { action: lc.CloseAction.DoNotRestart, handled: true };
      },
    };
  }

  /**
   * @param {Program} program
   * @param {string} command
   * @param {Error} error
   */
  async failed(program, command, error) {
    this.servers.get(program.uri.toString())?.watcher.dispose();
    this.servers.delete(program.uri.toString());
    this.changed.fire(program);
    this.log.error(`cannot start \`${command} lsp\` for ${program.name}: ${error.message}`);
    const locate = "Locate stilt…";
    const choice = await vscode.window.showErrorMessage(
      `Stilt: cannot start \`${command} lsp\`: ${error.message}. Set \`stilt.path\` to the stilt binary.`,
      locate,
      "Open Settings",
    );
    if (choice === locate) {
      const picked = await vscode.window.showOpenDialog({ canSelectMany: false, openLabel: "Use this stilt" });
      if (picked && picked[0]) {
        await vscode.workspace.getConfiguration("stilt").update("path", picked[0].fsPath, vscode.ConfigurationTarget.Global);
      }
    } else if (choice === "Open Settings") {
      await vscode.commands.executeCommand("workbench.action.openSettings", "stilt.path");
    }
  }

  /** @param {string} message */
  async offerRestart(message) {
    const choice = await vscode.window.showErrorMessage(message, "Restart", "Show Logs");
    if (choice === "Restart") {
      await this.restart();
    } else if (choice === "Show Logs") {
      this.log.show();
    }
  }

  /** @param {Program} program */
  async stop(program) {
    const key = program.uri.toString();
    const server = this.servers.get(key);
    this.servers.delete(key);
    if (server) {
      server.watcher.dispose();
      await server.client.stop().catch((/** @type {Error} */ e) => this.log.warn(e.message));
    }
    this.changed.fire(program);
  }

  /** Restarts every server, after a rebuild of `stilt` for example. */
  async restart() {
    const running = [...this.servers.values()].map((s) => s.program);
    await Promise.all(running.map((p) => this.stop(p)));
    running.forEach((p) => this.start(p));
    this.openAll();
  }

  /** Stops the servers of the programs inside workspace folders that were removed.
   * @param {readonly vscode.WorkspaceFolder[]} removed */
  async removed(removed) {
    const gone = [...this.servers.values()]
      .map((s) => s.program)
      .filter((p) => removed.some((f) => p.uri.fsPath.startsWith(f.uri.fsPath)));
    await Promise.all(gone.map((p) => this.stop(p)));
  }

  dispose() {
    return Promise.all([...this.servers.values()].map((s) => this.stop(s.program)));
  }
}

module.exports = { Programs, programOf, binary, isProgram };
