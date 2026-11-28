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
const { toolchain, binary } = require("./toolchain");

/**
 * A program: the directory that holds it, its name, and the workspace folder it is in.
 * @typedef {{ uri: vscode.Uri, name: string, folder: vscode.WorkspaceFolder | undefined }} Program
 */

/**
 * The state of a program's server: waiting for the lookup of `stilt`, starting, running,
 * stopped after a failure, switched off by `stilt.server.enable`, or not started because no
 * `stilt` that runs was found.
 * @typedef {"looking" | "starting" | "running" | "stopped" | "off" | "unusable"} State
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

/** Whether `stilt.server.enable` lets the language servers run. */
function enabled() {
  return vscode.workspace.getConfiguration("stilt").get("server.enable", true);
}

/**
 * Why a server failed to start. The language client may reject with no error at all, having
 * logged the reason to the output itself.
 * @param {unknown} error
 */
function reason(error) {
  if (error && typeof error === "object" && "message" in error && error.message) {
    return String(error.message);
  }
  return error ? String(error) : "the reason is in the Stilt output";
}

/** The language servers of the programs whose files are open, and the events of their states. */
class Programs {
  /** @param {vscode.LogOutputChannel} log */
  constructor(log) {
    this.log = log;
    /** @type {Map<string, { client: lc.LanguageClient, program: Program, watcher: vscode.FileSystemWatcher }>} */
    this.servers = new Map();
    /** The programs whose servers wait for the lookup of `stilt`. @type {Set<string>} */
    this.pending = new Set();
    /** Counts the restarts, so that a start that waited across one gives up. */
    this.generation = 0;
    /** Whether a failure to start was shown since the last restart, so it shows once. */
    this.reported = false;
    /** What to offer when `stilt` can't be used, which ./install.js sets.
     * @type {(found: import("./locate").Found) => void} */
    this.offer = () => {};
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
   * @returns {{ program: Program, state: State } | undefined}
   */
  state(document) {
    const program = programOf(document.uri);
    if (!program) {
      return undefined;
    }
    const key = program.uri.toString();
    const server = this.servers.get(key);
    if (server) {
      const states = { [lc.State.Starting]: "starting", [lc.State.Running]: "running", [lc.State.Stopped]: "stopped" };
      return { program, state: /** @type {State} */ (states[server.client.state]) };
    }
    const found = toolchain.current(program.uri);
    if (!enabled()) {
      return { program, state: "off" };
    }
    if (this.pending.has(key) || !found) {
      return { program, state: "looking" };
    }
    return { program, state: found.kind === "missing" || found.kind === "broken" ? "unusable" : "stopped" };
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

  /**
   * Starts the server of a program once `stilt` is found, unless `stilt.server.enable` is off or
   * no `stilt` that runs is found, which ./install.js then offers to install.
   * @param {Program} program
   */
  async start(program) {
    const key = program.uri.toString();
    if (this.servers.has(key) || this.pending.has(key) || !enabled()) {
      return;
    }
    const generation = this.generation;
    this.pending.add(key);
    this.changed.fire(program);
    const found = await toolchain.resolve(program.uri);
    this.pending.delete(key);
    if (generation !== this.generation || this.servers.has(key)) {
      return;
    }
    if (found.kind !== "found" && found.kind !== "outdated") {
      this.changed.fire(program);
      this.offer(found);
      return;
    }
    if (found.kind === "outdated") {
      this.offer(found);
    }
    this.launch(program, found.path);
  }

  /**
   * @param {Program} program
   * @param {string} command the `stilt` found
   */
  launch(program, command) {
    const key = program.uri.toString();
    const run = { command, args: ["lsp"], options: { cwd: program.uri.fsPath, env: toolchain.env(program.uri) } };
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
      (/** @type {unknown} */ error) => this.failed(program, command, error),
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
   * Logs a server that can't start, and says so once until the next restart.
   * @param {Program} program
   * @param {string} command
   * @param {unknown} error
   */
  async failed(program, command, error) {
    const server = this.servers.get(program.uri.toString());
    this.servers.delete(program.uri.toString());
    server?.watcher.dispose();
    this.changed.fire(program);
    this.log.error(`cannot start \`${command} lsp\` for ${program.name}: ${reason(error)}`);
    if (!this.reported) {
      this.reported = true;
      await this.offerRestart(`Stilt: the language server of ${program.name} can't start: ${reason(error)}`);
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

  /** Restarts every server, after a rebuild of `stilt` for example, looking for it again. */
  async restart() {
    this.generation += 1;
    this.pending.clear();
    this.reported = false;
    toolchain.forget();
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
