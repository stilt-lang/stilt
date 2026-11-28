// @ts-check
// Debugging a program: the debug type `stilt` builds the program with `stilt build`, whose
// executables carry DWARF debug information, and runs it under LLDB DAP or CodeLLDB, whichever
// `stilt.debug.engine` picks, with breakpoints set in its `.lt` files. F5 in a Stilt file
// debugs its program without a `launch.json`, and the debug view offers each program of the
// workspace.

"use strict";

const fs = require("fs");
const os = require("os");
const path = require("path");
const vscode = require("vscode");
const { programOf, isProgram } = require("./programs");
const { stilt } = require("./show");

/** The debugger extensions that run a built program, by their debug type. */
const ENGINES = {
  "lldb-dap": { extension: "llvm-vs-code-extensions.lldb-dap", type: "lldb-dap", name: "LLDB DAP" },
  codelldb: { extension: "vadimcn.vscode-lldb", type: "lldb", name: "CodeLLDB" },
};

/** The engine the settings pick, among those installed, or `undefined` when none is. */
function engine() {
  const wanted = vscode.workspace.getConfiguration("stilt.debug").get("engine", "auto");
  const order = wanted === "auto" ? ["lldb-dap", "codelldb"] : [wanted];
  const key = order.find((k) => vscode.extensions.getExtension(ENGINES[/** @type {keyof ENGINES} */ (k)].extension));
  return key ? ENGINES[/** @type {keyof ENGINES} */ (key)] : undefined;
}

/**
 * The directory of a program that a configuration names: a directory, or a file's program.
 * @param {string | undefined} given
 */
function rootOf(given) {
  if (!given) {
    const editor = vscode.window.activeTextEditor;
    return editor ? programOf(editor.document.uri)?.uri.fsPath : undefined;
  }
  const stat = fs.existsSync(given) ? fs.statSync(given) : undefined;
  if (stat && stat.isFile()) {
    return isProgram(path.dirname(given)) ? path.dirname(given) : given;
  }
  return given;
}

/**
 * Builds the program at `root` for the debugger, and gives its executable.
 * @param {vscode.ExtensionContext} context
 * @param {string} root
 * @param {vscode.CancellationToken} [token]
 */
async function built(context, root, token) {
  const storage = (context.storageUri || context.globalStorageUri).fsPath;
  const dir = path.join(storage, "debug");
  await fs.promises.mkdir(dir, { recursive: true });
  const name = path.basename(root, ".lt");
  const output = path.join(dir, os.platform() === "win32" ? `${name}.exe` : name);
  const title = `Building ${name} for the debugger`;
  const out = await vscode.window.withProgress({ location: vscode.ProgressLocation.Notification, title, cancellable: true }, (_, cancel) =>
    stilt(vscode.Uri.file(root), ["build", "-o", output, root], fs.statSync(root).isFile() ? path.dirname(root) : root, cancel || token),
  );
  return out.status === 0 ? output : { error: out.stderr.trim() || out.stdout.trim() };
}

/**
 * @param {vscode.ExtensionContext} context
 * @param {import("./install").Installer} installer
 * @returns {vscode.DebugConfigurationProvider}
 */
function resolver(context, installer) {
  return {
    provideDebugConfigurations(folder) {
      return [{ type: "stilt", request: "launch", name: "Debug the program", program: folder ? folder.uri.fsPath : "${workspaceFolder}" }];
    },
    async resolveDebugConfigurationWithSubstitutedVariables(_folder, config, token) {
      if (!vscode.workspace.isTrusted) {
        vscode.window.showWarningMessage("Stilt: trust this workspace to build and debug its programs.");
        return undefined;
      }
      const root = rootOf(config.program);
      if (!root) {
        vscode.window.showWarningMessage("Stilt: open a file of a program, or name it with `program`, to debug it.");
        return undefined;
      }
      if (!(await installer.ready(vscode.Uri.file(root)))) {
        return undefined;
      }
      const chosen = engine();
      if (!chosen) {
        vscode.window.showErrorMessage("Stilt: debugging needs LLDB DAP or CodeLLDB.", "Install LLDB DAP").then((c) => {
          if (c) {
            vscode.commands.executeCommand("workbench.extensions.search", ENGINES["lldb-dap"].extension);
          }
        });
        return undefined;
      }
      const exe = await built(context, root, token);
      if (typeof exe !== "string") {
        const first = exe.error.split("\n").find((l) => l.trim()) || "the build failed";
        vscode.window.showErrorMessage(`Stilt: ${path.basename(root)} doesn't build: ${first}`, "Show Problems").then((c) => {
          if (c) {
            vscode.commands.executeCommand("workbench.actions.view.problems");
          }
        });
        return undefined;
      }
      const cwd = config.cwd || (fs.statSync(root).isFile() ? path.dirname(root) : root);
      return { type: chosen.type, request: "launch", name: config.name || `Debug ${path.basename(root)}`, program: exe, args: config.args || [], cwd };
    },
  };
}

/**
 * Debugs the program of the active file, or the one a code lens names.
 * @param {vscode.Uri} [root]
 */
async function debugProgram(root) {
  const editor = vscode.window.activeTextEditor;
  const program = root ? root.fsPath : editor && programOf(editor.document.uri)?.uri.fsPath;
  if (!program) {
    vscode.window.showWarningMessage("Stilt: open a file of a program to debug it.");
    return;
  }
  const folder = vscode.workspace.getWorkspaceFolder(vscode.Uri.file(program));
  await vscode.debug.startDebugging(folder, { type: "stilt", request: "launch", name: `Debug ${path.basename(program)}`, program });
}

/**
 * @param {vscode.ExtensionContext} context
 * @param {import("./install").Installer} installer
 */
function register(context, installer) {
  const provider = resolver(context, installer);
  /** @type {vscode.DebugConfigurationProvider} */
  const dynamic = {
    provideDebugConfigurations() {
      const roots = new Set();
      for (const d of vscode.workspace.textDocuments) {
        const p = d.languageId === "stilt" ? programOf(d.uri) : undefined;
        if (p) {
          roots.add(p.uri.fsPath);
        }
      }
      return [...roots].map((program) => ({ type: "stilt", request: "launch", name: `Debug ${path.basename(program)}`, program }));
    },
  };
  context.subscriptions.push(
    vscode.debug.registerDebugConfigurationProvider("stilt", provider),
    vscode.debug.registerDebugConfigurationProvider("stilt", dynamic, vscode.DebugConfigurationProviderTriggerKind.Dynamic),
    vscode.commands.registerCommand("stilt.debug", debugProgram),
  );
}

module.exports = { register };
