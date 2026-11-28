// @ts-check
// Stilt for Visual Studio Code. It finds `stilt` (./toolchain.js, ./locate.js), offers to
// install or update it (./install.js), starts a language server for each program whose files
// are open (./programs.js) and adjusts its answers (./middleware.js), and adds the language
// status (./status.js) and its menu (./menu.js), the documents of `stilt show` and the
// explanations of diagnostics (./show.js), the causes of facts at the cursor's line
// (./causes.js), the Test Explorer's tests (./tests.js), the tasks (./tasks.js), the debugger
// (./debug.js), the code lenses above `main` (./lenses.js) and **New Project** (./project.js).

"use strict";

const path = require("path");
const vscode = require("vscode");
const { Programs, programOf } = require("./programs");
const { Installer } = require("./install");
const { toolchain } = require("./toolchain");

/** The settings whose change restarts the servers, which look for `stilt` again. */
const RESTARTING = ["stilt.path", "stilt.env", "stilt.server.enable"];

/** @type {Programs | undefined} */
let programs;

/**
 * Opens the manifest of the active file's program, `stilt.toml`, if it has one.
 */
async function openManifest() {
  const editor = vscode.window.activeTextEditor;
  const program = editor && programOf(editor.document.uri);
  if (!program) {
    vscode.window.showWarningMessage("Stilt: open a file of a program first.");
    return;
  }
  const manifest = vscode.Uri.file(path.join(program.uri.fsPath, "stilt.toml"));
  try {
    await vscode.window.showTextDocument(manifest);
  } catch {
    vscode.window.showInformationMessage(`Stilt: ${program.name} has no manifest. A program needs one only to name itself or its dependencies.`);
  }
}

/**
 * Lets the integrated terminal find the `stilt` the extension found, when the editor's `PATH`
 * lacks its directory, as it does when `~/.stilt/bin` was added to the shell's profile after the
 * editor started. The directory goes last, so it never hides another `stilt`, and one that
 * `stilt.path` names, such as a build directory, is left out.
 * @param {vscode.ExtensionContext} context
 * @param {import("./locate").Found} found
 */
function terminalPath(context, found) {
  const terminals = context.environmentVariableCollection;
  terminals.persistent = false;
  terminals.description = "Adds the directory of the `stilt` that the Stilt extension runs to the PATH";
  const usable = (found.kind === "found" || found.kind === "outdated") && found.source !== "stilt.path";
  const dir = usable ? path.dirname(found.path) : undefined;
  const onPath = (process.env.PATH || "").split(path.delimiter).includes(dir || "");
  if (dir && !onPath) {
    terminals.append("PATH", `${path.delimiter}${dir}`);
  } else {
    terminals.delete("PATH");
  }
}

/** @param {vscode.ExtensionContext} context */
function activate(context) {
  const log = vscode.window.createOutputChannel("Stilt", { log: true });
  toolchain.log = log;
  const all = new Programs(log);
  programs = all;
  const installer = new Installer(log, () => all.restart());
  all.offer = (found) => installer.offer(found);
  vscode.commands.executeCommand("setContext", "stilt:activated", true);
  require("./status").register(context, all);
  require("./menu").register(context);
  require("./show").register(context, all);
  require("./causes").register(context, all);
  require("./tests").register(context, installer);
  require("./tasks").register(context, installer);
  require("./debug").register(context, installer);
  require("./lenses").register(context);
  require("./project").register(context, installer);
  context.subscriptions.push(
    log,
    toolchain,
    toolchain.onDidChange((found) => terminalPath(context, found)),
    vscode.workspace.onDidOpenTextDocument((d) => all.open(d)),
    vscode.workspace.onDidChangeWorkspaceFolders((change) => {
      all.removed(change.removed);
      all.openAll();
    }),
    vscode.workspace.onDidChangeConfiguration((change) => {
      if (RESTARTING.some((s) => change.affectsConfiguration(s))) {
        installer.offered.clear();
        all.restart();
      }
    }),
    vscode.workspace.onDidGrantWorkspaceTrust(() => all.restart()),
    vscode.commands.registerCommand("stilt.restart", () => {
      installer.offered.clear();
      return all.restart();
    }),
    vscode.commands.registerCommand("stilt.showLogs", () => log.show()),
    vscode.commands.registerCommand("stilt.openManifest", openManifest),
    vscode.commands.registerCommand("stilt.install", () => installer.install()),
    vscode.commands.registerCommand("stilt.locate", () => installer.locate()),
    vscode.commands.registerCommand("stilt.checkForUpdates", () => installer.checkForUpdates()),
  );
  all.openAll();
}

function deactivate() {
  return programs?.dispose();
}

module.exports = { activate, deactivate };
