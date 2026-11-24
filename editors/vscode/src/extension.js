// @ts-check
// Stilt for Visual Studio Code. It starts a language server for each program whose files are
// open (./programs.js) and adjusts its answers (./middleware.js), and adds the language status
// (./status.js), the documents of `stilt show` and the explanations of diagnostics
// (./show.js), the causes of facts at the cursor's line (./causes.js), the Test Explorer's
// tests (./tests.js), the tasks (./tasks.js), the debugger (./debug.js) and the code lenses
// above `main` (./lenses.js).

"use strict";

const path = require("path");
const vscode = require("vscode");
const { Programs, programOf } = require("./programs");

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

/** @param {vscode.ExtensionContext} context */
function activate(context) {
  const log = vscode.window.createOutputChannel("Stilt", { log: true });
  const all = new Programs(log);
  programs = all;
  require("./status").register(context, all);
  require("./show").register(context, all);
  require("./causes").register(context, all);
  require("./tests").register(context);
  require("./tasks").register(context);
  require("./debug").register(context);
  require("./lenses").register(context);
  context.subscriptions.push(
    log,
    vscode.workspace.onDidOpenTextDocument((d) => all.open(d)),
    vscode.workspace.onDidChangeWorkspaceFolders((change) => {
      all.removed(change.removed);
      all.openAll();
    }),
    vscode.workspace.onDidChangeConfiguration((change) => {
      if (change.affectsConfiguration("stilt.path")) {
        all.restart();
      }
    }),
    vscode.workspace.onDidGrantWorkspaceTrust(() => all.restart()),
    vscode.commands.registerCommand("stilt.restart", () => all.restart()),
    vscode.commands.registerCommand("stilt.showLogs", () => log.show()),
    vscode.commands.registerCommand("stilt.openManifest", openManifest),
  );
  all.openAll();
}

function deactivate() {
  return programs?.dispose();
}

module.exports = { activate, deactivate };
