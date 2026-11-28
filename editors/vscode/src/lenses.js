// @ts-check
// **Run** and **Debug** above each program's `main`: the one of the program's `main.lt`, or of
// a program of one file. `stilt.codeLens.enable` switches both off, and `stilt.codeLens.run` and
// `stilt.codeLens.debug` each.

"use strict";

const path = require("path");
const vscode = require("vscode");
const { programOf } = require("./programs");

/** The line that declares a program's entry point (program.main). */
const MAIN = /^\s*fn\s+main\s*\(/;

/** @type {vscode.CodeLensProvider & { changed: vscode.EventEmitter<void> }} */
const lenses = {
  changed: new vscode.EventEmitter(),
  get onDidChangeCodeLenses() {
    return this.changed.event;
  },
  provideCodeLenses(document) {
    const settings = vscode.workspace.getConfiguration("stilt.codeLens", document);
    const run = settings.get("run", true);
    const debug = settings.get("debug", true);
    if (!settings.get("enable", true) || (!run && !debug)) {
      return [];
    }
    const program = programOf(document.uri);
    if (!program || path.basename(document.uri.fsPath) !== "main.lt" || path.dirname(document.uri.fsPath) !== program.uri.fsPath) {
      return [];
    }
    for (let line = 0; line < document.lineCount; line++) {
      if (MAIN.test(document.lineAt(line).text)) {
        const range = new vscode.Range(line, 0, line, 0);
        return [
          run && new vscode.CodeLens(range, { title: "$(play) Run", command: "stilt.run", arguments: [program.uri], tooltip: `stilt run ${program.name}` }),
          debug && new vscode.CodeLens(range, { title: "$(debug-alt) Debug", command: "stilt.debug", arguments: [program.uri], tooltip: `Build ${program.name} and debug it` }),
        ].filter((lens) => lens instanceof vscode.CodeLens);
      }
    }
    return [];
  },
};

/** @param {vscode.ExtensionContext} context */
function register(context) {
  context.subscriptions.push(
    lenses.changed,
    vscode.languages.registerCodeLensProvider({ language: "stilt", scheme: "file" }, lenses),
    vscode.workspace.onDidChangeConfiguration((e) => e.affectsConfiguration("stilt.codeLens") && lenses.changed.fire()),
  );
}

module.exports = { register };
