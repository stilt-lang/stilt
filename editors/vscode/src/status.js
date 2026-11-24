// @ts-check
// The language status of the active Stilt file, beside the language's name in the status
// bar: the state of its program's language server, and its module with the module's tier,
// which the compiler infers and the tools show (program.module-tier). Either may be pinned. It also
// keeps the context key `stilt:inProgram`, which the menus read, true when a program holds the
// active file.

"use strict";

const vscode = require("vscode");

/** How long an edit must settle before the module's tier, which it may change, is asked for again. */
const SETTLE = 250;

/**
 * @param {vscode.ExtensionContext} context
 * @param {import("./programs").Programs} programs
 */
function register(context, programs) {
  const selector = { language: "stilt" };
  const server = vscode.languages.createLanguageStatusItem("stilt.server", selector);
  server.name = "Stilt Language Server";
  const module = vscode.languages.createLanguageStatusItem("stilt.module", selector);
  module.name = "Stilt Module";
  /** @type {NodeJS.Timeout | undefined} */
  let timer;

  const update = async () => {
    const editor = vscode.window.activeTextEditor;
    const found = editor && editor.document.languageId === "stilt" ? programs.state(editor.document) : undefined;
    vscode.commands.executeCommand("setContext", "stilt:inProgram", Boolean(found));
    if (!editor || !found) {
      server.text = "No program";
      server.detail = "No stilt.toml or main.lt holds this file: it is highlighted only";
      server.severity = vscode.LanguageStatusSeverity.Information;
      server.busy = false;
      server.command = undefined;
      module.text = "";
      return;
    }
    const { program, state, version } = found;
    server.busy = state === "starting";
    server.severity = state === "stopped" ? vscode.LanguageStatusSeverity.Error : vscode.LanguageStatusSeverity.Information;
    server.text = { starting: "Starting", running: version ? `stilt ${version}` : "stilt", stopped: "Stopped" }[state];
    server.detail = `The language server of ${program.name}, ${program.uri.fsPath}`;
    server.command = { title: "Restart", command: "stilt.restart" };
    const running = programs.serving(editor.document);
    if (!running) {
      module.text = "";
      return;
    }
    const params = { textDocument: { uri: editor.document.uri.toString() }, position: editor.selection.active };
    const at = await running.client.sendRequest("stilt/whereabouts", params).catch(() => undefined);
    module.text = at ? `$(symbol-namespace) ${at.module}: ${at.tier}` : "";
    module.detail = at ? `The module's tier, the first that allows every feature it uses` : undefined;
    module.command = at ? { title: "Show Skeleton", command: "stilt.showModule" } : undefined;
  };
  const soon = () => {
    clearTimeout(timer);
    timer = setTimeout(update, SETTLE);
  };

  context.subscriptions.push(
    server,
    module,
    programs.onDidChange(() => update()),
    vscode.window.onDidChangeActiveTextEditor(() => update()),
    vscode.workspace.onDidChangeTextDocument((e) => e.document.languageId === "stilt" && soon()),
  );
  update();
}

module.exports = { register };
