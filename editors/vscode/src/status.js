// @ts-check
// The language status of the active Stilt file, beside the language's name in the status
// bar: the toolchain's version and the state of its program's language server, whose link
// opens the menu of ./menu.js, or installs or updates Stilt when it is missing or too old; and
// its module with the module's tier, which the compiler infers and the tools show
// (program.module-tier). Either may be pinned. It also keeps the context key `stilt:inProgram`,
// which the menus read, true when a program holds the active file.

"use strict";

const vscode = require("vscode");
const { NEEDS } = require("./locate");
const { toolchain } = require("./toolchain");

/** How long an edit must settle before the module's tier, which it may change, is asked for again. */
const SETTLE = 250;

const { Information, Warning, Error: Failure } = vscode.LanguageStatusSeverity;

/**
 * What the server's item says: its text, detail, severity, whether it is busy, and its link.
 * @param {ReturnType<import("./programs").Programs["state"]>} at the active file's program and its server
 * @param {import("./locate").Found | undefined} found the toolchain
 */
function describe(at, found) {
  const manage = { title: "Manage", command: "stilt.menu" };
  if (!found || at?.state === "looking") {
    return { text: "Looking for stilt", detail: "", severity: Information, busy: true, command: manage };
  }
  if (found.kind === "missing" && found.configured) {
    return { text: "stilt not found", detail: `\`stilt.path\` names ${found.configured}`, severity: Failure, busy: false, command: { title: "Locate", command: "stilt.locate" } };
  }
  if (found.kind === "missing") {
    return { text: "stilt not found", detail: "Install Stilt for the language server", severity: Failure, busy: false, command: { title: "Install", command: "stilt.install" } };
  }
  if (found.kind === "broken") {
    return { text: "stilt doesn't run", detail: found.path, severity: Failure, busy: false, command: { title: "Show Logs", command: "stilt.showLogs" } };
  }
  const text = `stilt ${found.version}`;
  if (found.kind === "outdated" && at?.state !== "stopped") {
    return { text, detail: `Older than the ${NEEDS} this extension needs`, severity: Warning, busy: at?.state === "starting", command: { title: "Update", command: "stilt.install" } };
  }
  if (!at) {
    return { text, detail: "No stilt.toml or main.lt holds this file: it is highlighted only", severity: Information, busy: false, command: manage };
  }
  const where = `${at.program.name}, ${at.program.uri.fsPath}`;
  switch (at.state) {
    case "off":
      return { text, detail: "The language server is off: `stilt.server.enable`", severity: Information, busy: false, command: manage };
    case "stopped":
      return { text: "Server stopped", detail: `The language server of ${where}: see the logs`, severity: Failure, busy: false, command: { title: "Restart", command: "stilt.restart" } };
    case "starting":
      return { text, detail: `Starting the language server of ${where}`, severity: Information, busy: true, command: manage };
    default:
      return { text, detail: `The language server of ${where}`, severity: Information, busy: false, command: manage };
  }
}

/**
 * @param {vscode.ExtensionContext} context
 * @param {import("./programs").Programs} programs
 */
function register(context, programs) {
  const selector = { language: "stilt" };
  const server = vscode.languages.createLanguageStatusItem("stilt.server", selector);
  server.name = "Stilt";
  const module = vscode.languages.createLanguageStatusItem("stilt.module", selector);
  module.name = "Stilt Module";
  /** @type {NodeJS.Timeout | undefined} */
  let timer;

  const update = async () => {
    const editor = vscode.window.activeTextEditor;
    const stilt = editor && editor.document.languageId === "stilt" ? editor.document : undefined;
    const at = stilt ? programs.state(stilt) : undefined;
    vscode.commands.executeCommand("setContext", "stilt:inProgram", Boolean(at));
    if (!stilt) {
      return;
    }
    const scope = at ? at.program.uri : stilt.uri;
    const found = toolchain.current(scope);
    if (!found) {
      // A file outside every program starts no server, which would look for `stilt`; the
      // lookup's end updates this item again.
      toolchain.resolve(scope);
    }
    Object.assign(server, describe(at, found));
    const running = programs.serving(stilt);
    if (!running) {
      module.text = "";
      return;
    }
    const params = { textDocument: { uri: stilt.uri.toString() }, position: /** @type {vscode.TextEditor} */ (editor).selection.active };
    const where = await running.client.sendRequest("stilt/whereabouts", params).catch(() => undefined);
    module.text = where ? `$(symbol-namespace) ${where.module}: ${where.tier}` : "";
    module.detail = where ? `The module's tier, the first that allows every feature it uses` : undefined;
    module.command = where ? { title: "Show Skeleton", command: "stilt.showModule" } : undefined;
  };
  const soon = () => {
    clearTimeout(timer);
    timer = setTimeout(update, SETTLE);
  };

  context.subscriptions.push(
    server,
    module,
    programs.onDidChange(() => update()),
    toolchain.onDidChange(() => update()),
    vscode.window.onDidChangeActiveTextEditor(() => update()),
    vscode.workspace.onDidChangeTextDocument((e) => e.document.languageId === "stilt" && soon()),
  );
  update();
}

module.exports = { register };
