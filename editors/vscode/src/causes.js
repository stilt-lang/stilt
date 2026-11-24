// @ts-check
// What the line that holds the cursor does that causes its function's facts, at the line's end,
// as `stilt show` writes it in a comment, such as `// an interpolated string allocates` (modes.show; facts.visibility). The language server gives every line's as inlay hints, and with
// `stilt.inlayHints.causes` set to `cursorLine`, the default, the extension keeps the cursor
// line's alone, so that a reader sees why a fact holds where they look without a hint at the end
// of every line.

"use strict";

const vscode = require("vscode");

/** How long the cursor must rest on a line before its causes show. */
const SETTLE = 120;

/**
 * @param {vscode.ExtensionContext} context
 * @param {import("./programs").Programs} programs
 */
function register(context, programs) {
  const decoration = vscode.window.createTextEditorDecorationType({
    after: {
      color: new vscode.ThemeColor("editorInlayHint.foreground"),
      fontStyle: "italic",
      margin: "0 0 0 2ch",
    },
    rangeBehavior: vscode.DecorationRangeBehavior.ClosedOpen,
  });
  /** @type {NodeJS.Timeout | undefined} */
  let timer;
  /** The cause of each line of each document version, so that moving the cursor asks nothing. */
  /** @type {Map<string, { version: number, causes: Map<number, string> }>} */
  const known = new Map();

  /** @param {vscode.TextEditor} editor */
  const causesOf = async (editor) => {
    const document = editor.document;
    const key = document.uri.toString();
    const held = known.get(key);
    if (held && held.version === document.version) {
      return held.causes;
    }
    const server = programs.serving(document);
    if (!server) {
      return new Map();
    }
    const end = document.lineAt(document.lineCount - 1).range.end;
    const params = { textDocument: { uri: key }, range: { start: { line: 0, character: 0 }, end } };
    /** @type {{ position: { line: number }, label: unknown }[] | null} */
    const hints = await server.client.sendRequest("textDocument/inlayHint", params).catch(() => null);
    const causes = new Map();
    for (const h of hints || []) {
      if (typeof h.label === "string" && h.label.startsWith("// ")) {
        causes.set(h.position.line, h.label);
      }
    }
    known.set(key, { version: document.version, causes });
    return causes;
  };

  /** @param {vscode.TextEditor | undefined} editor */
  const show = async (editor) => {
    if (!editor || editor.document.languageId !== "stilt") {
      return;
    }
    const mode = vscode.workspace.getConfiguration("stilt.inlayHints", editor.document).get("causes", "cursorLine");
    if (mode !== "cursorLine") {
      editor.setDecorations(decoration, []);
      return;
    }
    const line = editor.selection.active.line;
    const says = (await causesOf(editor)).get(line);
    if (vscode.window.activeTextEditor !== editor || editor.selection.active.line !== line) {
      return;
    }
    const range = editor.document.lineAt(line).range;
    const at = new vscode.Range(range.end, range.end);
    editor.setDecorations(decoration, says ? [{ range: at, renderOptions: { after: { contentText: says } } }] : []);
  };
  /** @param {vscode.TextEditor | undefined} editor */
  const soon = (editor) => {
    clearTimeout(timer);
    timer = setTimeout(() => show(editor), SETTLE);
  };

  context.subscriptions.push(
    decoration,
    vscode.window.onDidChangeTextEditorSelection((e) => soon(e.textEditor)),
    vscode.window.onDidChangeActiveTextEditor((e) => soon(e)),
    vscode.workspace.onDidChangeTextDocument((e) => {
      const editor = vscode.window.activeTextEditor;
      if (editor && e.document === editor.document) {
        editor.setDecorations(decoration, []);
        soon(editor);
      }
    }),
    vscode.workspace.onDidCloseTextDocument((d) => known.delete(d.uri.toString())),
    vscode.workspace.onDidChangeConfiguration((e) => e.affectsConfiguration("stilt.inlayHints") && soon(vscode.window.activeTextEditor)),
    programs.onDidChange(() => {
      known.clear();
      soon(vscode.window.activeTextEditor);
    }),
  );
}

module.exports = { register };
