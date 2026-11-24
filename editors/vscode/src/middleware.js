// @ts-check
// What the extension changes in the language server's answers before the editor shows them:
// the inlay hints of the kinds the settings switch off, and the code of each diagnostic, which
// becomes a link to its explanation, as `stilt show CODE` prints it.

"use strict";

const vscode = require("vscode");

/** The scheme of the read-only documents that show what `stilt show` prints. */
const SHOW = "stilt-show";

/**
 * Whether an inlay hint says what a line does that causes its function's facts: the server
 * writes those as `show` writes them, after `// `, at the line's end.
 * @param {vscode.InlayHint} hint
 */
function isCause(hint) {
  return typeof hint.label === "string" && hint.label.startsWith("// ");
}

/**
 * Whether an inlay hint holds a function's facts, as `[panic, alloc]`, whose parts are facts.
 * @param {vscode.InlayHint} hint
 */
function isFacts(hint) {
  return hint.kind === undefined && !isCause(hint);
}

/**
 * The hints the settings keep: types, facts, and the causes of facts at every line's end when
 * `stilt.inlayHints.causes` is `everyLine`, since the extension shows the cursor line's itself.
 * @param {vscode.TextDocument} document
 * @param {vscode.InlayHint[] | null | undefined} hints
 */
function kept(document, hints) {
  const settings = vscode.workspace.getConfiguration("stilt.inlayHints", document);
  const types = settings.get("types", true);
  const facts = settings.get("facts", true);
  const causes = /** @type {string} */ (settings.get("causes", "cursorLine")) === "everyLine";
  return (hints || []).filter((h) => {
    if (h.kind === vscode.InlayHintKind.Type) {
      return types;
    }
    return isCause(h) ? causes : facts;
  });
}

/**
 * The document that explains a diagnostic code, as `stilt show CODE` prints it.
 * @param {string} code
 */
function explanation(code) {
  return vscode.Uri.from({ scheme: SHOW, path: `/${code}.md` });
}

/**
 * A diagnostic whose code links to its explanation.
 * @param {vscode.Diagnostic} d
 */
function linked(d) {
  const code = typeof d.code === "object" ? d.code.value : d.code;
  if (typeof code === "string" && /^[EW]\d{4}$/.test(code)) {
    d.code = { value: code, target: explanation(code) };
  }
  return d;
}

/** The middleware of every client. @returns {import("vscode-languageclient").Middleware} */
function middleware() {
  return {
    provideInlayHints: async (document, range, token, next) => kept(document, await next(document, range, token)),
    handleDiagnostics: (uri, diagnostics, next) => next(uri, diagnostics.map(linked)),
  };
}

module.exports = { middleware, explanation, isCause, isFacts, SHOW };
