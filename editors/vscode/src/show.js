// @ts-check
// The read-only documents that show what `stilt show` prints: a function with its inferred
// facts written in, with its macros expanded, or with its release build's performance report,
// a module's skeleton, and a diagnostic code's explanation, as Markdown. Each is shown again as
// the program changes, since `show` reads the editor's buffers through the program's engine.

"use strict";

const childProcess = require("child_process");
const os = require("os");
const vscode = require("vscode");
const { programOf } = require("./programs");
const { binary, toolchain } = require("./toolchain");
const { SHOW, explanation } = require("./middleware");

/** How long the program must stay unchanged before the open documents are shown again. */
const SETTLE = 400;

/**
 * Runs `stilt` with `args` in `cwd`, and gives what it printed and its status.
 * @param {vscode.Uri | undefined} scope the program whose settings name the binary
 * @param {string[]} args
 * @param {string} cwd
 * @param {vscode.CancellationToken} [token]
 * @returns {Promise<{ stdout: string, stderr: string, status: number }>}
 */
function stilt(scope, args, cwd, token) {
  return new Promise((resolve) => {
    const child = childProcess.execFile(binary(scope), args, { cwd, env: toolchain.env(scope), maxBuffer: 64 * 1024 * 1024 }, (error, stdout, stderr) => {
      const code = error && typeof error.code === "number" ? error.code : 0;
      resolve({ stdout, stderr: stderr || (error && !stdout ? error.message : ""), status: error ? code || 1 : 0 });
    });
    token?.onCancellationRequested(() => child.kill());
  });
}

/**
 * An explanation, as `stilt show CODE` prints it, as Markdown: its title a heading, and the
 * lines that give where it is reported, the record that defines it, its tier and the phase that
 * checks it, a list.
 * @param {string} text
 */
function markdown(text) {
  const [title, ...rest] = text.trimEnd().split("\n");
  const body = rest.map((line) => line.replace(/^([A-Z][a-z]+(?: [a-z]+)*): /, "- **$1:** "));
  return `# ${title}\n${body.join("\n")}\n`;
}

/**
 * The document that shows `stilt show` with `args`, run in the program at `root`.
 * @param {string} root
 * @param {string} name the document's name, as `eval.call`
 * @param {string[]} args
 */
function shown(root, name, args) {
  const query = encodeURIComponent(JSON.stringify({ root, args }));
  return vscode.Uri.from({ scheme: SHOW, path: `/${name}.lt`, query });
}

/** Provides the documents of `stilt-show:`, and shows the open ones again as programs change. */
class Shown {
  constructor() {
    this.changed = new vscode.EventEmitter();
    this.onDidChange = this.changed.event;
    /** @type {NodeJS.Timeout | undefined} */
    this.timer = undefined;
  }

  /**
   * @param {vscode.Uri} uri
   * @param {vscode.CancellationToken} token
   */
  async provideTextDocumentContent(uri, token) {
    const code = /^\/([EW]\d{4})\.md$/.exec(uri.path);
    if (code) {
      const program = vscode.window.activeTextEditor && programOf(vscode.window.activeTextEditor.document.uri);
      const cwd = program ? program.uri.fsPath : os.tmpdir();
      const out = await stilt(program?.uri, ["show", code[1]], cwd, token);
      return out.status === 0 ? markdown(out.stdout) : `# ${code[1]}\n\n${out.stderr.trim()}\n`;
    }
    const { root, args } = JSON.parse(decodeURIComponent(uri.query));
    const out = await stilt(vscode.Uri.file(root), args, root, token);
    const notes = out.stderr.trim() ? `\n// ${out.stderr.trim().split("\n").join("\n// ")}\n` : "";
    return out.stdout + notes;
  }

  /** Shows every open document of `stilt-show:` again, once the program has settled. */
  refresh() {
    clearTimeout(this.timer);
    this.timer = setTimeout(() => {
      for (const d of vscode.workspace.textDocuments) {
        if (d.uri.scheme === SHOW && d.uri.query) {
          this.changed.fire(d.uri);
        }
      }
    }, SETTLE);
  }
}

/**
 * Opens what `stilt show` prints for the function at the cursor, or for its module.
 * @param {import("./programs").Programs} programs
 * @param {"facts" | "expanded" | "release" | "module"} what
 */
async function showAtCursor(programs, what) {
  const editor = vscode.window.activeTextEditor;
  const server = editor && programs.serving(editor.document);
  if (!editor || !server) {
    vscode.window.showWarningMessage("Stilt: open a file of a program, and wait for its language server to start.");
    return;
  }
  const params = { textDocument: { uri: editor.document.uri.toString() }, position: editor.selection.active };
  const at = await server.client.sendRequest("stilt/whereabouts", params).catch(() => undefined);
  const address = what === "module" ? at?.module : at?.function;
  if (!address) {
    vscode.window.showWarningMessage(what === "module" ? "Stilt: this file has no module." : "Stilt: the cursor is in no function.");
    return;
  }
  const flags = { facts: [], expanded: ["--expanded"], release: ["--release"], module: [] }[what];
  const suffix = { facts: "", expanded: " (expanded)", release: " (release)", module: "" }[what];
  const uri = shown(server.program.uri.fsPath, `${address}${suffix}`, ["show", ...flags, address]);
  const document = await vscode.workspace.openTextDocument(uri);
  await vscode.languages.setTextDocumentLanguage(document, what === "release" ? "plaintext" : "stilt");
  await vscode.window.showTextDocument(document, { preview: true, viewColumn: vscode.ViewColumn.Beside, preserveFocus: true });
}

/**
 * Opens the explanation of a diagnostic code: the one asked for, or that of the diagnostic at
 * the cursor, as a rendered Markdown preview beside the editor.
 * @param {string} [code]
 */
async function explain(code) {
  const editor = vscode.window.activeTextEditor;
  const atCursor = editor && vscode.languages.getDiagnostics(editor.document.uri)
    .filter((d) => d.range.contains(editor.selection.active))
    .map((d) => (typeof d.code === "object" ? String(d.code.value) : String(d.code)))
    .find((c) => /^[EW]\d{4}$/.test(c));
  const chosen = typeof code === "string" ? code : await vscode.window.showInputBox({
    title: "Explain a diagnostic code",
    prompt: "A code, as E0311 or W0001",
    value: atCursor || "",
    validateInput: (v) => (/^[EW]\d{4}$/.test(v.trim()) ? undefined : "A code is E or W and four digits, as E0311"),
  });
  if (chosen) {
    await vscode.commands.executeCommand("markdown.showPreviewToSide", explanation(chosen.trim()));
  }
}

/**
 * The code actions that explain the diagnostics of `stilt` at a range.
 * @type {vscode.CodeActionProvider}
 */
const explaining = {
  provideCodeActions(_document, _range, context) {
    const codes = new Set(context.diagnostics
      .filter((d) => d.source === "stilt")
      .map((d) => (typeof d.code === "object" ? String(d.code.value) : String(d.code))));
    return [...codes].map((code) => {
      const action = new vscode.CodeAction(`Explain ${code}`, vscode.CodeActionKind.Empty);
      action.command = { title: `Explain ${code}`, command: "stilt.explain", arguments: [code] };
      return action;
    });
  },
};

/**
 * @param {vscode.ExtensionContext} context
 * @param {import("./programs").Programs} programs
 */
function register(context, programs) {
  const provider = new Shown();
  const onStilt = (/** @type {vscode.TextDocument} */ d) => d.languageId === "stilt" && provider.refresh();
  context.subscriptions.push(
    provider.changed,
    vscode.workspace.registerTextDocumentContentProvider(SHOW, provider),
    vscode.workspace.onDidChangeTextDocument((e) => onStilt(e.document)),
    vscode.workspace.onDidSaveTextDocument(onStilt),
    vscode.languages.registerCodeActionsProvider({ language: "stilt" }, explaining, {
      providedCodeActionKinds: [vscode.CodeActionKind.Empty],
    }),
    vscode.commands.registerCommand("stilt.showFacts", () => showAtCursor(programs, "facts")),
    vscode.commands.registerCommand("stilt.showExpansion", () => showAtCursor(programs, "expanded")),
    vscode.commands.registerCommand("stilt.showRelease", () => showAtCursor(programs, "release")),
    vscode.commands.registerCommand("stilt.showModule", () => showAtCursor(programs, "module")),
    vscode.commands.registerCommand("stilt.explain", explain),
  );
}

module.exports = { register, stilt, markdown };
