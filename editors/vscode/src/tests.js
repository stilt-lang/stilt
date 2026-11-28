// @ts-check
// The programs' tests in the Test Explorer, and in the editor's gutter: each `test "name"`, each
// doc example, `/// ex:`, and each property, `/// prop:`, of each file, under its program. A run
// runs `stilt test --json` in each program it covers, which runs every test of the program and
// reuses the results of those whose code is unchanged, and reports each result where it is
// written, a failure with why it failed and a comparison's two sides as a diff. A program with
// errors runs no test, and each of its tests is reported with the first error. `stilt test`
// reads the editor's buffers through the program's engine, so a run tests what the editor shows.

"use strict";

const fs = require("fs");
const path = require("path");
const vscode = require("vscode");
const { binary, programOf } = require("./programs");
const { stilt } = require("./show");

/** The lines that declare a case: a test by its name, a doc example or a property by its text. */
const CASE = /^\s*(?:(?:pub\s+)?test\s+"((?:[^"\\]|\\.)*)"|\/\/\/\s*(ex|prop):\s*(.*?)\s*(?:\/\/~.*)?$)/;

/** The directories that never hold a program's sources. */
const SKIP = "**/{target,target.noindex,_build,_opam,node_modules,.git}/**";

/**
 * The cases of a file's text, each with its kind, its label and its line, from 0.
 * @param {string} text
 */
function cases(text) {
  const found = [];
  const lines = text.split("\n");
  for (let line = 0; line < lines.length; line++) {
    const m = CASE.exec(lines[line]);
    if (m) {
      const kind = m[1] !== undefined ? "test" : m[2] === "ex" ? "example" : "property";
      found.push({ kind, label: m[1] !== undefined ? m[1] : m[3], line });
    }
  }
  return found;
}

/**
 * The message of a failure: why it failed, as `stilt test` writes it, and for a comparison
 * whose sides it gives, a diff of the two.
 * @param {{ why?: string[] }} result
 */
function failure(result) {
  const why = result.why || ["failed"];
  const left = why.find((l) => l.startsWith("left:"));
  const right = why.find((l) => l.startsWith("right:"));
  if (left && right && why.length === 2) {
    return vscode.TestMessage.diff("The two sides differ", right.replace(/^right:\s*/, ""), left.replace(/^left:\s*/, ""));
  }
  return new vscode.TestMessage(why.join("\n"));
}

class Tests {
  /** @param {vscode.TestController} controller */
  constructor(controller) {
    this.controller = controller;
  }

  /**
   * The item of a program, made the first time it is asked for.
   * @param {import("./programs").Program} program
   */
  programItem(program) {
    const id = program.uri.toString();
    let item = this.controller.items.get(id);
    if (!item) {
      item = this.controller.createTestItem(id, program.name, program.uri);
      item.canResolveChildren = true;
      item.description = vscode.workspace.asRelativePath(program.uri);
      this.controller.items.add(item);
    }
    return item;
  }

  /** Finds the programs of the workspace's folders. */
  async discover() {
    const roots = await vscode.workspace.findFiles("**/{stilt.toml,main.lt}", SKIP, 500);
    for (const root of roots) {
      const program = programOf(root);
      if (program) {
        this.programItem(program);
      }
    }
  }

  /**
   * The files of a program, each with its cases, but those of a program nested inside it.
   * @param {vscode.TestItem} item
   */
  async files(item) {
    if (!item.uri) {
      return;
    }
    const all = await vscode.workspace.findFiles(new vscode.RelativePattern(item.uri, "**/*.lt"), SKIP);
    const own = all.filter((f) => programOf(f)?.uri.toString() === item.uri?.toString());
    for (const file of own.sort((a, b) => a.fsPath.localeCompare(b.fsPath))) {
      const open = vscode.workspace.textDocuments.find((d) => d.uri.toString() === file.toString());
      const text = open ? open.getText() : await fs.promises.readFile(file.fsPath, "utf8").catch(() => "");
      this.update(file, text);
    }
  }

  /**
   * Reads the cases of a file of a program again, from its text.
   * @param {vscode.Uri} file
   * @param {string} text
   */
  update(file, text) {
    const program = programOf(file);
    if (!program || !file.fsPath.endsWith(".lt")) {
      return;
    }
    const parent = this.programItem(program);
    const found = cases(text);
    const id = file.toString();
    if (found.length === 0) {
      parent.children.delete(id);
      return;
    }
    let fileItem = parent.children.get(id);
    if (!fileItem) {
      fileItem = this.controller.createTestItem(id, path.relative(program.uri.fsPath, file.fsPath), file);
      parent.children.add(fileItem);
    }
    const seen = new Map();
    const items = found.map((c) => {
      const key = `${c.kind}:${c.label}`;
      const n = (seen.get(key) || 0) + 1;
      seen.set(key, n);
      const item = this.controller.createTestItem(`${id}#${key}#${n}`, c.label, file);
      item.range = new vscode.Range(c.line, 0, c.line, 0);
      item.description = c.kind === "test" ? undefined : c.kind;
      item.sortText = String(c.line).padStart(8, "0");
      return item;
    });
    fileItem.children.replace(items);
  }

  /**
   * Runs the programs that a request covers, and reports the results of its items.
   * @param {vscode.TestRunRequest} request
   * @param {vscode.CancellationToken} token
   */
  async run(request, token) {
    const run = this.controller.createTestRun(request);
    const wanted = this.leaves(request);
    /** @type {Map<string, vscode.TestItem[]>} */
    const byProgram = new Map();
    for (const item of wanted) {
      const program = item.uri && programOf(item.uri);
      if (program) {
        byProgram.set(program.uri.toString(), [...(byProgram.get(program.uri.toString()) || []), item]);
        run.enqueued(item);
      }
    }
    for (const [root, items] of byProgram) {
      if (token.isCancellationRequested) {
        items.forEach((i) => run.skipped(i));
        continue;
      }
      items.forEach((i) => run.started(i));
      await this.runProgram(vscode.Uri.parse(root), items, run, token);
    }
    run.end();
  }

  /**
   * The cases a request covers: those it includes, or every case, without those it excludes.
   * @param {vscode.TestRunRequest} request
   */
  leaves(request) {
    /** @type {vscode.TestItem[]} */
    const found = [];
    const excluded = new Set((request.exclude || []).map((i) => i.id));
    /** @param {vscode.TestItem} item */
    const walk = (item) => {
      if (excluded.has(item.id)) {
        return;
      }
      if (item.children.size === 0 && item.range) {
        found.push(item);
      }
      item.children.forEach(walk);
    };
    if (request.include) {
      request.include.forEach(walk);
    } else {
      this.controller.items.forEach(walk);
    }
    return found;
  }

  /**
   * Runs `stilt test --json` in a program, and reports each of `items` by its file and line.
   * @param {vscode.Uri} root
   * @param {vscode.TestItem[]} items
   * @param {vscode.TestRun} run
   * @param {vscode.CancellationToken} token
   */
  async runProgram(root, items, run, token) {
    const out = await stilt(root, ["test", "--json", "."], root.fsPath, token);
    if (out.stderr) {
      run.appendOutput(out.stderr.replace(/\r?\n/g, "\r\n"));
    }
    /** @type {{ diagnostics: any[], tests: any[] } | undefined} */
    let verdict;
    try {
      verdict = JSON.parse(out.stdout);
    } catch {
      const why = new vscode.TestMessage(`\`${binary(root)} test --json\` gave no verdict: ${out.stderr.trim() || out.stdout.trim()}`);
      items.forEach((i) => run.errored(i, why));
      return;
    }
    // A result names its file from the program's directory, with `/`, and its line from 1.
    const at = (/** @type {vscode.TestItem} */ i) =>
      `${path.relative(root.fsPath, i.uri?.fsPath || "").split(path.sep).join("/")}:${(i.range?.start.line || 0) + 1}`;
    const results = new Map((verdict?.tests || []).map((t) => [`${t.file}:${t.line}`, t]));
    const error = (verdict?.diagnostics || []).find((d) => d.code && d.code.startsWith("E"));
    for (const item of items) {
      const result = results.get(at(item));
      if (result && result.passed) {
        run.passed(item);
      } else if (result) {
        const message = failure(result);
        message.location = new vscode.Location(/** @type {vscode.Uri} */ (item.uri), /** @type {vscode.Range} */ (item.range));
        run.failed(item, message);
      } else if (error) {
        const message = new vscode.TestMessage(`No test ran: ${error.file}:${error.line}: ${error.message} [${error.code}]`);
        message.location = new vscode.Location(vscode.Uri.joinPath(root, error.file), new vscode.Position(error.line - 1, error.col - 1));
        run.errored(item, message);
      } else {
        run.skipped(item);
      }
    }
  }
}

/**
 * @param {vscode.ExtensionContext} context
 * @param {import("./install").Installer} installer
 */
function register(context, installer) {
  const controller = vscode.tests.createTestController("stilt", "Stilt");
  const tests = new Tests(controller);
  controller.resolveHandler = async (item) => (item ? tests.files(item) : tests.discover());
  controller.refreshHandler = async () => {
    controller.items.replace([]);
    await tests.discover();
  };
  const runHandler = async (/** @type {vscode.TestRunRequest} */ request, /** @type {vscode.CancellationToken} */ token) => {
    if (!vscode.workspace.isTrusted) {
      vscode.window.showWarningMessage("Stilt: trust this workspace to run its tests.");
      return Promise.resolve();
    }
    const first = request.include?.[0]?.uri;
    const ready = await installer.ready(first && programOf(first)?.uri);
    if (!ready) {
      return undefined;
    }
    return request.continuous ? watch(tests, request, token) : tests.run(request, token);
  };
  controller.createRunProfile("Run", vscode.TestRunProfileKind.Run, runHandler, true, undefined, true);
  const reread = (/** @type {vscode.TextDocument} */ d) => d.languageId === "stilt" && tests.update(d.uri, d.getText());
  context.subscriptions.push(
    controller,
    vscode.workspace.onDidOpenTextDocument(reread),
    vscode.workspace.onDidChangeTextDocument((e) => reread(e.document)),
  );
}

/**
 * Runs a request again each time a file of a program it covers is saved, until it is cancelled.
 * @param {Tests} tests
 * @param {vscode.TestRunRequest} request
 * @param {vscode.CancellationToken} token
 */
function watch(tests, request, token) {
  return new Promise((resolve) => {
    const saved = vscode.workspace.onDidSaveTextDocument((d) => {
      if (d.languageId === "stilt") {
        const fresh = new vscode.TestRunRequest(request.include, request.exclude, request.profile, false);
        tests.run(fresh, token);
      }
    });
    token.onCancellationRequested(() => {
      saved.dispose();
      resolve(undefined);
    });
  });
}

module.exports = { register, cases };
