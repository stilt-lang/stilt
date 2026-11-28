// @ts-check
// The tasks of each program: `stilt check`, `build`, `test`, `run` and `fmt`, which **Tasks: Run
// Task** lists and `tasks.json` may name as `{ "type": "stilt", "command": "check" }`. Each
// reads its output with the problem matchers of `package.json`, so a diagnostic or a failed
// test lands in the Problems view. **Stilt: Run Program** runs the active file's program in a
// terminal, where it reads its standard input.

"use strict";

const path = require("path");
const vscode = require("vscode");
const { programOf, isProgram } = require("./programs");
const { binary, toolchain } = require("./toolchain");

/** The commands a task may run, with the group it is in and the problem matchers it reads. */
const COMMANDS = {
  check: { group: vscode.TaskGroup.Build, matchers: ["$stilt", "$stilt-warnings"], detail: "Report the program's errors and warnings" },
  build: { group: vscode.TaskGroup.Build, matchers: ["$stilt", "$stilt-warnings"], detail: "Build the program into an executable" },
  test: { group: vscode.TaskGroup.Test, matchers: ["$stilt", "$stilt-warnings", "$stilt-tests"], detail: "Run every test, doc example and property" },
  run: { group: undefined, matchers: ["$stilt", "$stilt-warnings"], detail: "Run the program, patching each edit into it" },
  fmt: { group: undefined, matchers: [], detail: "Write every file in the canonical format" },
};

/**
 * The task that runs `stilt COMMAND` in a program.
 * @param {{ type: string, command: keyof typeof COMMANDS, program?: string, args?: string[], arguments?: string[] }} definition
 * @param {vscode.Uri} root the program's directory
 * @param {vscode.WorkspaceFolder | vscode.TaskScope} scope
 */
function task(definition, root, scope) {
  const spec = COMMANDS[definition.command];
  const args = [definition.command, ...(definition.args || []), ".", ...(definition.arguments || [])];
  const env = /** @type {Record<string, string>} */ (toolchain.env(root));
  const execution = new vscode.ProcessExecution(binary(root), args, { cwd: root.fsPath, env });
  const name = `${definition.command} ${path.basename(root.fsPath)}`;
  const made = new vscode.Task(definition, scope, name, "stilt", execution, spec.matchers);
  made.detail = `${spec.detail}: stilt ${args.join(" ")} in ${vscode.workspace.asRelativePath(root)}`;
  if (spec.group) {
    made.group = spec.group;
  }
  made.presentationOptions = { reveal: vscode.TaskRevealKind.Always, clear: true, showReuseMessage: false };
  return made;
}

/** The programs that tasks are offered for: the workspace folders that are programs, and those
 * of the open Stilt files. */
function programs() {
  const found = new Map();
  for (const folder of vscode.workspace.workspaceFolders || []) {
    if (folder.uri.scheme === "file" && isProgram(folder.uri.fsPath)) {
      found.set(folder.uri.toString(), { uri: folder.uri, folder });
    }
  }
  for (const d of vscode.workspace.textDocuments) {
    const p = d.languageId === "stilt" ? programOf(d.uri) : undefined;
    if (p) {
      found.set(p.uri.toString(), p);
    }
  }
  return [...found.values()];
}

/** @type {vscode.TaskProvider} */
const provider = {
  provideTasks() {
    const made = [];
    for (const p of programs()) {
      const scope = p.folder || vscode.TaskScope.Workspace;
      for (const command of /** @type {(keyof typeof COMMANDS)[]} */ (Object.keys(COMMANDS))) {
        made.push(task({ type: "stilt", command }, p.uri, scope));
      }
    }
    return made;
  },
  resolveTask(given) {
    const definition = /** @type {any} */ (given.definition);
    if (!(definition.command in COMMANDS)) {
      return undefined;
    }
    const folder = typeof given.scope === "object" ? given.scope : undefined;
    const base = folder ? folder.uri.fsPath : vscode.workspace.workspaceFolders?.[0]?.uri.fsPath;
    if (!base) {
      return undefined;
    }
    const root = vscode.Uri.file(definition.program ? path.resolve(base, definition.program) : base);
    return task(definition, root, given.scope || vscode.TaskScope.Workspace);
  },
};

/**
 * Runs the program of the active file, or the one a code lens names, in a terminal, with the
 * arguments of `stilt.run.arguments`.
 * @param {import("./install").Installer} installer
 * @param {vscode.Uri} [root]
 */
async function runProgram(installer, root) {
  const editor = vscode.window.activeTextEditor;
  const program = root ? { uri: root, folder: vscode.workspace.getWorkspaceFolder(root) } : editor && programOf(editor.document.uri);
  if (!program) {
    vscode.window.showWarningMessage("Stilt: open a file of a program to run it.");
    return;
  }
  if (!(await installer.ready(program.uri))) {
    return;
  }
  /** @type {string[]} */
  const programArgs = vscode.workspace.getConfiguration("stilt.run", program.uri).get("arguments", []);
  const definition = { type: "stilt", command: /** @type {const} */ ("run"), arguments: programArgs };
  await vscode.tasks.executeTask(task(definition, program.uri, program.folder || vscode.TaskScope.Workspace));
}

/**
 * @param {vscode.ExtensionContext} context
 * @param {import("./install").Installer} installer
 */
function register(context, installer) {
  context.subscriptions.push(
    vscode.tasks.registerTaskProvider("stilt", provider),
    vscode.commands.registerCommand("stilt.run", (/** @type {vscode.Uri | undefined} */ root) => runProgram(installer, root)),
  );
}

module.exports = { register };
