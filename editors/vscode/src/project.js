// @ts-check
// **Stilt: New Project…**: `stilt new`, a program or a library, in a directory chosen in three
// steps, then the new package opened, in this window when it has no folder open, with its first
// source file shown.

"use strict";

const childProcess = require("child_process");
const fs = require("fs");
const os = require("os");
const path = require("path");
const vscode = require("vscode");
const { toolchain } = require("./toolchain");

/** The source file to show once a new package opens, kept across the window's reload. */
const OPEN_AFTER = "stilt.openAfter";

/** A package's name: a lowercase identifier (`stilt new` also refuses reserved words). */
const NAME = /^[a-z_][a-z0-9_]*$/;

/**
 * The first source file of a new package, as `stilt new` writes it.
 * @param {string} dir
 */
function firstSource(dir) {
  const src = path.join(dir, "src");
  const files = fs.existsSync(src) ? fs.readdirSync(src).filter((f) => f.endsWith(".lt")).sort() : [];
  const main = files.find((f) => f === "main.lt" || f === "lib.lt") || files[0];
  return main ? path.join(src, main) : path.join(dir, "stilt.toml");
}

/**
 * Asks what to start, where, and its name.
 * @returns {Promise<{ lib: boolean, parent: string, name: string } | undefined>}
 */
async function ask() {
  const kinds = [
    { label: "$(play) Program", detail: "A `main`, a test and a README", lib: false },
    { label: "$(library) Library", detail: "Functions with a test and a doc example, and no `main`", lib: true },
  ];
  const kind = await vscode.window.showQuickPick(kinds, { title: "New Stilt Project (1/3)", placeHolder: "What to start" });
  if (!kind) {
    return undefined;
  }
  const near = vscode.workspace.workspaceFolders?.[0]?.uri;
  const picked = await vscode.window.showOpenDialog({
    title: "New Stilt Project (2/3): the directory to create it in",
    openLabel: "Create Here",
    canSelectFiles: false,
    canSelectFolders: true,
    canSelectMany: false,
    defaultUri: near ? vscode.Uri.file(path.dirname(near.fsPath)) : vscode.Uri.file(os.homedir()),
  });
  if (!picked || !picked[0]) {
    return undefined;
  }
  const parent = picked[0].fsPath;
  const name = await vscode.window.showInputBox({
    title: "New Stilt Project (3/3)",
    prompt: `Its name, which names its directory in ${parent}`,
    placeHolder: kind.lib ? "csv_tools" : "hello",
    validateInput: (v) => {
      if (!NAME.test(v)) {
        return "A lowercase identifier, such as hello or csv_tools";
      }
      const dir = path.join(parent, v);
      return fs.existsSync(dir) && fs.readdirSync(dir).length ? `${dir} exists and isn't empty` : undefined;
    },
  });
  return name ? { lib: kind.lib, parent, name } : undefined;
}

/**
 * @param {import("./install").Installer} installer
 * @param {vscode.ExtensionContext} context
 */
async function newProject(installer, context) {
  const found = await toolchain.resolve();
  if (found.kind !== "found" && found.kind !== "outdated") {
    await installer.offer(found, { asked: true });
    return;
  }
  const asked = await ask();
  if (!asked) {
    return;
  }
  const args = ["new", ...(asked.lib ? ["--lib"] : []), asked.name];
  const made = await new Promise((resolve) => {
    childProcess.execFile(found.path, args, { cwd: asked.parent, env: toolchain.env() }, (error, _stdout, stderr) => resolve(error ? String(stderr).trim() || error.message : ""));
  });
  if (made) {
    vscode.window.showErrorMessage(`Stilt: ${String(made).replace(/^stilt: /, "")}`);
    return;
  }
  const dir = vscode.Uri.file(path.join(asked.parent, asked.name));
  const first = firstSource(dir.fsPath);
  if (!vscode.workspace.workspaceFolders?.length) {
    await context.globalState.update(OPEN_AFTER, first);
    await vscode.commands.executeCommand("vscode.openFolder", dir);
    return;
  }
  const choice = await vscode.window.showInformationMessage(`Created ${asked.name} in ${asked.parent}.`, "Open", "Open in New Window", "Add to Workspace");
  if (choice === "Add to Workspace") {
    vscode.workspace.updateWorkspaceFolders(vscode.workspace.workspaceFolders.length, 0, { uri: dir });
    await vscode.window.showTextDocument(vscode.Uri.file(first));
  } else if (choice) {
    await context.globalState.update(OPEN_AFTER, first);
    await vscode.commands.executeCommand("vscode.openFolder", dir, { forceNewWindow: choice === "Open in New Window" });
  }
}

/**
 * Shows the first source file of a package that **New Project** just opened in this window.
 * @param {vscode.ExtensionContext} context
 */
function openAfter(context) {
  const file = context.globalState.get(OPEN_AFTER);
  if (typeof file !== "string" || !vscode.workspace.getWorkspaceFolder(vscode.Uri.file(file))) {
    return;
  }
  context.globalState.update(OPEN_AFTER, undefined);
  vscode.window.showTextDocument(vscode.Uri.file(file));
}

/**
 * @param {vscode.ExtensionContext} context
 * @param {import("./install").Installer} installer
 */
function register(context, installer) {
  context.subscriptions.push(vscode.commands.registerCommand("stilt.newProject", () => newProject(installer, context)));
  openAfter(context);
}

module.exports = { register };
