// @ts-check
// The menu that the language status opens, **Stilt: Show Menu**: what can be done about the
// toolchain and the language servers, in one quick pick. Also the commands it lists that have no
// other home: reporting an issue, opening the settings, and turning the servers on or off.

"use strict";

const os = require("os");
const vscode = require("vscode");
const { toolchain } = require("./toolchain");

const ISSUES = "https://github.com/stilt-lang/stilt/issues/new";
const WALKTHROUGH = "stilt-lang.stilt#stilt.start";

/**
 * The menu's entries for the toolchain that was found.
 * @param {import("./locate").Found | undefined} found
 * @returns {(vscode.QuickPickItem & { command?: string })[]}
 */
function entries(found) {
  const usable = found && (found.kind === "found" || found.kind === "outdated");
  const on = vscode.workspace.getConfiguration("stilt").get("server.enable", true);
  const install = !usable
    ? [{ label: "$(cloud-download) Install Stilt", detail: "Runs the installer of Stilt's latest release, install.sh", command: "stilt.install" }]
    : found.kind === "outdated"
      ? [{ label: "$(arrow-circle-up) Update Stilt", description: found.version, command: "stilt.install" }]
      : [{ label: "$(sync) Check for Updates", description: found.version, command: "stilt.checkForUpdates" }];
  const where = found && found.kind !== "missing" ? found.path : "Not found";
  return [
    ...install,
    { label: "$(debug-restart) Restart Language Server", command: "stilt.restart" },
    on
      ? { label: "$(debug-stop) Turn Language Server Off", command: "stilt.toggleServer" }
      : { label: "$(debug-start) Turn Language Server On", command: "stilt.toggleServer" },
    { label: "$(output) Show Logs", command: "stilt.showLogs" },
    { label: "", kind: vscode.QuickPickItemKind.Separator },
    { label: "$(file-binary) Locate stilt…", description: where, command: "stilt.locate" },
    { label: "$(gear) Open Settings", command: "stilt.openSettings" },
    { label: "$(book) Get Started", command: "stilt.openWalkthrough" },
    { label: "$(issues) Report an Issue", command: "stilt.reportIssue" },
  ];
}

async function menu() {
  const editor = vscode.window.activeTextEditor;
  const found = toolchain.current(editor?.document.uri) || (await toolchain.resolve(editor?.document.uri));
  const picked = await vscode.window.showQuickPick(entries(found), { title: "Stilt", placeHolder: "What to do" });
  if (picked && picked.command) {
    await vscode.commands.executeCommand(picked.command);
  }
}

/** Opens a new issue whose version and system are filled in, for the user to complete. */
async function reportIssue() {
  const found = toolchain.current() || (await toolchain.resolve());
  const ext = vscode.extensions.getExtension("stilt-lang.stilt");
  const stilt = found.kind === "found" || found.kind === "outdated" ? `stilt ${found.version}` : "stilt not found";
  const query = new URLSearchParams({
    template: "bug.yml",
    version: `${stilt}; extension ${ext?.packageJSON.version || "unknown"}; ${vscode.env.appName} ${vscode.version}`,
    system: `${os.type()} ${os.release()} ${os.arch()}`,
  });
  await vscode.env.openExternal(vscode.Uri.parse(`${ISSUES}?${query}`));
}

async function toggleServer() {
  const config = vscode.workspace.getConfiguration("stilt");
  await config.update("server.enable", !config.get("server.enable", true), vscode.ConfigurationTarget.Global);
}

/** @param {vscode.ExtensionContext} context */
function register(context) {
  context.subscriptions.push(
    vscode.commands.registerCommand("stilt.menu", menu),
    vscode.commands.registerCommand("stilt.reportIssue", reportIssue),
    vscode.commands.registerCommand("stilt.toggleServer", toggleServer),
    vscode.commands.registerCommand("stilt.openSettings", () => vscode.commands.executeCommand("workbench.action.openSettings", "@ext:stilt-lang.stilt")),
    vscode.commands.registerCommand("stilt.openWalkthrough", async () => {
      // The walkthrough shows once the extension runs, so that installing it opens no page.
      await vscode.commands.executeCommand("setContext", "stilt:activated", true);
      await vscode.commands.executeCommand("workbench.action.openWalkthrough", WALKTHROUGH, false);
    }),
  );
}

module.exports = { register };
