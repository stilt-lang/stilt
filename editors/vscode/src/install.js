// @ts-check
// Getting a `stilt` when none is found or the one found is too old: one notification, once a
// session, that offers to install it with the project's installer, install.sh, to locate it,
// which writes `stilt.path`, or not to ask again, which `stilt.installPrompt` remembers. An
// install or update runs only on a click, never with elevated rights, in a notification that
// shows its progress and can cancel it, with its output in the **Stilt** output; once it ends,
// the servers start with no reload.

"use strict";

const childProcess = require("child_process");
const fs = require("fs");
const os = require("os");
const path = require("path");
const vscode = require("vscode");
const locate = require("./locate");
const { toolchain } = require("./toolchain");

/** @typedef {import("./locate").Found} Found */

const INSTALLER = "https://raw.githubusercontent.com/stilt-lang/stilt/main/install.sh";
const LATEST = "https://api.github.com/repos/stilt-lang/stilt/releases/latest";
const RELEASES = "https://github.com/stilt-lang/stilt/releases";
const GET_STARTED = "https://github.com/stilt-lang/stilt#get-started";
const BREW = "stilt-lang/stilt/stilt";

/** Downloads the installer to a temporary file, so that a failed download runs nothing, and runs it. */
const SCRIPT = `set -eu
script=$(mktemp)
trap 'rm -f "$script"' EXIT
if command -v curl > /dev/null 2>&1; then
  curl -sSfL --proto '=https' --tlsv1.2 -o "$script" "$1"
else
  wget -q --https-only -O "$script" "$1"
fi
sh "$script"`;

class Installer {
  /**
   * @param {vscode.LogOutputChannel} log
   * @param {() => Promise<void>} restart restarts the servers, which look for `stilt` again
   */
  constructor(log, restart) {
    this.log = log;
    this.restart = restart;
    /** The kinds of offers made this session. @type {Set<string>} */
    this.offered = new Set();
    /** @type {Promise<void> | undefined} */
    this.running = undefined;
  }

  /**
   * Offers what to do about a `stilt` that can't be used, once a session for each kind, or
   * always when a command needs it (`asked`).
   * @param {Found} found
   * @param {{ asked?: boolean }} [options]
   */
  async offer(found, { asked = false } = {}) {
    const kind = found.kind === "missing" && found.configured ? "configured" : found.kind;
    if (kind === "found" || this.running || (!asked && this.offered.has(kind))) {
      return;
    }
    const quiet = !vscode.workspace.getConfiguration("stilt").get("installPrompt", true);
    if (!asked && quiet && (kind === "missing" || kind === "outdated")) {
      return;
    }
    this.offered.add(kind);
    const { message, actions, level } = this.offerOf(found, asked);
    const w = vscode.window;
    const choice = await (level === "error" ? w.showErrorMessage(message, ...actions)
      : level === "warning" ? w.showWarningMessage(message, ...actions)
      : w.showInformationMessage(message, ...actions));
    await this.act(choice);
  }

  /**
   * The message of an offer, its actions, and its level.
   * @param {Found} found
   * @param {boolean} asked
   * @returns {{ message: string, actions: string[], level: "info" | "warning" | "error" }}
   */
  offerOf(found, asked) {
    const never = asked ? [] : ["Don't Ask Again"];
    if (found.kind === "missing" && found.configured) {
      return { message: `Stilt: \`stilt.path\` names ${found.configured}, which isn't an executable.`, actions: ["Locate…", "Open Settings"], level: "warning" };
    }
    if (found.kind === "missing") {
      const get = locate.installable() ? "Install Stilt" : "Get Stilt";
      const message = "Stilt isn't installed, or VS Code can't find it. Install it for diagnostics, completion, formatting and the rest.";
      return { message, actions: [get, "Locate…", ...never], level: "info" };
    }
    if (found.kind === "broken") {
      return { message: `Stilt: ${found.path} doesn't run: ${firstLine(found.error)}`, actions: ["Show Logs", "Locate…"], level: "error" };
    }
    const by = locate.manager(found.path);
    const how = by === "nix" ? " Update it with Nix." : by === "other" ? " Point `stilt.path` at a newer one, or install the latest." : "";
    const message = `Stilt ${found.version} is older than this extension needs, ${locate.NEEDS} or later.${how}`;
    const update = by === "nix" ? [] : [by === "other" ? "Install Latest" : "Update"];
    return { message, actions: [...update, ...never], level: "info" };
  }

  /** @param {string | undefined} choice */
  async act(choice) {
    switch (choice) {
      case "Install Stilt":
      case "Install Latest":
      case "Update":
        return this.install();
      case "Get Stilt":
        return void vscode.env.openExternal(vscode.Uri.parse(GET_STARTED));
      case "Locate…":
        return this.locate();
      case "Open Settings":
        return void vscode.commands.executeCommand("workbench.action.openSettings", "stilt.path");
      case "Show Logs":
        return this.log.show();
      case "Don't Ask Again":
        return void vscode.workspace.getConfiguration("stilt").update("installPrompt", false, vscode.ConfigurationTarget.Global);
    }
  }

  /**
   * The `stilt` of a program, or `undefined` after offering what to do about it, for a command
   * that needs it.
   * @param {vscode.Uri} [scope]
   */
  async ready(scope) {
    const found = await toolchain.resolve(scope);
    if (found.kind === "found" || found.kind === "outdated") {
      return found.path;
    }
    await this.offer(found, { asked: true });
    return undefined;
  }

  /**
   * Installs Stilt, or updates the one found the way it was installed. With a `stilt` as recent
   * as the extension needs, it checks for a newer release first, unless that check asked.
   * @param {{ checked?: boolean }} [options]
   */
  async install({ checked = false } = {}) {
    if (this.running) {
      return this.running;
    }
    const found = toolchain.current() || (await toolchain.resolve());
    if (found.kind === "found" && !checked) {
      return this.checkForUpdates();
    }
    const by = found.kind === "found" || found.kind === "outdated" ? locate.manager(found.path) : "installer";
    if (by === "nix") {
      vscode.window.showInformationMessage(`Stilt: ${found.kind !== "missing" ? found.path : "this stilt"} is Nix's; update it with Nix.`);
      return;
    }
    const brew = by === "homebrew" ? ["/opt/homebrew/bin/brew", "/usr/local/bin/brew"].find((f) => fs.existsSync(f)) : undefined;
    if (!brew && !locate.installable()) {
      await vscode.env.openExternal(vscode.Uri.parse(GET_STARTED));
      return;
    }
    const verb = found.kind === "missing" || found.kind === "broken" ? "Installing" : "Updating";
    const command = brew ? { file: brew, args: ["upgrade", BREW] } : { file: "/bin/sh", args: ["-c", SCRIPT, "install.sh", INSTALLER] };
    this.running = this.run(`${verb} Stilt`, command).finally(() => (this.running = undefined));
    return this.running;
  }

  /**
   * Runs an install or update, and starts the servers again once it ends.
   * @param {string} title
   * @param {{ file: string, args: string[] }} command
   */
  async run(title, command) {
    this.log.info(`${title}: ${command.file} ${command.args.map((a) => (a.includes("\n") ? "<script>" : a)).join(" ")}`);
    const done = await vscode.window.withProgress({ location: vscode.ProgressLocation.Notification, title, cancellable: true }, (progress, token) =>
      spawned(command, toolchain.env(), (line) => {
        this.log.info(line);
        progress.report({ message: line.replace(/^stilt: /, "") });
      }, token),
    );
    toolchain.forget();
    await this.restart();
    const found = await toolchain.resolve();
    if (done.cancelled) {
      this.log.warn(`${title}: cancelled`);
    } else if (done.status !== 0) {
      const choice = await vscode.window.showErrorMessage(`Stilt: ${title.toLowerCase()} failed: ${done.last || `status ${done.status}`}`, "Show Logs", "Try Again");
      if (choice === "Try Again") {
        await this.install({ checked: true });
      } else if (choice) {
        this.log.show();
      }
    } else if (found.kind === "found" || found.kind === "outdated") {
      this.installed(found);
    }
  }

  /**
   * Says that Stilt is installed, and that `stilt.path` names another one if it does.
   * @param {Extract<Found, { kind: "found" | "outdated" }>} found
   */
  async installed(found) {
    const named = vscode.workspace.getConfiguration("stilt").inspect("path")?.globalValue;
    const home = path.join(process.env.STILT_HOME || path.join(os.homedir(), ".stilt"), "bin");
    if (!named || found.source !== "stilt.path" || path.dirname(found.path) === home) {
      vscode.window.showInformationMessage(`Stilt ${found.version} is installed.`);
      return;
    }
    const use = "Use the Installed One";
    const choice = await vscode.window.showInformationMessage(`Stilt is installed in ${home}, and \`stilt.path\` still names ${named}.`, use);
    if (choice === use) {
      await vscode.workspace.getConfiguration("stilt").update("path", undefined, vscode.ConfigurationTarget.Global);
    }
  }

  /** Asks for the `stilt` binary, checks that it is one, and writes it to `stilt.path`. */
  async locate() {
    const bin = path.join(os.homedir(), ".stilt", "bin");
    const picked = await vscode.window.showOpenDialog({
      title: "Locate stilt",
      openLabel: "Use This stilt",
      canSelectFiles: true,
      canSelectFolders: false,
      canSelectMany: false,
      defaultUri: vscode.Uri.file(fs.existsSync(bin) ? bin : os.homedir()),
    });
    if (!picked || !picked[0]) {
      return;
    }
    const file = picked[0].fsPath;
    const found = await locate.find({ configured: file, env: toolchain.env() });
    if (found.kind !== "found" && found.kind !== "outdated") {
      const why = found.kind === "broken" ? firstLine(found.error) : "it isn't an executable";
      vscode.window.showErrorMessage(`Stilt: ${file} isn't a stilt that runs: ${why}`);
      return;
    }
    const config = vscode.workspace.getConfiguration("stilt");
    await config.update("path", file, vscode.ConfigurationTarget.Global);
    const shadowed = config.inspect("path");
    if (shadowed?.workspaceValue !== undefined || shadowed?.workspaceFolderValue !== undefined) {
      vscode.window.showWarningMessage("Stilt: the workspace's settings name another `stilt.path`, which still applies here.");
    }
  }

  /** Asks GitHub for the latest release, and offers to update to it. */
  async checkForUpdates() {
    const found = await toolchain.resolve();
    if (found.kind === "missing" || found.kind === "broken") {
      return this.offer(found, { asked: true });
    }
    let latest;
    try {
      latest = await vscode.window.withProgress({ location: vscode.ProgressLocation.Window, title: "Checking for a newer Stilt" }, latestRelease);
    } catch (error) {
      this.log.error(`checking for updates: ${error instanceof Error ? error.message : String(error)}`);
      vscode.window.showErrorMessage("Stilt: can't reach GitHub to check for a newer release.", "Show Logs").then((c) => c && this.log.show());
      return;
    }
    if (locate.compare(latest, found.version) <= 0) {
      vscode.window.showInformationMessage(`Stilt ${found.version} is the latest release.`);
      return;
    }
    const notes = "Release Notes";
    const choice = await vscode.window.showInformationMessage(`Stilt ${latest} is out, and this machine has ${found.version}.`, "Update", notes);
    if (choice === "Update") {
      await this.install({ checked: true });
    } else if (choice === notes) {
      await vscode.env.openExternal(vscode.Uri.parse(`${RELEASES}/tag/${latest}`));
    }
  }
}

/** The version of the latest release, from GitHub's API. @returns {Promise<string>} */
async function latestRelease() {
  const response = await fetch(LATEST, { headers: { Accept: "application/vnd.github+json", "User-Agent": "stilt-vscode" } });
  if (!response.ok) {
    throw new Error(`GitHub answered ${response.status}`);
  }
  const release = /** @type {{ tag_name?: string }} */ (await response.json());
  const tag = String(release.tag_name || "").replace(/^v/, "");
  if (!locate.parseVersion(`stilt ${tag}`)) {
    throw new Error(`the latest release's tag is ${JSON.stringify(release.tag_name)}`);
  }
  return tag;
}

/**
 * Runs a command, giving each line it prints, and how it ended.
 * @param {{ file: string, args: string[] }} command
 * @param {NodeJS.ProcessEnv} env
 * @param {(line: string) => void} onLine
 * @param {vscode.CancellationToken} token
 * @returns {Promise<{ status: number | null, last: string, cancelled: boolean }>}
 */
function spawned(command, env, onLine, token) {
  return new Promise((resolve) => {
    let last = "";
    const child = childProcess.spawn(command.file, command.args, { env, stdio: ["ignore", "pipe", "pipe"] });
    const lines = (/** @type {Buffer} */ chunk) => {
      for (const line of String(chunk).split(/\r?\n/).filter((l) => l.trim())) {
        last = line.replace(/^stilt: /, "");
        onLine(line);
      }
    };
    child.stdout.on("data", lines);
    child.stderr.on("data", lines);
    token.onCancellationRequested(() => child.kill());
    child.on("error", (error) => resolve({ status: -1, last: error.message, cancelled: false }));
    child.on("close", (status) => resolve({ status, last, cancelled: token.isCancellationRequested }));
  });
}

/** @param {string} text */
function firstLine(text) {
  return text.split("\n").find((l) => l.trim())?.trim() || "it gave no reason";
}

module.exports = { Installer };
