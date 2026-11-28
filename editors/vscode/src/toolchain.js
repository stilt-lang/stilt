// @ts-check
// The `stilt` that the extension runs, found once and kept until a setting that names it
// changes, an install or update ends, or the servers restart. Every part of the extension that
// runs `stilt` asks here for its path and environment: the language servers (./programs.js), the
// documents of `stilt show` (./show.js), the tests, the tasks and the debugger's builds. The
// context key `stilt:toolchain` holds what was found, `found`, `outdated`, `broken`, `missing`
// or `looking`, for the walkthrough and the menus.

"use strict";

const os = require("os");
const path = require("path");
const vscode = require("vscode");
const locate = require("./locate");

/** @typedef {import("./locate").Found} Found */

/**
 * The `stilt.path` that applies to a program, and the workspace folder it is read from.
 * @param {vscode.Uri} [scope]
 */
function setting(scope) {
  const configured = vscode.workspace.getConfiguration("stilt", scope).get("path", "") || "";
  const folder = scope ? vscode.workspace.getWorkspaceFolder(scope) : vscode.workspace.workspaceFolders?.[0];
  return { configured, folder: folder?.uri.scheme === "file" ? folder.uri.fsPath : undefined };
}

class Toolchain {
  constructor() {
    /** @type {Map<string, Promise<Found>>} */
    this.lookups = new Map();
    /** @type {Map<string, Found>} */
    this.found = new Map();
    this.changed = new vscode.EventEmitter();
    /** Fires when a lookup ends, with what it found. */
    this.onDidChange = this.changed.event;
    /** @type {vscode.LogOutputChannel | undefined} */
    this.log = undefined;
  }

  /** @param {vscode.Uri} [scope] */
  key(scope) {
    const { configured, folder } = setting(scope);
    // A setting that is relative or names the folder means another file in each folder.
    const perFolder = configured && (!path.isAbsolute(configured) || configured.includes("${workspaceFolder}"));
    return `${configured}\0${perFolder ? folder || "" : ""}`;
  }

  /**
   * Finds the `stilt` of a program, once until `forget`.
   * @param {vscode.Uri} [scope]
   * @returns {Promise<Found>}
   */
  resolve(scope) {
    const key = this.key(scope);
    const pending = this.lookups.get(key);
    if (pending) {
      return pending;
    }
    vscode.commands.executeCommand("setContext", "stilt:toolchain", "looking");
    const lookup = locate.find({ ...setting(scope), env: this.env(scope) }).then((found) => {
      if (this.lookups.get(key) === lookup) {
        this.found.set(key, found);
        this.report(found);
        vscode.commands.executeCommand("setContext", "stilt:toolchain", found.kind);
        this.changed.fire(found);
      }
      return found;
    });
    this.lookups.set(key, lookup);
    return lookup;
  }

  /** @param {Found} found */
  report(found) {
    if (found.kind === "missing") {
      const what = found.configured ? `\`stilt.path\` names ${found.configured}, which isn't an executable` : "no stilt was found";
      this.log?.warn(`${what}; looked in ${found.tried.join(", ")}`);
    } else if (found.kind === "broken") {
      this.log?.error(`${found.path} (from ${found.source}) doesn't run: ${found.error}`);
    } else {
      const old = found.kind === "outdated" ? `, older than the ${locate.NEEDS} this extension needs` : "";
      this.log?.info(`using stilt ${found.version} at ${found.path}, from ${found.source}${old}`);
    }
  }

  /**
   * What the last lookup for a program found, if it has ended.
   * @param {vscode.Uri} [scope]
   */
  current(scope) {
    return this.found.get(this.key(scope));
  }

  /**
   * The `stilt` to run for a program: the one found, or what the settings name before a lookup
   * ends, so that a task made at once still runs.
   * @param {vscode.Uri} [scope]
   */
  binary(scope) {
    const found = this.current(scope);
    if (found && found.kind !== "missing") {
      return found.path;
    }
    const { configured, folder } = setting(scope);
    const at = { folder, env: process.env, home: os.homedir(), platform: process.platform };
    return configured ? locate.expand(configured, at) : "stilt";
  }

  /**
   * The environment of every `stilt` the extension runs: the editor's, with `stilt.env` over it.
   * @param {vscode.Uri} [scope]
   * @returns {NodeJS.ProcessEnv}
   */
  env(scope) {
    /** @type {Record<string, string | null>} */
    const extra = vscode.workspace.getConfiguration("stilt", scope).get("env", {}) || {};
    const env = { ...process.env };
    for (const [name, value] of Object.entries(extra)) {
      if (value === null) {
        delete env[name];
      } else {
        env[name] = String(value);
      }
    }
    return env;
  }

  /** Forgets every lookup, the login shell's answer among them, so the next one looks again. */
  forget() {
    this.lookups.clear();
    this.found.clear();
    locate.forgetShell();
  }

  dispose() {
    this.changed.dispose();
  }
}

/** The one toolchain of the extension. */
const toolchain = new Toolchain();

/**
 * The `stilt` binary for a program.
 * @param {vscode.Uri} [scope]
 */
function binary(scope) {
  return toolchain.binary(scope);
}

module.exports = { toolchain, binary, setting };
