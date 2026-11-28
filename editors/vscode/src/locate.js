// @ts-check
// Finding `stilt`, apart from the editor's API so that plain Node tests it (../test/). The
// places looked in, in order: the path that `stilt.path` names; `$STILT_HOME/bin` and
// `~/.stilt/bin`, where install.sh puts it; the `PATH`; the directories of Homebrew and Nix; and
// last the `PATH` of the user's login shell. An editor started from the Dock or a desktop menu
// holds the environment it read when it started, which lacks a directory added to the shell's
// profile since, as install.sh asks for `~/.stilt/bin`, so a bare `stilt` isn't found there.

"use strict";

const childProcess = require("child_process");
const fs = require("fs");
const os = require("os");
const path = require("path");

/** The oldest toolchain whose language server answers everything the extension asks. */
const NEEDS = "2027.1.0";

/** How long `stilt --version` and the login shell's lookup may take. */
const TIMEOUT = 5000;

/**
 * Where to look, and with what.
 * @typedef {{ configured?: string, folder?: string, env: NodeJS.ProcessEnv, home: string, platform: NodeJS.Platform }} Where
 */

/**
 * A `stilt` that was looked for: found and recent enough, found but older than `NEEDS`, found
 * but unable to run, or found nowhere.
 * @typedef {{ kind: "found" | "outdated", path: string, version: string, source: string }
 *   | { kind: "broken", path: string, source: string, error: string }
 *   | { kind: "missing", configured?: string, tried: string[] }} Found
 */

/** @param {Partial<Where>} [given] @returns {Where} */
function where(given = {}) {
  return { env: process.env, home: os.homedir(), platform: process.platform, ...given };
}

/**
 * A setting's path with `~`, `${userHome}`, `${workspaceFolder}` and `${env:NAME}` replaced, and
 * made absolute from the workspace folder when it is relative and names a directory.
 * @param {string} value
 * @param {Where} at
 */
function expand(value, at) {
  let out = value.trim()
    .replace(/^~(?=$|[\\/])/, at.home)
    .replace(/\$\{userHome\}/g, at.home)
    .replace(/\$\{env:([A-Za-z_][A-Za-z0-9_]*)\}/g, (_, name) => at.env[name] || "");
  if (at.folder) {
    out = out.replace(/\$\{workspaceFolder\}/g, at.folder);
  }
  if (!path.isAbsolute(out) && /[\\/]/.test(out) && at.folder) {
    out = path.join(at.folder, out);
  }
  return out;
}

/** @param {Where} at */
function exe(at, name = "stilt") {
  return at.platform === "win32" && !name.toLowerCase().endsWith(".exe") ? `${name}.exe` : name;
}

/** @param {string} file */
function runnable(file) {
  try {
    fs.accessSync(file, fs.constants.X_OK);
    return fs.statSync(file).isFile();
  } catch {
    return false;
  }
}

/**
 * The directories of the package managers that install Stilt, which an editor started outside a
 * shell may not have on its `PATH`.
 * @param {Where} at
 */
function managed(at) {
  if (at.platform === "win32") {
    return [];
  }
  const user = at.env.USER || path.basename(at.home);
  return [
    "/opt/homebrew/bin",
    "/usr/local/bin",
    path.join(at.home, ".nix-profile", "bin"),
    `/etc/profiles/per-user/${user}/bin`,
    "/nix/var/nix/profiles/default/bin",
    "/run/current-system/sw/bin",
  ];
}

/**
 * The files to try, in order, each with where it comes from. A `stilt.path` that names a file
 * is the only one tried: a wrong setting is reported, never passed over.
 * @param {Where} at
 * @returns {{ file: string, source: string }[]}
 */
function candidates(at) {
  const configured = at.configured ? expand(at.configured, at) : "";
  const named = configured && configured !== "stilt" ? configured : "";
  if (named && (path.isAbsolute(named) || /[\\/]/.test(named))) {
    return [{ file: named, source: "stilt.path" }];
  }
  const name = exe(at, named || "stilt");
  const tried = [];
  if (!named) {
    if (at.env.STILT_HOME) {
      tried.push({ file: path.join(expand(at.env.STILT_HOME, at), "bin", name), source: "$STILT_HOME" });
    }
    tried.push({ file: path.join(at.home, ".stilt", "bin", name), source: "~/.stilt" });
  }
  const dirs = (at.env.PATH || at.env.Path || "").split(path.delimiter).filter(Boolean);
  tried.push(...dirs.map((dir) => ({ file: path.join(dir, name), source: "PATH" })));
  tried.push(...managed(at).map((dir) => ({ file: path.join(dir, name), source: "a package manager" })));
  return tried;
}

/** The login shell's answers, asked once a session for each name. @type {Map<string, Promise<string | undefined>>} */
const shellAnswers = new Map();

/**
 * Where the user's login shell finds `name`, as a terminal would, or `undefined`. It runs the
 * shell once for each name, as an interactive login shell so that it reads the profile and rc
 * files, between markers that set the answer apart from what those files print.
 * @param {string} name
 * @param {Where} at
 * @returns {Promise<string | undefined>}
 */
function loginShell(name, at) {
  if (at.platform === "win32" || !/^[\w.+-]+$/.test(name)) {
    return Promise.resolve(undefined);
  }
  const cached = shellAnswers.get(name);
  if (cached) {
    return cached;
  }
  const shell = at.env.SHELL || (at.platform === "darwin" ? "/bin/zsh" : "/bin/sh");
  const mark = "_STILT_LOOKUP_";
  const script = `printf '%s' ${mark}; command -v ${name}; printf '%s' ${mark}`;
  // VS Code sets VSCODE_RESOLVING_ENVIRONMENT when it reads the shell's environment, so that rc
  // files can skip what only a terminal needs; this lookup asks the same.
  const env = { ...at.env, VSCODE_RESOLVING_ENVIRONMENT: "1", DISABLE_AUTO_UPDATE: "true", TERM: "dumb" };
  const answer = new Promise((resolve) => {
    let out = "";
    const child = childProcess.spawn(shell, ["-ilc", script], { env, stdio: ["ignore", "pipe", "ignore"], detached: false });
    const timer = setTimeout(() => child.kill("SIGKILL"), TIMEOUT);
    child.stdout.on("data", (chunk) => (out += chunk));
    child.on("error", () => resolve(undefined));
    child.on("close", () => {
      clearTimeout(timer);
      const between = out.split(mark)[1] || "";
      const line = between.split(/\r?\n/).map((l) => l.trim()).find((l) => path.isAbsolute(l));
      resolve(line && runnable(line) ? line : undefined);
    });
  });
  shellAnswers.set(name, /** @type {Promise<string | undefined>} */ (answer));
  return /** @type {Promise<string | undefined>} */ (answer);
}

/** Forgets the login shell's answers, so the next lookup asks it again. */
function forgetShell() {
  shellAnswers.clear();
}

/**
 * The version that `stilt --version` prints, as `stilt 2027.1.0 (bef482a9f 2026-11-26)`.
 * @param {string} text
 */
function parseVersion(text) {
  const m = /^stilt\s+(\d+\.\d+\.\d+\S*)/m.exec(text);
  return m ? m[1] : undefined;
}

/**
 * Compares two versions, year.minor.patch, by their numbers: negative when `a` is older.
 * @param {string} a
 * @param {string} b
 */
function compare(a, b) {
  const parts = (/** @type {string} */ v) => v.split(/[.-]/).slice(0, 3).map((p) => parseInt(p, 10) || 0);
  const [x, y] = [parts(a), parts(b)];
  for (let i = 0; i < 3; i++) {
    if (x[i] !== y[i]) {
      return x[i] - y[i];
    }
  }
  return 0;
}

/**
 * Runs `stilt --version`.
 * @param {string} file
 * @param {NodeJS.ProcessEnv} env
 * @returns {Promise<{ version?: string, error?: string }>}
 */
function version(file, env) {
  return new Promise((resolve) => {
    childProcess.execFile(file, ["--version"], { env, timeout: TIMEOUT }, (error, stdout, stderr) => {
      const found = parseVersion(String(stdout));
      if (found) {
        resolve({ version: found });
      } else {
        const why = String(stderr).trim() || (error ? error.message : `it printed ${JSON.stringify(String(stdout).trim())}`);
        resolve({ error: why });
      }
    });
  });
}

/**
 * Finds `stilt`, and asks the one found its version.
 * @param {Partial<Where>} [given]
 * @returns {Promise<Found>}
 */
async function find(given) {
  const at = where(given);
  const list = candidates(at);
  const value = at.configured ? expand(at.configured, at) : "";
  const configured = value && value !== "stilt" ? value : undefined;
  const isFile = list.length === 1 && list[0].source === "stilt.path";
  const seen = new Set();
  /** @type {Found | undefined} */
  let broken;
  const shell = isFile ? [] : [{ file: "", source: "the login shell's PATH" }];
  for (const candidate of [...list, ...shell]) {
    const file = candidate.file || (await loginShell(exe(at, configured || "stilt"), at));
    if (!file || seen.has(file) || !runnable(file)) {
      continue;
    }
    seen.add(file);
    const asked = await version(file, at.env);
    if (asked.version) {
      const kind = compare(asked.version, NEEDS) < 0 ? "outdated" : "found";
      return { kind, path: file, version: asked.version, source: candidate.source };
    }
    broken = broken || { kind: "broken", path: file, source: candidate.source, error: asked.error || "" };
  }
  const tried = [...new Set(list.map((c) => path.dirname(c.file)))];
  if (!isFile && at.platform !== "win32") {
    tried.push("the login shell's PATH");
  }
  return broken || { kind: "missing", configured, tried };
}

/**
 * What installed a `stilt`, which says how to update it: install.sh, Homebrew, Nix, or neither,
 * as a build of Stilt's repository.
 * @param {string} file
 * @param {Partial<Where>} [given]
 * @returns {"installer" | "homebrew" | "nix" | "other"}
 */
function manager(file, given) {
  const at = where(given);
  let real = file;
  try {
    real = fs.realpathSync(file);
  } catch {
    // A file that vanished is updated by nobody.
  }
  const homes = [at.env.STILT_HOME, path.join(at.home, ".stilt")].filter(Boolean).map((h) => {
    try {
      return fs.realpathSync(/** @type {string} */ (h));
    } catch {
      return /** @type {string} */ (h);
    }
  });
  if (homes.some((h) => real.startsWith(h + path.sep))) {
    return "installer";
  }
  if (real.includes(`${path.sep}Cellar${path.sep}`)) {
    return "homebrew";
  }
  return real.startsWith(`${path.sep}nix${path.sep}store${path.sep}`) ? "nix" : "other";
}

/**
 * Whether install.sh has a toolchain for this machine: macOS on ARM, and Linux on x86-64 or ARM.
 * @param {NodeJS.Platform} [platform]
 * @param {string} [arch]
 */
function installable(platform = process.platform, arch = process.arch) {
  return (platform === "darwin" && arch === "arm64") || (platform === "linux" && (arch === "x64" || arch === "arm64"));
}

module.exports = { NEEDS, expand, candidates, find, loginShell, forgetShell, parseVersion, compare, manager, installable };
