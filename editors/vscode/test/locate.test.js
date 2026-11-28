// @ts-check
// The lookup of `stilt` (../src/locate.js), against fake toolchains in a temporary directory: the
// order of the places looked in, the version check, and the login shell's answer, under a
// `PATH` that holds none of them, as an editor started from the Dock or a desktop menu has.

"use strict";

const assert = require("node:assert/strict");
const fs = require("node:fs");
const os = require("node:os");
const path = require("node:path");
const { describe, it, beforeEach } = require("node:test");
const locate = require("../src/locate");

const unix = process.platform !== "win32";

/** A fresh directory for one test. */
function scratch() {
  return fs.mkdtempSync(path.join(os.tmpdir(), "stilt-locate-"));
}

/**
 * Writes an executable script at `file` that prints `out` and exits with `status`.
 * @param {string} file
 * @param {string} out
 * @param {number} [status]
 */
function script(file, out, status = 0) {
  fs.mkdirSync(path.dirname(file), { recursive: true });
  fs.writeFileSync(file, `#!/bin/sh\nprintf '%s\\n' '${out}'\nexit ${status}\n`, { mode: 0o755 });
  return file;
}

/** The path of a `stilt` found, if one was. @param {import("../src/locate").Found} found */
function pathOf(found) {
  return found.kind === "missing" ? undefined : found.path;
}

/** A fake `stilt` of a version. @param {string} file @param {string} version */
function stilt(file, version) {
  return script(file, `stilt ${version} (bef482a9f 2026-11-26)`);
}

/**
 * Where to look: a home and a `PATH` of the test's own, and a login shell that finds nothing,
 * so that the machine's own `stilt` is never found.
 * @param {string} dir
 * @param {Partial<import("../src/locate").Where>} [more]
 * @returns {import("../src/locate").Where}
 */
function at(dir, more = {}) {
  const shell = script(path.join(dir, "shells", "none"), "");
  return { home: path.join(dir, "home"), env: { PATH: path.join(dir, "empty"), SHELL: shell, USER: "nobody" }, platform: process.platform, ...more };
}

describe("versions", () => {
  it("reads the version that `stilt --version` prints", () => {
    assert.equal(locate.parseVersion("stilt 2027.1.0 (bef482a9f 2026-11-26)\n"), "2027.1.0");
    assert.equal(locate.parseVersion("stilt 2027.2.13"), "2027.2.13");
    assert.equal(locate.parseVersion("rustc 1.80.0"), undefined);
  });

  it("compares versions by their numbers", () => {
    assert.ok(locate.compare("2027.1.0", "2027.10.0") < 0);
    assert.ok(locate.compare("2028.1.0", "2027.9.9") > 0);
    assert.equal(locate.compare("2027.1.0", "2027.1.0"), 0);
  });
});

describe("expand", () => {
  const where = { home: "/home/ada", env: { STILT_ROOT: "/opt/stilt" }, platform: /** @type {NodeJS.Platform} */ ("linux"), folder: "/work/calc" };

  it("expands the home, the workspace folder and variables", () => {
    assert.equal(locate.expand("~/.stilt/bin/stilt", where), "/home/ada/.stilt/bin/stilt");
    assert.equal(locate.expand("${userHome}/bin/stilt", where), "/home/ada/bin/stilt");
    assert.equal(locate.expand("${workspaceFolder}/target/release/stilt", where), "/work/calc/target/release/stilt");
    assert.equal(locate.expand("${env:STILT_ROOT}/bin/stilt", where), "/opt/stilt/bin/stilt");
  });

  it("reads a relative path from the workspace folder, and leaves a bare name", () => {
    assert.equal(locate.expand("target/debug/stilt", where), path.join("/work/calc", "target/debug/stilt"));
    assert.equal(locate.expand("stilt", where), "stilt");
  });
});

describe("candidates", () => {
  it("looks in $STILT_HOME, ~/.stilt, the PATH, then the package managers' directories", () => {
    const list = locate.candidates({ home: "/h", env: { STILT_HOME: "/s", PATH: "/usr/bin" }, platform: "linux" });
    assert.deepEqual(list.slice(0, 3).map((c) => c.file), ["/s/bin/stilt", "/h/.stilt/bin/stilt", "/usr/bin/stilt"]);
    assert.ok(list.some((c) => c.file === "/opt/homebrew/bin/stilt"));
    assert.ok(list.some((c) => c.file === "/h/.nix-profile/bin/stilt"));
  });

  it("tries only the file that `stilt.path` names", () => {
    const list = locate.candidates({ configured: "/opt/stilt/bin/stilt", home: "/h", env: { PATH: "/usr/bin" }, platform: "linux" });
    assert.deepEqual(list, [{ file: "/opt/stilt/bin/stilt", source: "stilt.path" }]);
  });

  it("looks for a bare name that `stilt.path` gives on the PATH alone", () => {
    const list = locate.candidates({ configured: "stilt-dev", home: "/h", env: { PATH: "/usr/bin" }, platform: "linux" });
    assert.equal(list[0].file, "/usr/bin/stilt-dev");
    assert.ok(!list.some((c) => c.file.includes(".stilt")));
  });
});

describe("find", { skip: !unix && "the fake toolchains are shell scripts" }, () => {
  beforeEach(() => locate.forgetShell());

  it("finds install.sh's stilt in ~/.stilt/bin with nothing on the PATH", async () => {
    const dir = scratch();
    const file = stilt(path.join(dir, "home", ".stilt", "bin", "stilt"), "2027.1.0");
    const found = await locate.find(at(dir));
    assert.deepEqual(found, { kind: "found", path: file, version: "2027.1.0", source: "~/.stilt" });
  });

  it("prefers $STILT_HOME to ~/.stilt, and ~/.stilt to the PATH", async () => {
    const dir = scratch();
    stilt(path.join(dir, "home", ".stilt", "bin", "stilt"), "2027.1.0");
    stilt(path.join(dir, "path", "stilt"), "2027.1.0");
    const custom = stilt(path.join(dir, "custom", "bin", "stilt"), "2027.1.0");
    const where = at(dir);
    where.env = { ...where.env, STILT_HOME: path.join(dir, "custom"), PATH: path.join(dir, "path") };
    assert.equal(pathOf(await locate.find(where)), custom);
  });

  it("reports a stilt older than the extension needs", async () => {
    const dir = scratch();
    stilt(path.join(dir, "home", ".stilt", "bin", "stilt"), "2026.9.0");
    const found = await locate.find(at(dir));
    assert.equal(found.kind, "outdated");
  });

  it("reports a stilt that doesn't run, and goes on to one that does", async () => {
    const dir = scratch();
    script(path.join(dir, "home", ".stilt", "bin", "stilt"), "cannot execute: wrong architecture", 126);
    const good = stilt(path.join(dir, "path", "stilt"), "2027.1.0");
    const where = at(dir);
    where.env = { ...where.env, PATH: path.join(dir, "path") };
    assert.equal(pathOf(await locate.find(where)), good);
    where.env = { ...where.env, PATH: path.join(dir, "empty") };
    const broken = await locate.find(where);
    assert.equal(broken.kind, "broken");
  });

  it("asks the login shell last, and keeps its answer", async () => {
    const dir = scratch();
    const file = stilt(path.join(dir, "elsewhere", "stilt"), "2027.1.0");
    const shell = script(path.join(dir, "shells", "zsh"), `_STILT_LOOKUP_${file}\n_STILT_LOOKUP_`);
    const where = at(dir);
    where.env = { ...where.env, SHELL: shell };
    const found = await locate.find(where);
    assert.deepEqual(found, { kind: "found", path: file, version: "2027.1.0", source: "the login shell's PATH" });
    fs.writeFileSync(shell, "#!/bin/sh\nexit 1\n");
    assert.equal(pathOf(await locate.find(where)), file);
  });

  it("ignores what the shell's profile prints around its answer", async () => {
    const dir = scratch();
    const file = stilt(path.join(dir, "elsewhere", "stilt"), "2027.1.0");
    const noisy = `Welcome back!\n_STILT_LOOKUP_${file}\n_STILT_LOOKUP_\nbye`;
    const where = at(dir);
    where.env = { ...where.env, SHELL: script(path.join(dir, "shells", "noisy"), noisy) };
    assert.equal(pathOf(await locate.find(where)), file);
  });

  it("says where it looked when it finds nothing", async () => {
    const dir = scratch();
    const found = await locate.find(at(dir));
    assert.equal(found.kind, "missing");
    assert.ok(found.kind === "missing" && found.tried.includes(path.join(dir, "home", ".stilt", "bin")));
    assert.ok(found.kind === "missing" && found.configured === undefined);
  });

  it("reports a `stilt.path` that names no file, and looks nowhere else", async () => {
    const dir = scratch();
    stilt(path.join(dir, "home", ".stilt", "bin", "stilt"), "2027.1.0");
    const found = await locate.find(at(dir, { configured: "~/nope/stilt" }));
    assert.deepEqual(found, { kind: "missing", configured: path.join(dir, "home", "nope", "stilt"), tried: [path.join(dir, "home", "nope")] });
  });

  it("reads a relative `stilt.path` from the workspace folder", async () => {
    const dir = scratch();
    const file = stilt(path.join(dir, "repo", "target", "release", "stilt"), "2027.1.0");
    const found = await locate.find(at(dir, { configured: "target/release/stilt", folder: path.join(dir, "repo") }));
    assert.equal(found.kind === "found" && found.source, "stilt.path");
    assert.equal(found.kind === "found" && found.path, file);
  });
});

describe("manager", { skip: !unix && "paths are POSIX" }, () => {
  it("tells install.sh's toolchain, through its link, from Homebrew's and Nix's", () => {
    const dir = scratch();
    const real = stilt(path.join(dir, "home", ".stilt", "2027.1.0", "bin", "stilt"), "2027.1.0");
    fs.mkdirSync(path.join(dir, "home", ".stilt", "bin"), { recursive: true });
    const link = path.join(dir, "home", ".stilt", "bin", "stilt");
    fs.symlinkSync(real, link);
    assert.equal(locate.manager(link, { home: path.join(dir, "home"), env: {} }), "installer");
    assert.equal(locate.manager("/opt/homebrew/Cellar/stilt/2027.1.0/bin/stilt", { home: "/h", env: {} }), "homebrew");
    assert.equal(locate.manager("/nix/store/abc-stilt-2027.1.0/bin/stilt", { home: "/h", env: {} }), "nix");
    assert.equal(locate.manager("/work/stilt/target/release/stilt", { home: "/h", env: {} }), "other");
  });
});

describe("installable", () => {
  it("knows the hosts install.sh has a toolchain for", () => {
    assert.ok(locate.installable("darwin", "arm64"));
    assert.ok(locate.installable("linux", "x64"));
    assert.ok(locate.installable("linux", "arm64"));
    assert.ok(!locate.installable("darwin", "x64"));
    assert.ok(!locate.installable("win32", "x64"));
  });
});
