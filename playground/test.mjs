// The playground's test, which `just playground` runs under Node once it has built the
// playground: one check, one show and one run of the page's first program, in the browser's
// builds, through the page's own WASI host and engine, must print what the native toolchain
// prints for the same program, `stilt` and `stilt-ref`, with the same exit status.
//
//   node playground/test.mjs STILT STILT_REF BUILT
//
// BUILT is the directory that holds `compiler.wasm` and `interpreter.js`.

import { execFileSync } from "node:child_process";
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { createRequire } from "node:module";
import { tmpdir } from "node:os";
import { dirname, join, resolve } from "node:path";
import { fileURLToPath } from "node:url";

const require = createRequire(import.meta.url);
const here = dirname(fileURLToPath(import.meta.url));
const [stilt, stiltRef, built] = process.argv.slice(2).map((p) => resolve(p));
if (!built) {
  console.error("usage: node playground/test.mjs STILT STILT_REF BUILT");
  process.exit(2);
}

// The page's scripts, as the page loads them: the WASI host, the compiler's module in base64,
// the interpreter, and the engine that asks them.
const wasm = readFileSync(join(built, "compiler.wasm"));
globalThis.StiltWasi = require(join(here, "page", "wasi.js"));
globalThis.stiltCompiler = wasm.toString("base64");
globalThis.stiltRun = require(join(built, "interpreter.js")).stiltRun;
require(join(here, "page", "engine.js"));
const engine = globalThis.StiltEngine;

const program = readFileSync(join(here, "page", "example.lt"), "utf8");
// The same program with an error, whose diagnostic has a fix with edits (effects.rows).
const broken = program.replace("fn main() / io {", "fn main() {");
if (broken === program) throw new Error("the first program's `main` is no longer `fn main() / io`");

/** What the native command `exe` with `args` prints for `text` as `main.lt`, and its status. */
function native(exe, args, text) {
  const dir = mkdtempSync(join(tmpdir(), "stilt-playground-"));
  writeFileSync(join(dir, "main.lt"), text);
  try {
    const stdout = execFileSync(exe, [...args, "main.lt"], { cwd: dir, encoding: "utf8", stdio: "pipe" });
    return { status: 0, stdout, stderr: "" };
  } catch (e) {
    if (typeof e.status !== "number") throw e;
    return { status: e.status, stdout: e.stdout, stderr: e.stderr };
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}

/** A run's pieces of output as one stdout, one stderr and its status. */
function joined(run) {
  const of = (stream) => run.output.filter(([s]) => s === stream).map(([, t]) => t).join("");
  return { status: run.status, stdout: of("stdout"), stderr: of("stderr") };
}

let failed = 0;

/** Compares what the browser's build gave with what the native toolchain gave. */
function same(what, browser, expected) {
  for (const key of ["status", "stdout", "stderr"]) {
    if (browser[key] !== expected[key]) {
      failed += 1;
      console.error(`FAIL ${what}: ${key} differs`);
      console.error(`  browser: ${JSON.stringify(browser[key])}`);
      console.error(`  native:  ${JSON.stringify(expected[key])}`);
      return;
    }
  }
  console.log(`ok ${what}`);
}

const compiled = await WebAssembly.compile(wasm);
const check = await globalThis.StiltWasi.run(compiled, ["check", "--json", "main.lt"], {
  "main.lt": broken,
});
same("check --json", check, native(stilt, ["check", "--json"], broken));

// What the page shows as one types holds the same records, each also rendered as `check` renders
// it for people.
const live = await engine.handle({ kind: "live", text: broken });
const rendered = native(stilt, ["check"], broken).stderr;
same(
  "live",
  { status: 0, stdout: JSON.stringify({ diagnostics: live.diagnostics }) + "\n", stderr: live.rendered.join("\n") },
  { status: 0, stdout: check.stdout, stderr: rendered },
);

const show = await engine.handle({ kind: "show", address: "main.hit", text: program });
same("show main.hit", show, native(stilt, ["show", "main.hit"], program));

const run = joined(await engine.handle({ kind: "run", text: program }));
same("run, against stilt-ref", run, native(stiltRef, ["run"], program));
same("run, against stilt", run, native(stilt, ["run"], program));

if (failed) {
  console.error(`${failed} of the playground's comparisons failed`);
  process.exit(1);
}
