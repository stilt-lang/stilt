// The files the playground's page loads, under `/playground/`: its scripts, as they are in the
// repository's `playground/page/`; the editors' grammar, as a script; and the compiler's module
// and the interpreter that `just playground` builds into `target/playground`. The module is also
// given in base64 inside `compiler.js`, which the page loads only where no worker starts.

import fs from "node:fs";
import path from "node:path";
import type { APIRoute, GetStaticPaths } from "astro";
import { GRAMMAR } from "../../lib/highlight";
import { PLAYGROUND, read } from "../../lib/repo";

/** The scripts of `playground/page/`, served as they are. */
const SCRIPTS = ["wasi.js", "highlight.js", "engine.js", "worker.js", "playground.js"];

/** The build `name` of `just playground`, which must have run. */
function built(name: string): Buffer {
  const file = path.join(PLAYGROUND, name);
  if (!fs.existsSync(file)) throw new Error(`${file} is missing; \`just playground\` builds it`);
  return fs.readFileSync(file);
}

/** Each file, by its name. */
const FILES: Record<string, () => string | Buffer> = {
  ...Object.fromEntries(SCRIPTS.map((name) => [name, () => read(`playground/page/${name}`)])),
  "grammar.js": () => `globalThis.stiltGrammar = ${read(GRAMMAR)};\n`,
  "compiler.wasm": () => built("compiler.wasm"),
  "compiler.js": () => `globalThis.stiltCompiler = "${built("compiler.wasm").toString("base64")}";\n`,
  "interpreter.js": () => built("interpreter.js"),
};

const TYPES: Record<string, string> = { js: "text/javascript; charset=utf-8", wasm: "application/wasm" };

export const getStaticPaths = (() =>
  Object.keys(FILES).map((file) => ({ params: { file } }))) satisfies GetStaticPaths;

export const GET: APIRoute = ({ params }) => {
  const name = String(params.file);
  const body = FILES[name]();
  const type = TYPES[name.slice(name.lastIndexOf(".") + 1)];
  return new Response(typeof body === "string" ? body : new Uint8Array(body), {
    headers: { "Content-Type": type },
  });
};
