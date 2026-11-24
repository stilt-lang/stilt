// What the playground asks of its two tools, the compiler built for WebAssembly
// (`compiler.wasm`, run through `wasi.js`) and the reference interpreter built for JavaScript
// (`interpreter.js`), for a program of one file, `main.lt`. The page asks it in a worker of each
// tool, which fetches the module, or, opened from a file, where browsers start no worker and
// fetch nothing, on the page itself, which loads the module from `compiler.js`, in base64.

"use strict";

{
  const FILE = "main.lt";
  let compiled = null;

  /** The compiler's module, compiled once: from `compiler.js` if it is loaded, or fetched. */
  function compiler() {
    compiled ??= globalThis.stiltCompiler ? fromBase64(globalThis.stiltCompiler) : fetched();
    return compiled;
  }

  /** The module whose bytes `text` holds in base64. */
  function fromBase64(text) {
    const binary = globalThis.atob(text);
    const bytes = new Uint8Array(binary.length);
    for (let i = 0; i < binary.length; i++) bytes[i] = binary.charCodeAt(i);
    return WebAssembly.compile(bytes);
  }

  /** The module fetched beside this script, compiled as it arrives where the server allows. */
  async function fetched() {
    const url = new URL("compiler.wasm", globalThis.location.href);
    try {
      return await WebAssembly.compileStreaming(fetch(url));
    } catch {
      const response = await fetch(url);
      if (!response.ok) throw new Error(`compiler.wasm: ${response.status}`);
      return WebAssembly.compile(await response.arrayBuffer());
    }
  }

  /** Runs the compiler's command `args` on the program `text`. */
  async function command(args, text) {
    return globalThis.StiltWasi.run(await compiler(), [...args, FILE], { [FILE]: text });
  }

  /**
   * Answers `request`: `live`, the program's diagnostics and facts as the compiler's `live` gives
   * them, or why it gave none; `show`, what `stilt show ADDRESS` prints; and `run`, what the
   * reference interpreter's run of the program writes, and its exit status.
   */
  async function handle(request) {
    switch (request.kind) {
      case "live": {
        const done = await command(["live"], request.text);
        if (done.status > 1) return { failed: done.stderr || `the compiler ended with ${done.status}` };
        return JSON.parse(done.stdout);
      }
      case "show":
        return command(["show", request.address], request.text);
      case "run": {
        const done = globalThis.stiltRun(request.text);
        return { status: done.status, output: Array.from(done.output, (p) => Array.from(p)) };
      }
      default:
        throw new Error(`no request ${request.kind}`);
    }
  }

  globalThis.StiltEngine = { handle };
}
