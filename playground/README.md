# Playground

Stilt in the browser, with nothing installed: the website's page `/playground/`, which `just site` builds into `target/site`. An editor whose program the compiler checks as one types, with each diagnostic marked under the code and listed under the editor as `stilt check` renders it, and each fact the compiler infers written at the end of the line it comes from, as the language server's inlay hints write it; beside the editor, what `stilt show` prints of the function at the cursor, with what each of its facts means; a Run button, which runs the program in the reference interpreter; and a link that holds the program in its fragment, `#code=` and the program's UTF-8 in base64url. Each program of the guide and of the error index links to the playground with its code.

| Path | Holds |
| --- | --- |
| `compiler/` | `stilt-playground`, the compiler's `check`, `show` and the facts beside each function for a program of one file, built for `wasm32-wasip1`. It compiles the modules of `stilt show` and of `check`'s reports from `compiler/stilt-cli/src/` as they are, and adds only the commands that join them and `live`, which gives the diagnostics and the facts at once |
| `interpreter/` | The reference interpreter's `run` of a program of one file, built for JavaScript by js_of_ocaml, with what the program writes collected for the page |
| `page/` | The page's scripts and style: the WASI host that runs the compiler's module, the highlighting, which reads the editors' TextMate grammar ([`editors/vscode/syntaxes/stilt.tmLanguage.json`](../editors/vscode/syntaxes/stilt.tmLanguage.json)), the workers and the page itself, and the program it opens with |
| `test.mjs` | The test that `just playground` runs under Node |

The website ([`site/`](../site/)) writes the page, and serves the scripts with the builds of `just playground`: the compiler's module as `compiler.wasm`, which the page's workers fetch, and in base64 inside `compiler.js`, which the page loads where the browser starts no worker. The interpreter loads at the first run.

## Building and testing

`just playground` builds both into `target/playground` and runs `test.mjs` under Node: one `check --json`, one `show` and one run of the page's first program, through the page's own WASI host and engine, must print what the native `stilt` and `stilt-ref` print for it, with the same exit status. `just site` builds them too.

The compiler builds with the toolchain that [`rust-toolchain.toml`](../rust-toolchain.toml) pins, whose `wasm32-wasip1` target `just setup` installs, in the profile `playground` of the workspace's manifest, optimized for size, then through binaryen's `wasm-opt`, which `just toolchain` fetches. The interpreter needs js_of_ocaml in the opam switch, which `just setup` installs from the project's dependencies.

## What runs in the browser

Checking and `show` are the compiler's own, whole: every diagnostic, fix and fact of a program of one file. A program of one file has no manifest, so it has no dependency and links no C library; `stilt show` of an address with a hash isn't offered. Procedural macros run on the module's one thread.

Running is the reference interpreter's, compiled from the same sources as `stilt-ref`, with no arguments and an empty standard input. `std.fs` reads and writes files in js_of_ocaml's memory, which keeps them until the page closes or Stop ends a run, and the clocks read the browser's. `interpreter/stubs.js` gives what js_of_ocaml's runtime doesn't: a file in memory has a status, sleeping waits, a path is its own real path, and floats are formatted from their exact digits, a tie to even, as C's printf rounds them. What a browser can't give, it doesn't:

- a program that calls C ([c.calls](../reference/20-builds.md#c.calls)), starts a process or reaches the network ends with `stilt-ref: internal error` and status 125, where it reaches the call;
- the interpreter's limits on the stack and the heap read OCaml's own measures, which JavaScript doesn't keep, so a program that recurses without end or runs out of memory isn't ended with status 134: it runs until the browser ends its worker, or Stop does.
