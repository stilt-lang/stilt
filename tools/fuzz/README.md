# Fuzzing

`cargo fuzz` targets for the compiler's front end, its language server and the reader of the
packages it fetches: each takes any bytes and must not panic.

| Target | What it checks |
| --- | --- |
| `parse` | The parser gives a tree for any bytes, and the tree's text is the input when it is UTF-8 |
| `format` | The formatter never panics, and formatting its output changes nothing |
| `check` | The checks of a program of one file never panic. One query database holds the standard library for every input, and each input replaces the file's bytes, so the checks run incrementally, as they do while a person types |
| `lsp` | The language server answers any session of an editor's without panicking. The input gives a document's text and the messages, framed as an editor frames them: buffers opened, changed and closed, and requests at positions past the last line, inside a character, or not numbers at all. A backend of `lsp/fake.rs` answers from the input too, with offsets past the end or inside a character, spans that end before they start, and lists empty or long. Each request gets one answer, every message the server writes is framed JSON, and only a frame no editor writes, which a session may end with, fails it |
| `pack` | The reader of git's packs, which `stilt` fetches packages as, never panics, never allocates the sizes a pack declares, and ends on a chain of deltas that loops. The input is read as a pack a server sends, and, split at the length its first two bytes give, as a pack index of version 2 and its pack. Corrupt bytes give an error |

The crate is a workspace of its own, since `cargo fuzz` builds with a nightly compiler. The
conformance suite and the examples make a good first corpus; its `lexical/nesting_*` tests start
the fuzzer at the limit of nesting and one level past it, which mutations rarely reach:

```sh
CARGO_TARGET_DIR=target/fuzz cargo +nightly fuzz run --fuzz-dir tools/fuzz -O -s none check \
    tools/fuzz/corpus/check conformance examples -- -fork=8 -max_total_time=600
```

The `lsp` target needs no corpus to start from, and `-a` adds the checks of overflow that `-O`
leaves out, which find offsets at the last byte there can be:

```sh
CARGO_TARGET_DIR=target/fuzz cargo +nightly fuzz run --fuzz-dir tools/fuzz -O -a -s none lsp \
    tools/fuzz/corpus/lsp -- -max_total_time=600
```

The build goes under `target/`, as every other does. The new inputs go to `corpus/`, and any
input that panics or hangs to `artifacts/`; neither is tracked. A hang shows as a timeout.
The sanitizer is off (`-s none`): the front end's crates hold no `unsafe` code, and on macOS the
linker rejects the initializers that `salsa` registers when AddressSanitizer is on.
