# Zed

The extension that brings Stilt to [Zed](https://zed.dev): it highlights `.lt` files with the tree-sitter grammar of [`../tree-sitter/`](../tree-sitter/), and runs the language server, `stilt lsp`, which gives Zed its diagnostics with their fixes, completion, hovers, navigation, formatting, semantic tokens and inlay hints, the inferred facts among them. Zed shows inlay hints once `"inlay_hints": { "enabled": true }` is in its settings.

The server is the `stilt` on the `PATH` of the project's shell, which [`install.sh`](../../install.sh) puts in `~/.stilt/bin`; without one, Zed's log of the server says so.

| File | Contents |
| --- | --- |
| `extension.toml` | The extension's name and version, the grammar, at a commit of this repository, and the language server |
| `languages/stilt/config.toml` | The language: its files, its comments, its brackets and its indentation |
| `languages/stilt/highlights.scm` | The highlighting queries, with the capture names of Zed's themes. Generated from the grammar, as the queries of [`../tree-sitter/queries/`](../tree-sitter/queries/) are, by `just grammar-generate` |
| `languages/stilt/brackets.scm`, `indents.scm`, `outline.scm` | The pairs of brackets, what is indented, and the outline: the functions, types, traits, impls, constants, effects, macros and tests, with their members |
| `src/lib.rs` | The command of the language server, `stilt lsp`, found on the `PATH` |
| `rust-toolchain.toml` | The repository's toolchain, with the target `wasm32-wasip2` that Zed builds extensions for |
| `LICENSE-MIT`, `LICENSE-APACHE` | Links to the repository's licences, which Zed's registry reads in the extension's folder |

The crate is a workspace of its own, which the root `Cargo.toml` excludes. `cargo build --release --target wasm32-wasip2` in this folder builds it as Zed does, and `just grammar` runs each query over the suite's programs.

The grammar's `rev` in `extension.toml` is a commit of this repository; each release sets it to the tagged commit ([RELEASING.md](../../RELEASING.md)). Zed checks that commit out and compiles the grammar's `src/parser.c` and `src/scanner.c` there, as Helix does.

To try it, run `zed: install dev extension` from Zed's command palette and choose this folder: Zed builds the crate and the grammar, and opens `.lt` files with them.
