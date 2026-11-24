# Grammar generator in Stilt

A port of `stilt-grammar generate` to Stilt: it reads the `ebnf` blocks of `reference/03-syntax.md` and the table of tokens of `reference/02-lexical.md`, and writes `stilt.gbnf` and `stilt.lark`, byte for byte what the Rust program writes. Run it from the repository root with `stilt run tools/grammar/stilt --out DIR` (the default is `reference/grammar`), or build it with `stilt build tools/grammar/stilt -o generate`. `stilt test tools/grammar/stilt` runs its examples and tests.
