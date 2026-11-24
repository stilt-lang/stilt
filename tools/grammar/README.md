# Grammar

`stilt-grammar` publishes the grammar of [`reference/03-syntax.md`](../../reference/03-syntax.md) in the two forms that constrained decoders read (goal `published-grammar`), and checks them. It writes too the files that restate the words and tokens of [`reference/02-lexical.md`](../../reference/02-lexical.md) for the lexers and the editors, so that the Reference is their one source.

| Command | Does |
| --- | --- |
| `generate` | Writes [`reference/grammar/stilt.gbnf`](../../reference/grammar/stilt.gbnf), the GBNF that llama.cpp reads, and [`stilt.lark`](../../reference/grammar/stilt.lark), the Lark-like format of llguidance. With `--check` it writes nothing, and fails if the files differ from what it generates. `just grammar-generate` runs it |
| `sources` | Writes the files of [Words and tokens](#words-and-tokens) from the Reference. With `--check` it writes nothing, and fails if one differs from what it generates. `just grammar-generate` runs it |
| `programs` | Prints the paths of the conformance suite's programs without a syntax error, and of the programs of directories, which `just grammar` parses with the tree-sitter grammar |
| `check` | Feeds the bytes of programs to grammars in llguidance's Lark-like format, byte by byte, and fails at the first byte that no continuation accepts, or at the end of a program that the grammar can't finish. A byte-level pass over a whole file covers all its prefixes |

[`stilt/`](stilt/) holds `generate` written in Stilt, which `just ports` checks writes both forms byte for byte as this one does (goal `shipped-programs`).

`just grammar` runs `generate --check` and `sources --check`, converts the GBNF, then runs `check` on both forms against the conformance suite's programs without a syntax error (those whose files hold no code of the syntax phase), the guide's examples (`stilt` blocks without `fragment` or a syntax error) and the programs that `just generated` makes. The programs are checked on all cores. Then, when npm is installed, the recipe installs the tree-sitter CLI, pinned, into `target/tree-sitter`, generates the tree-sitter parser there, and parses the same programs but the guide's with it, failing at any syntax error. The recipe takes about 30 s.

## One source

The generator reads the `ebnf` blocks of `reference/03-syntax.md`, so a production changed there changes both forms, and the check fails until `just grammar-generate` has written them. The tokens that a `TOKEN` of [macros.patterns](../../reference/16-meta.md#macros.patterns) may be come from the table of [lexical.tokens](../../reference/02-lexical.md#lexical.tokens). The lexical structure of [lexical.tokens](../../reference/02-lexical.md#lexical.tokens), [lexical.terminator-insertion](../../reference/02-lexical.md#lexical.terminator-insertion) and [lexical.interpolation](../../reference/02-lexical.md#lexical.interpolation) (tokens, comments, newlines as separators, interpolation) is written once in `src/lexicon.rs` as regular expressions, and printed in each syntax.

| File | Concern |
| --- | --- |
| `src/ebnf.rs` | Reads the rules of the `ebnf` blocks |
| `src/expand.rs` | Expands `list`, `list1` and `arms`, and names the classes of tokens |
| `src/heads.rs` | Derives the heads of [expressions.heads](../../reference/08-expressions.md#expressions.heads), as `reference/03-syntax.md` describes them |
| `src/recursion.rs` | Removes left recursion, which GBNF can't express |
| `src/shape.rs` | Separators, the `TOKEN` of [macros.patterns](../../reference/16-meta.md#macros.patterns), with the interpolated strings whose splices hold what the rule that reads it holds, the start rule, the rules reachable from it, where newlines may stand, and the choices between tokens that a lexer reads as one lexeme |
| `src/lexicon.rs` | The lexemes of [lexical.tokens](../../reference/02-lexical.md#lexical.tokens) as regular expressions |
| `src/lexical.rs` | Reads the lists of the lexical chapter and the limits of the production `limit`, and checks that every spelling the productions quote is a keyword or a token |
| `src/sources.rs`, `src/rust.rs`, `src/ocaml.rs`, `src/textmate.rs`, `src/treesitter.rs`, `src/treesitter_scanner.rs`, `src/facts.rs`, `src/names.rs` | The files of [Words and tokens](#words-and-tokens), and the names each implementation gives the kinds of its tokens |
| `src/gbnf.rs`, `src/lark.rs`, `src/print.rs` | The two output syntaxes |
| `src/corpus.rs`, `src/check.rs` | The programs, and the check with llguidance |

## Words and tokens

The keywords of [lexical.keywords](../../reference/02-lexical.md#lexical.keywords), the words of [lexical.reserved-words](../../reference/02-lexical.md#lexical.reserved-words), the contextual keywords of [lexical.contextual-keywords](../../reference/02-lexical.md#lexical.contextual-keywords), the primitive type names of [lexical.primitive-type-names](../../reference/02-lexical.md#lexical.primitive-type-names), the tokens of [lexical.tokens](../../reference/02-lexical.md#lexical.tokens) and the limits of the production `limit` are written once, in the Reference, as are the facts of the table of [facts.inferred-facts](../../reference/15-facts.md#facts.inferred-facts). `sources` writes them into the files that restate them, each of which says so in its header, but the manifest's schema, which says so in the description of its `may`:

| File | Holds |
| --- | --- |
| [`compiler/stilt-syntax/src/lexer/lexicon.rs`](../../compiler/stilt-syntax/src/lexer/lexicon.rs) | The compiler's tables of keywords, contextual keywords, limits, tokens longest first and primitive type names, each with its `SyntaxKind` |
| [`interpreter/lib/lexical/lexicon.ml`](../../interpreter/lib/lexical/lexicon.ml) | The same tables for the reference interpreter, each with its `Token_type.t` |
| [`editors/vscode/syntaxes/stilt.tmLanguage.json`](../../editors/vscode/syntaxes/stilt.tmLanguage.json) | The TextMate grammar: its template, [`stilt.tmLanguage.template.json`](../../editors/vscode/syntaxes/stilt.tmLanguage.template.json), with each placeholder replaced by the words or tokens it names (`src/textmate.rs`) |
| [`compiler/stilt-ide/src/editor/tokens/control.rs`](../../compiler/stilt-ide/src/editor/tokens/control.rs) | The keywords that direct control, which the language server's semantic tokens mark as the TextMate grammar colors them |
| [`compiler/stilt-ide/src/show/facts/table.rs`](../../compiler/stilt-ide/src/show/facts/table.rs) | The facts of the table of [facts.inferred-facts](../../reference/15-facts.md#facts.inferred-facts), each with what it says of a function and the paragraphs of its sites, from which `stilt show` and the language server's hints say what each fact means, and in whose order `show` prints them (`src/facts.rs`) |
| [`editors/vscode/schemas/stilt.toml.json`](../../editors/vscode/schemas/stilt.toml.json) | The strings that a dependency's `may` takes: `io`, the capabilities of [facts.capabilities](../../reference/15-facts.md#facts.capabilities) in its order, and `unsafe`, each with a description of its own, which only a person writes and `sources` counts (`src/copies.rs`) |
| [`editors/tree-sitter/grammar.js`](../../editors/tree-sitter/grammar.js), [`src/scanner.c`](../../editors/tree-sitter/src/scanner.c) | The tree-sitter grammar: the productions with their heads, the levels of [expressions.precedence](../../reference/08-expressions.md#expressions.precedence), the lexemes, and the scanner that reads a newline as a separator (`src/treesitter.rs`, `src/treesitter_scanner.rs`; [`editors/tree-sitter/README.md`](../../editors/tree-sitter/README.md)) |

Each implementation names the kind of a token from its spelling: a keyword's is its word in capitals, and a token's joins the names of its characters (`src/names.rs`). A token whose character has no name there fails the generator, which says so. The editors color some words apart, those that direct control, declare, bind or are reserved, by the classes of `src/textmate.rs`; each word of a class must be one the Reference lists, and the keywords that no class holds are colored as keywords.

So a keyword or a token added to the Reference reaches both lexers and the editor once `just grammar-generate` has run; the implementations then fail to build until their parsers have a kind for it.

Some lists of the Reference are restated in prose, which only a person writes, and `sources` checks them, generating or not (`src/copies.rs`): the limits that the table of [Programs](../../docs/guide/08-programs.md) names, in the order of the facts; each fact of [facts.inferred-facts](../../reference/15-facts.md#facts.inferred-facts) in the table of [what is inferred](../../docs/design/inferred-facts.md#what-is-inferred); the capabilities that the guide and the design documents list; and the implicit effects and the limits that the [design sketch](../../docs/design/design-sketch.md) lists. A list that differs fails with the list the Reference gives.

The forms accept more than the language in a few places, which [syntax.published-grammars.loosening](../../reference/03-syntax.md#syntax.published-grammars.loosening) lists, each with the rule it loosens.

## How the check reads GBNF

No maintained implementation reads GBNF from Rust. llguidance, the implementation that checks the Lark form, ships a converter from GBNF to its own format, in its Python package. `gbnf_to_lark.py` runs it (through `uv`, as the other scripts of the repository), and `check` reads the result. So the GBNF is checked as llguidance reads it after conversion, not as llama.cpp reads it. Two properties of the GBNF serve the converter, which reads a rule that holds only characters as one lexeme:

- `blanks` is a recursive rule, so that every token and every rule that holds one stays a rule;
- each alternative of a rule ends the line with `|`, as llama.cpp requires.

The `llguidance` crate is a dependency of this crate only, never of the compiler.

## Why the Lark form starts with `LEAD`

llguidance doesn't skip what `%ignore` names before the first token, so the form begins with a lexeme for the blanks and comments that may precede it. A float with a fraction is an integer, a `.` and a fraction, because llguidance's lexer commits to the longest lexeme, and `0..n` would otherwise read as the start of a float.
