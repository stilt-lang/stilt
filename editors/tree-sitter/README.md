# tree-sitter

The grammar of Stilt for [tree-sitter](https://tree-sitter.github.io/), which editors such as Neovim, Helix and Zed read to highlight, fold and select code. `just grammar-generate` writes it from the Reference, and `just grammar` checks that it is current and that it parses every program of the conformance suite without a syntax error, and the generated programs.

| File | Contents |
| --- | --- |
| `grammar.js` | The productions of [`reference/03-syntax.md`](../../reference/03-syntax.md), with the heads of [expressions.heads](../../reference/08-expressions.md#expressions.heads), the levels of [expressions.precedence](../../reference/08-expressions.md#expressions.precedence) and the lexemes of [lexical.tokens](../../reference/02-lexical.md#lexical.tokens). Generated |
| `src/scanner.c` | The external scanner, which reads a newline as a separator where the grammar accepts one and the next line doesn't continue the line ([lexical.terminator-insertion](../../reference/02-lexical.md#lexical.terminator-insertion) and [lexical.continuation-lines](../../reference/02-lexical.md#lexical.continuation-lines)). Generated |
| `queries/highlights.scm` | The highlighting queries, with tree-sitter's common capture names, generated from the grammar's words and tokens; `just grammar` runs them over the suite's programs |
| `tree-sitter.json` | The grammar's name, scope and file type |

The parser, `src/parser.c`, is not kept here: `tree-sitter generate`, run in this folder, writes it from `grammar.js`. The productions are ambiguous on their own ([syntax.ambiguities](../../reference/03-syntax.md#syntax.ambiguities)), so the grammar names the sets of rules between which the parser keeps both readings until the text settles them; when a change of the productions needs another, `tree-sitter generate` names it, and it goes into `CONFLICTS` in [`tools/grammar/src/treesitter.rs`](../../tools/grammar/src/treesitter.rs).

The grammar reads a doc comment as a comment, and accepts more than the language in the places where [syntax.published-grammars.loosening](../../reference/03-syntax.md#syntax.published-grammars.loosening) loosens the published grammars, and where a keyword stands for a name.
