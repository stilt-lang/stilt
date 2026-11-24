# Formatter tests

The tests of `stilt fmt` ([syntax.formatter-tests](../../reference/03-syntax.md#syntax.formatter-tests)). Each is a pair of files: an input, `NAME.in.lt`, and the output that the canonical format of [syntax.format](../../reference/03-syntax.md#syntax.format) gives it, `NAME.out.lt`. An output is derived from the record by hand, never by running the formatter, and the first comment of each file says what the pair covers.

## What is checked

`just formatter`, and `just test` with it, checks that:

- each input formats to its output, byte for byte;
- each output formats to itself, so it is canonical;
- each output has its input's tree, as `parse --sexp` prints it ([syntax.tree-form](../../reference/03-syntax.md#syntax.tree-form)).

An output changes only in a January release ([versions.formatting-kept](../../reference/21-versions.md#versions.formatting-kept)): `compiler/stilt-fmt/tests/stability.rs` compares each with its text at the tag of the last release, unless `VERSION` names the next release and it is of January.

`just formatter` also formats the conformance suite, the guide's examples and generated programs, and checks that formatting each a second time changes nothing and that the formatted text keeps its tree.

## The pairs

| Pair | Covers |
| --- | --- |
| `indentation` | Two spaces per level and no aligned columns; tabs replaced ([lexical.whitespace](../../reference/02-lexical.md#lexical.whitespace)) |
| `braces` | A brace on the line of its construct: after `=`, `else`, `loop` and `catch` |
| `fallback_braces` | The block of a let-else and of an expression-level `else`, a chain of `else` that ends in one, and the braces of a `catch`, on the line where the expression before them ends; fallbacks that aren't blocks |
| `let_else_breaks` | A let-else whose expression breaks, after an argument list and after a chain of calls |
| `nested_catch` | A `catch` in a nested block, and one in an arm of another `catch` |
| `short_blocks` | A block of one statement on one line, and every other block one statement per line |
| `if_chains` | An `if` with an `else` on one line when it fits, and otherwise every branch on lines of its own, an empty one too |
| `if_chain_in_closure` | An `if`, `else if`, `else` chain in a closure's block, on one line and broken |
| `if_let_chain` | An `if let`, `else if let`, `else` chain that doesn't fit |
| `short_block_boundary` | A block on one line that reaches the 100th column, and one that would reach the 101st |
| `nested_blocks` | Blocks inside a block on one line, and inside a block too long for one |
| `arms` | `match` and block-form `catch` arms one per line, though they would fit on one, with no `;` or comma between them; a one-arm `catch` |
| `type_declarations` | Record and variant types on one line when they fit, at 100 and 101 columns, and otherwise one field or variant per line |
| `record_last_list` | A record type that doesn't fit, whose last field is a `List<T>`, with a comma after it whether the source has one or not |
| `record_last_function` | A record type that doesn't fit, whose last field is a function type, with a comma after it |
| `separators` | No `;`: statements, items and the header's clause each on a line of their own, and a statement that starts with `.` or `\|` in parentheses |
| `punning` | Punned fields in record literals and record patterns, and fields that can't be punned |
| `comments` | Comments that end a line and comments alone on theirs, doc comments, and blocks held on several lines by a comment |
| `blank_lines` | At most one blank line, none after an opening brace or before a closing one, and none at the start or the end of the file |
| `wrapped_arguments` | An argument list that fits, one that doesn't, a nested call that doesn't, and a list of one string |
| `wrapped_signatures` | A signature that fits, one that doesn't, and a variant payload that doesn't |
| `parameters_first` | A signature whose parameter list breaks before its return type, a function type, and a method of a trait without a body |
| `return_type_breaks` | A signature whose return type still doesn't fit once its parameter list breaks |
| `without_clauses` | A `without` clause on its signature's line when it fits, at the boundary of 100 columns, and otherwise on the next line, a level in: after a signature on one line, a hole body, a method in an impl and a broken parameter list ([lexical.continuation-lines](../../reference/02-lexical.md#lexical.continuation-lines)) |
| `wrapped_patterns` | Variant, record and list patterns and alternatives that don't fit, and an ending `..` |
| `wrapped_operators` | Binary operators, `else`, `>` and conditions that continue |
| `method_chains` | A chain on one line, one broken at each call, one whose last call's arguments break |
| `closure_blocks` | A call whose last argument is a closure with a block, on the line of its start or not |
| `closure_parameters` | Closure parameters marked `inout`, with and without a type |
| `if_let` | `if let`, with `else if let`, a record pattern in its head, and a head that breaks before its `else` |
| `negation` | A `-` apart from its number, which stays apart |
| `trailing_commas` | A trailing comma where a list breaks and nowhere else, and in a tuple of one element |
| `literal_list` | Lists of literals that fill their lines: negated numbers, a `-` apart from its number, strings and booleans, and one that fits |
| `mixed_list` | A list that mixes literals and a call, one element per line |
| `literal_rows` | A list of lists of literals, one row per line, and a row that fills its own lines |
| `commented_list` | A list of literals with a comment, one element per line |
| `module_header` | The module header's `without` clause on a line of its own, written on the path's line in the input, and imports in their order |
| `impls` | The members of impls and traits |
| `projections` | A projection's result `-> inout T`, and `yield e` as a statement ([projections.show](../../reference/13-modes.md#projections.show)) |
| `macro_declarations` | Macro declarations formatted token by token ([macros.formatting](../../reference/16-meta.md#macros.formatting)): badly spaced arms one per line, fragments, repetitions with `,`, `;` and no separator, a trailing block, a `pub` documented macro, `{ … }` templates laid out as blocks, a `;` after a template that ends with `*`, a `-` apart from its number, and an empty macro |
| `macro_uses` | Uses' groups kept as written ([macros.formatting](../../reference/16-meta.md#macros.formatting)): as expressions, statements and patterns, in an interpolation, with a path, with a trailing block, and groups on several lines whose indentation follows the code around them |
| `procedural_macros` | Procedural macros ([macros.formatting](../../reference/16-meta.md#macros.formatting)): a badly spaced `meta use` and macro declaration formatted as a function, a quote of each form whose contents are formatted as the form they hold, a block quote of two statements on lines of its own, splices and spreads written against their `$`, and a use in a type whose group stays as written |
| `when` | `when` with its handles separated by `, ` and its block laid out as every block is, and `without locks` ([shared.when](../../reference/14-tasks.md#shared.when) and [shared.locks](../../reference/14-tasks.md#shared.locks)) |
| `value_parameters` | Value parameters written `name: T` among generics, and value arguments with their `-` against the literal ([generics.value-parameters](../../reference/07-types.md#generics.value-parameters) and [generics.value-arguments](../../reference/07-types.md#generics.value-arguments)) |
| `staging` | `comptime` one space before the `if`, `match` or `for` it annotates, which is laid out as it is without it ([meta.staging-annotations](../../reference/16-meta.md#meta.staging-annotations)) |
| `bound_tests` | A bound test's `:` after its type parameter and one space, and its bounds joined by ` + `, as a generic's are, in an `if` and an `else if` ([meta.bound-tests](../../reference/16-meta.md#meta.bound-tests)) |
| `guide_example` | The example of the guide's "One syntax, one format" |

The choices for what [syntax.format](../../reference/03-syntax.md#syntax.format) leaves open, which `comments`, `blank_lines`, `fallback_braces`, `wrapped_arguments`, `wrapped_signatures`, `wrapped_patterns`, `wrapped_operators`, `method_chains`, `closure_blocks`, `trailing_commas`, `module_header`, `impls`, `macro_declarations` and `macro_uses` pin down, are listed in [`stilt-fmt`](../../compiler/stilt-fmt/src/lib.rs).
