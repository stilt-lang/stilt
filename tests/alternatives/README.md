# Alternatives suite

Programs whose diagnostics have known admissible alternatives, which `stilt check --json` must list ([Goals](../../docs/design/goals.md), `admissible-alternatives`). Each list is derived by reasoning from the rules below and the records they cite, never by running an implementation. A program is a `.lt` file, or a directory that holds one, as in the conformance suite.

## What a diagnostic's alternatives are

A diagnostic's JSON has the list `alternatives`, at most 10, each an object with its `kind`, its `text` as code writes it, and for a binding its `type`. The rendering for people doesn't show them, since its message stays short (`short-messages`). Where the checker can't enumerate what would be admissible, the list is empty.

| Kind | Diagnostic | The alternatives |
| --- | --- | --- |
| `binding` | E0311, an expression whose type isn't the one its context expects | The bindings in scope where the expression is whose type is the expected type, in the order they are bound: the parameters, `self` first, then the bindings of the patterns whose scope holds the expression. Of two bindings of one name, only the later counts, since it hides the other. None when the expected type isn't known |
| `variant` | E0329, arms that don't cover every value ([patterns.guards-and-constants](../../reference/09-patterns.md#patterns.guards-and-constants)) | The first value the arms miss, as the message names it, then, for a type with constructors, the first value the arms miss of each other constructor, in the type's order |
| `effect` | E0502, an effect that the row of the function or the closure doesn't hold ([effects.missing-effects](../../reference/12-effects.md#effects.missing-effects)) | The elements of that row, as it writes them: `io`, its `raise`, then its row variables. None for a row that holds nothing |
| `name` | E0211, a name that doesn't resolve ([declarations.unknown-names](../../reference/10-declarations.md#declarations.unknown-names)) | The names close to it that the code may write there, nearest first |
| `effect` | E0211, a row variable that doesn't resolve | The row variables close to it that the signature declares, and `io`, nearest first |
| `field` | E0313, a field the record doesn't have | The record's fields close to it, nearest first |
| `method` | E0314, a member the type doesn't have | The type's member that another language's name stands for, as `len` for `length` or `push` for `append`, then the type's members close to it, nearest first |

A name is close to the one written as `closest-candidates` finds the names its fixes write: its edit distance from it, ignoring case, counting the swap of two neighbouring characters as one edit, is at most a third of the written name's length, at least 1, and less than the length of either. Of two at one distance, the one whose bytes sort first comes first. The two closest are also the diagnostic's fixes, unless the name is another language's for what Stilt writes otherwise, as `println` or `String`, whose fix writes the Stilt form.

## Annotations

A line with a diagnostic ends with `//~ CODE`, as `//~ E0329`, and the comment lines right after it each hold one `//~ alternative: KIND TEXT` of its list, in order: for a binding, `//~ alternative: binding name: Type`. A diagnostic without such lines lists none.

## What is checked

`just alternatives`, part of `just test` and of `just ci`, runs `stilt check --json` on each program, and checks that its diagnostics are exactly those the annotations mark, by line and code, each with exactly the alternatives they list. `just diagnostics` checks the shape of every snapshot program's list.
