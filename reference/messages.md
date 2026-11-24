# How diagnostics are written

The registry, [`errors.toml`](errors.toml), says which code each mistake gets and where it is reported, and the Reference's chapters define the rule behind each code. This page says how the words around a code are written: the compiler's message, labels and fixes, which [`tests/diagnostics/`](../tests/diagnostics/) snapshots, and the registry's help and examples, which the [error index](../docs/errors/) and `stilt show CODE` print. Implementations are judged on codes, files and lines alone ([conformance.diagnostic-text](01-conformance.md#conformance.diagnostic-text)), so this page binds the compiler's words, not the language.

A diagnostic is rendered as a title, the message, the user's code with its labelled spans, the help, and at most two fixes, each shown in the code:

```text
── MODIFYING WHAT CAN'T BE MODIFIED ────────────────────── main.lt:3:21  [E0403]

`sum` can't be modified here; only `var` bindings and `inout` parameters of this
body can:

  3 │   for p in prices { sum += p }
    │                     ^^^

A `let` binding or a parameter never changes. Declare the binding with `var`, or
copy the parameter into one, as `var x = x`; a closure can't change what it
captures.

To fix it, declare `sum` with `var`:

  2 │   var sum = 0
    │   ~~~
```

## Principles

1. **Written for the person who made the mistake.** A message names what is wrong in the reader's terms: their names, their types, their code. No message or help cites a file of the repository, a paragraph ID, or the words of how the language is specified, such as its grammar's notation or its checking phases.
2. **One mistake, one diagnostic.** Several symptoms of one mistake are one diagnostic with several labels, which [Programs with errors](18-errors.md) decides for every implementation.
3. **The fix is the usual fix.** A fix is shown as the edited code. When there are two, the more common comes first, and applying either removes the diagnostic and causes no other. A fix never discards a value that the code most likely meant to keep.
4. **Teach the Stilt form.** When the mistake is another language's syntax or idiom, such as `let mut`, `&str`, `null` or `->` in a `match` arm, the message says what Stilt writes instead.
5. **Say what was expected.** A syntax error names what the code needed where it breaks, a form such as an expression or a token such as `)`, and what it found there, as in ``expected `,` or `)`, found `x` ``.
6. **Short by default.** The message and its labels stay under 40 tokens. The help is one or two sentences, and `stilt show CODE` and the error index give the long form, with examples.
7. **The help is help, not law.** The paragraph under the message says what to do and, in plain words, why Stilt works this way, for the most common case of the code; a message whose case is different gives its own help. The rule itself is one step away: `stilt show CODE` prints it, and the error index links it.

## What is checked

- `just diagnostics` checks that each snapshot program reports exactly its one diagnostic, renders byte for byte as its reviewed snapshot, and that each fix it offers, applied, leaves no diagnostic.
- `just diagnostics-tokens`, part of `just ci`, counts the tokens of each message and its labels.
- `cargo run -p stilt-registry`, which `just diagnostics` and `just coverage` run with `--check`, refuses a help that cites a paragraph, names a file of the repository or uses the words of the specification, and a code whose mistake one file shows without an example.
- `just guide` checks every example of the registry: the program with the mistake gets the code at its line, and the program fixed gets no diagnostic.
