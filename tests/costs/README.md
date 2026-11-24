# Costs suite

Programs whose release-build costs are known from the records, which `stilt show --release` must report ([builds.performance-report](../../reference/20-builds.md#builds.performance-report); [Goals](../../docs/design/goals.md), `no-hidden-costs`). Each function's first line carries what the release build compiles for it, and each line of a call left on a dictionary or of a check carries it, derived from the records by reasoning, never by running an implementation:

- the instantiations that the program's `main` reaches, each a list of type and value arguments, one function for a function without parameters, none for a function that nothing reaches, and the code with dictionaries of a recursive group that calls itself at a growing type and of a function used only as a polymorphic value ([builds.specialization](../../reference/20-builds.md#builds.specialization) and [builds.what-stays-generic](../../reference/20-builds.md#builds.what-stays-generic));
- each call left on a dictionary, with its reason: polymorphic recursion, or a call of a polymorphic argument ([builds.what-stays-generic](../../reference/20-builds.md#builds.what-stays-generic); [polymorphism.arguments](../../reference/07-types.md#polymorphism.arguments));
- the checks of an index, a key, a divisor and an overflow that verification proves, which the release build drops, and those it keeps ([facts.proved-indexes](../../reference/15-facts.md#facts.proved-indexes), [facts.proved-divisions](../../reference/15-facts.md#facts.proved-divisions), [facts.map-keys](../../reference/15-facts.md#facts.map-keys), [facts.proved-overflow](../../reference/15-facts.md#facts.proved-overflow), [facts.range-loops](../../reference/15-facts.md#facts.range-loops), [facts.guards](../../reference/15-facts.md#facts.guards), [facts.divisors](../../reference/15-facts.md#facts.divisors) and [facts.keys](../../reference/15-facts.md#facts.keys));
- the lines of the program's profile, `NAME.profile` beside it, whose bodies changed since they were counted, which the release build drops ([builds.profile-use](../../reference/20-builds.md#builds.profile-use)): here every line, since its hash `0000` is no body's.

Where the counting of references falls is the compiler's own ([modes.copies](../../reference/13-modes.md#modes.copies) and [modes.shared-writes](../../reference/13-modes.md#modes.shared-writes)), so each program's counts are pinned as a snapshot, `NAME.references`, a line for each function: its address and, for each line of its code that counts references, the operations and the copies among them. As a diagnostic's rendering is, a snapshot is reviewed before it is accepted: [`costs.rs`](../../compiler/stilt-cli/tests/costs.rs) drafts each one that is missing or differs into `_pending/` with `cargo test -p stilt-cli --test costs -- --ignored draft`, and a program passes while its approved snapshot is current, or while it has none and its draft is. A reviewed draft is accepted by moving it up.

A program is a `.lt` file, or a directory that holds one, as in the conformance suite.

## Annotations

The expected costs are annotations in the form of the conformance suite's ([conformance.annotations](../../reference/01-conformance.md#conformance.annotations) and [conformance.inline-annotations](../../reference/01-conformance.md#conformance.inline-annotations)), so each sits beside the line it describes. A function's entry is on the line of its name; `FOR` and `DICTIONARIES` with arguments end their annotation.

| Annotation | Expects |
| --- | --- |
| `FOR T = i64 \| T = str`, on a function's first line | The release build compiles the function once for each list of arguments, its parameters' in order: `Self` for a trait's default method, then its impl's, then its own, a value parameter's as its number, as in `n = 3`, and a list of several as in `A = i64, B = str` |
| `ONCE`, on a function's first line | The function has no type or value parameter, and the release build compiles it once |
| `UNREACHED`, on a function's first line | No root reaches the function, and the release build compiles nothing for it |
| `DICTIONARIES T = i64`, on a function's first line | The function keeps its dictionaries: compiled once, called with these arguments from outside its group, or, with no arguments, used only as a polymorphic value |
| `DICTIONARY recursion` or `DICTIONARY argument`, at the end of a line | A call on the line is left on a dictionary: one that passes the function's own type parameters' dictionaries in a group that keeps them, or a call of a polymorphic argument |
| `PROVED bounds`, `PROVED divide-by-zero`, `PROVED missing-key` or `PROVED overflow`, at the end of a line | Verification proves that a check on the line can't fail, and the release build drops it |
| `KEPT bounds`, `KEPT divide-by-zero`, `KEPT missing-key` or `KEPT overflow`, at the end of a line | Verification doesn't prove a check on the line, and the release build keeps it |
