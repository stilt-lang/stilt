# Conformance tests

The conformance suite is the Reference's executable form. Each test is a `.lt` file, or a directory holding `main.lt`, with `//~` annotations that state what an implementation must do. [Conformance](../reference/01-conformance.md) defines the annotations ([conformance.annotations](../reference/01-conformance.md#conformance.annotations)), the three kinds of test ([conformance.kinds-of-test](../reference/01-conformance.md#conformance.kinds-of-test)) and the environment tests run in ([conformance.environment](../reference/01-conformance.md#conformance.environment)).

A directory test that is a package holds its manifest, `stilt.toml`, and its dependencies as path dependencies inside it, so that no test needs the network ([conformance.directory-tests](../reference/01-conformance.md#conformance.directory-tests)). A manifest's diagnostics are expected by an annotation in a TOML comment, as in `csv = { path = "deps/csv" } # //~ ERROR E0608`, and the runner reads `stilt.toml` files for annotations as well as `.lt` files ([conformance.inline-annotations](../reference/01-conformance.md#conformance.inline-annotations)).

Tests are grouped in one folder per area of the language, except `ported/`. It holds programs ported from Rosetta Code, whose output the task fixes, and translations of the test programs of other languages about effect handlers and value semantics, whose expectations the original tests fix: Koka's (Apache-2.0), Effekt's (MIT), Swift's (Apache-2.0) and Hylo's (Apache-2.0), whose notices are in [NOTICE](../NOTICE). Where a test lives never changes what it expects.

Each test cites the paragraphs of the Reference it covers in a `//~ rule:` annotation, by paragraph ID, such as `numbers.integer-panics` ([conformance.rule-citations](../reference/01-conformance.md#conformance.rule-citations)), and each of those paragraphs links the test in its `Tests:` line. `just coverage` reports which paragraphs the tests cite and which codes of the registry they expect, and `just coverage conformance/_pending` counts the drafts as well.

Drafts go in `_pending/<area>/`. The runner skips every entry whose name starts with `_`, so drafts don't count until they are approved. `just approve` moves each draft here once every ID it cites is a paragraph of the Reference, and holds back the rest.

Run the suite against the reference interpreter with:

```sh
just conformance
```
