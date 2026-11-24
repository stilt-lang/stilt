# 21. Versions and compatibility

A package's versions follow its API. This chapter defines a package's API, with the facts it holds and those it leaves out. It gives the change in the API that each new version must show in its number, and how a version is checked before a manifest pins it. It says how a program selects one version of each package from its manifests alone. It ends with what each release of the toolchain keeps of the programs that the release before it accepted. It relies on [Programs, modules and packages](04-programs.md) for manifests, fetching and editions, and on [Inferred facts and limits](15-facts.md) for the facts that the API holds.

## A package's API

<a id="versions.api"></a>
A package's **API** is what another package can use. It is what the package's check gives when the package is the root of a program, with the versions that its own manifest selects. It is the `pub` items of its modules ([program.visibility](04-programs.md#program.visibility)), with these parts:

- **Functions and methods:** each one's generics with their bounds, its parameters' modes and types, which parameters are `escaping`, its return type, its row, and its limitable facts ([versions.limitable-facts](#versions.limitable-facts)). The names of its generics and parameters, and the order of its row, are not part of it. A `pub` foreign function is part of the API with its signature ([c.unsafe-in-api](20-builds.md#c.unsafe-in-api)).
- **Types:** each one's parameters, and its fields or its variants, in order, with their types.
- **Traits:** each one's methods' signatures, which of them have a default body, and the limitable facts of each default body.
- **Constants:** each one's type.
- **Effects:** each one's type parameters, and its operations, in order, each with its parameters, its result and its row ([handlers.declaring-effect](12-effects.md#handlers.declaring-effect)).
- **Pattern macros:** each one's patterns, as a function's signature is, while its templates are its body ([macros.syntax-declarations](16-meta.md#macros.syntax-declarations)).
- **Procedural macros:** each one's signature, which decides which uses check, while what it expands to is its body ([macros.procedural-declarations](16-meta.md#macros.procedural-declarations)).
- **Trait impls** that another package can see ([program.visibility](04-programs.md#program.visibility)): each one's trait, type and bounds, and the limitable facts of each of its methods.
- **The package:** each module's tier ([program.module-tier](04-programs.md#program.module-tier)), whether the package's own code performs `io` ([packages.own-effects](04-programs.md#packages.own-effects)), and whether its own code holds an `unsafe` block ([c.unsafe-in-api](20-builds.md#c.unsafe-in-api)).

Checked by: the toolchain's tests of versions (`compiler/stilt-cli/tests/versions.rs` and `api_versions.rs`) and `compiler/stilt-pkg/src/api/tests.rs`, since only repositories have versions.

<a id="versions.limitable-facts"></a>
The **limitable facts** of a function, a method or a default body are the inferred facts that a `without` can name and that its callers inherit: `panic`, `overflow`, `alloc`, `div`, `copy`, `locks` and each of the eight capabilities ([facts.inferred-facts](15-facts.md#facts.inferred-facts)). `unsafe` and `foreign` are not limitable facts, because no caller inherits them. Whether a package's own code holds an `unsafe` block is part of its API instead ([versions.api](#versions.api)).

Checked by: the toolchain's tests of versions (`compiler/stilt-cli/tests/versions.rs`).

<a id="versions.facts-without-proofs"></a>
Each limitable fact in the API is the fact as it is when verification proves nothing ([facts.what-proofs-change](15-facts.md#facts.what-proofs-change)). It comes from these:

- the body's own operations that have it, a check proved or not;
- every `while` loop, ended or not;
- every self-call that doesn't descend ([facts.descending-self-calls](15-facts.md#facts.descending-self-calls)), shrinking or not;
- the items it names that have the fact so counted.

A function that a `without panic` or a `without div` limits has none of it, as everywhere ([facts.without](15-facts.md#facts.without)). What the limits accept, what `stilt show` prints and what a release build drops read the proofs. Only the API doesn't. So a version's number never depends on what verification proves.

Checked by: the toolchain's tests of versions (`compiler/stilt-cli/tests/versions.rs`), where a version whose function gains an index or a `while` loop that verification proves still needs a new major version, and one that moves a proved guard into a function of its own needs none.

<a id="versions.facts-in-api"></a>
The limitable facts are the only inferred facts of a function that the API holds. These aren't part of it:

- the parameters each function consumes ([values.consumed-parameters](05-values.md#values.consumed-parameters));
- a binding's modes ([modes.bindings-and-axes](13-modes.md#modes.bindings-and-axes));
- what a view reads and what a binding writes ([views.show](13-modes.md#views.show), [projections.show](13-modes.md#projections.show));
- in-place parameters ([facts.in-place-parameters](15-facts.md#facts.in-place-parameters));
- the operations that may make reference counts atomic ([par.atomic-sites](14-tasks.md#par.atomic-sites));
- the type parameters a function reflects on ([meta.reflects](16-meta.md#meta.reflects));
- the checks that verification proves ([facts.shown-proofs](15-facts.md#facts.shown-proofs));
- whether a function is exported to C ([c.exported-fact](20-builds.md#c.exported-fact));
- whether a type can form a cycle ([cycles.can-form-cycle](14-tasks.md#cycles.can-form-cycle));
- `unsafe` and `foreign`.

So a version whose functions gain or lose one of them needs no new version number.

Checked by: the toolchain's tests of versions (`compiler/stilt-cli/tests/versions.rs`): a change in which parameters a function consumes, and a function newly exported to C, need no new version.

<a id="versions.outside-api"></a>
Function bodies, what a procedural macro expands to, the values of constants, private items, doc comments and tests aren't part of a package's API.

Checked by: the toolchain's tests of versions (`compiler/stilt-cli/tests/versions.rs`) and `compiler/stilt-pkg/src/api/tests.rs`.

<a id="versions.edition"></a>
A package's edition is part of its manifest, not of its API ([editions.edition](04-programs.md#editions.edition)). A version that moves to a newer edition with no change to what another package can use needs only a new patch version.

Checked by: the toolchain's tests of versions (`compiler/stilt-cli/tests/versions.rs`).

## The change a version needs

<a id="versions.change-needed"></a>
From one version of a package to a later one, the change in its API needs:

- **A new major version** when anything another package uses can break:
  - a module, item, impl, member or trait method removed;
  - a signature, a type's fields or variants, a trait method's signature or an impl's bounds changed;
  - a method added to a trait, or a trait's method that loses its default body;
  - an operation added to an effect, removed or changed ([handlers.handler-literals](12-effects.md#handlers.handler-literals));
  - a function, method or default body that gains a limitable fact;
  - a module whose tier rises;
  - the package's own code performing `io` when it didn't, or holding an `unsafe` block when it held none.
- **A new minor version** for every other change in the API, as when:
  - a module, an item, an inherent member or an impl is added;
  - a function loses a limitable fact;
  - a trait's method gains a default body;
  - a module's tier falls;
  - the package's own code stops performing `io` or holding an `unsafe` block.
- **Nothing** when the API is the same, so a new patch version is enough.

A new major version raises the major number. A new minor version raises the minor number and keeps the major. A new patch version raises the patch number alone ([packages.versions](04-programs.md#packages.versions)). So no new patch version can give a function a limitable fact that a caller's `without` rules out.

Checked by: the toolchain's tests of versions (`compiler/stilt-cli/tests/versions.rs`), which classify each change.

<a id="versions.minor-changes-that-break"></a>
Some changes that need only a new minor version can break a dependent:

- an added impl can make a method call ambiguous ([traits.ambiguous-methods](11-traits.md#traits.ambiguous-methods));
- an added inherent member can clash with a method of a trait that a dependent implements for the type ([traits.method-resolution](11-traits.md#traits.method-resolution));
- an added item can hide a child module of its name ([program.child-modules](04-programs.md#program.child-modules)).

Every package of a program is checked against the versions selected for it ([packages.dependencies-with-errors](04-programs.md#packages.dependencies-with-errors)). So a dependent that such a change breaks fails at its check, never while it runs.

Checked by: the toolchain's tests of versions, a dependency that a selected version breaks through an added item (`compiler/stilt-cli/tests/versions.rs`).

<a id="versions.checked-versions"></a>
Before a version of a repository is written into a manifest ([packages.filling-in](04-programs.md#packages.filling-in)), its number is checked against the change in the API since the repository's previous version. The previous version is the repository's highest lower version that has no error. The number must change at least as [versions.change-needed](#versions.change-needed) asks. A version that changes less is E0604, *version that understates its API change*, at the entry's key, and isn't written. The error names the first change that needs more, by its address ([edits.paths](19-tools.md#edits.paths)), and offers the repository's highest version that passes. A repository's first version without errors needs no check.

A version that has an error, checked as a program of its own ([packages.dependencies-with-errors](04-programs.md#packages.dependencies-with-errors)), is never written. It is E0607, and the error offers the repository's highest version that has no error and passes.

Checked by: the toolchain's tests of versions (`compiler/stilt-cli/tests/versions.rs`), since only repositories have versions.

## Selecting versions

<a id="versions.selection"></a>
A program's packages are the root package and every package that the root's manifest names, directly or through the manifests of the packages it names. Each counts at every version that any of those manifests asks for, transitively. For each repository, the selected version is the highest version that any of these manifests asks for. Nothing else decides it: there is no lockfile, and two machines given the same manifests select the same versions. Two manifests that give one version two hashes are E0602 ([packages.checked-content](04-programs.md#packages.checked-content)).

Checked by: the toolchain's tests of versions, selection over a graph of several versions, the same on two machines (`compiler/stilt-cli/tests/versions.rs`).

<a id="versions.compatible-selections"></a>
The versions that the manifests ask of one repository must have one major number. If a manifest asks for version A of a repository and version B is selected, the API's change from A to B must need no new major version ([versions.change-needed](#versions.change-needed)). Otherwise the program has E0605, *versions that don't agree*, which names the first change that needs one, by its address. E0605, and E0602 for two hashes of one version, are reported at the first entry of the root's manifest through which the requests they are about arrive.

Checked by: the toolchain's tests of versions, two majors and a selection that removes what a lower request had (`compiler/stilt-cli/tests/versions.rs`).

## Across releases of the toolchain

<a id="versions.programs-kept"></a>
Every release of the toolchain accepts every program that the release before it accepted, with the same diagnostics, output and exit status. Each manifest selects the versions it did. A release may accept a program that the one before it rejected, as one whose limit a proof of verification lets it accept ([facts.what-proofs-change](15-facts.md#facts.what-proofs-change)).

Within an edition, the words that a feature needs are keywords already reserved ([lexical.reserved-words](02-lexical.md#lexical.reserved-words)) or contextual keywords, which stay names everywhere else ([lexical.contextual-keywords](02-lexical.md#lexical.contextual-keywords)). The names that the standard library holds beyond the prelude live in its modules, never in the prelude ([program.contents](04-programs.md#program.contents)). So no name in an accepted program changes what it refers to. Only an edition breaks a program ([editions.only-editions-break](04-programs.md#editions.only-editions-break)), and a package keeps its edition until its author moves it with `stilt migrate` ([editions.migrate](04-programs.md#editions.migrate)).

Checked by: the conformance suite, which keeps every approved test whose program has no error, with its expectations, and runs it under both implementations.

<a id="versions.checks-across-releases"></a>
A manifest records no release of the toolchain. So a version's check never depends on the release that wrote the version into a manifest. Every release checks a version, and a selection, against the API as this chapter defines it. A version whose number understates its change by these rules is E0604 where a manifest would write it. It is E0605 where a selection serves a manifest that asks for a version below it. Each names the function and the fact that it gains, whatever release wrote the version before. This is the one way in which a release rejects a program that the release before it accepted, and the version's repository tags a new major version for it.

Checked by: the toolchain's tests of versions, a selection across a gained fact (`compiler/stilt-cli/tests/versions.rs`).

<a id="versions.lost-proofs"></a>
The API reads no proof, so a new patch version can lose a proof that a caller's limit relies on. A dependency's function whose index a proof made safe, or whose loop a proof showed to end, can lose the proof. It does, for example, when its test moves into a function of its own. A caller limited by `without panic` or `without div` then fails to check, with no change to its own code. Its E0204 names the function and the line whose check isn't proved ([facts.closest-rule](15-facts.md#facts.closest-rule)). It is the one way a new patch version breaks a limit. A program meets such a version only when a manifest asks for it ([versions.selection](#versions.selection)).

Checked by: the toolchain's tests of versions, a version that moves a proved guard into a function of its own (`compiler/stilt-cli/tests/versions.rs`).

<a id="versions.machine-output"></a>
What the commands write for programs is kept across releases too. That is each record that `--json` writes ([Tools](19-tools.md)), with every field it holds and what the field means. A release may add fields, kinds of records and kinds of diagnostics, so a reader skips what it doesn't know. What the commands write for people, the text of diagnostics, help and reports, may change in any release. A program that reads it reads nothing this chapter keeps.

Checked by: the toolchain's tests and the suites of `tests/facts/`, `tests/holes/` and `tests/alternatives/`, which read these records by their fields' names and fail when a field they read changes.

<a id="versions.formatting-kept"></a>
What `stilt fmt` writes for a program changes only in a release of January, the one release of a year that may introduce an edition ([editions.only-editions-break](04-programs.md#editions.only-editions-break)). A release of any other month formats every program as the release before it did. So a program that a check of its format passes keeps passing until January.

Checked by: the formatter's tests, which compare each output of `tests/format/` with its text at the tag of the last release, unless `VERSION` names the next release and it is of January (`compiler/stilt-fmt/tests/stability.rs`).
