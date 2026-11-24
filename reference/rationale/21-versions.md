# Rationale: Versions and compatibility

A version number is a promise to the packages that depend on it. A new patch version breaks nothing, a new minor version only adds, and a new major version may break. Cargo and npm leave the promise to the author, who tags a number that nothing checks. Stilt computes what each new version needs from the change in the package's API. It checks the number before a manifest pins it, and again wherever a program uses a version other than the one a manifest asked for.

## A package's API

The API is what another package can use ([versions.api](../21-versions.md#versions.api)): signatures, types, traits and impls, each module's tier, and what the package's own code does to the world. It also holds each function's limitable facts ([versions.limitable-facts](../21-versions.md#versions.limitable-facts)). A caller limited by `without panic`, `without div` or `without clock` relies on its callee not having the fact. It breaks when the callee gains the fact, with no change to its own code. A limit that a dependency's patch could break would promise nothing.

The facts that no `without` names stay out ([versions.facts-in-api](../21-versions.md#versions.facts-in-api)). They say how a function's code runs, such as which parameters it consumes, the modes of its bindings or the operations that may make its reference counts atomic. Callers can't rely on them, and can't observe them. Holding them in the API is rejected: an edit of a body would need a new minor version, and two compilers that infer them differently would ask for different versions. Exporting a function to C changes nothing either, because a package's callers are Stilt code.

The API reads `panic` and `div` as they are when verification proves nothing ([versions.facts-without-proofs](../21-versions.md#versions.facts-without-proofs)). Holding them with their proofs is rejected. A proof can come or go with an edit that means the same, as when a guard moves into a function of its own. It can also come or go with a toolchain that proves more or less. Versions' numbers would then move with no change to what any caller can use. A function that a proof makes unable to panic can't say so in its number. That breaks no caller, because losing a fact needs only a new minor version.

The cost is that a new patch version can lose a proof that a caller's limit relied on ([versions.lost-proofs](../21-versions.md#versions.lost-proofs)), the one way a patch breaks a limit. A version arrives only when a manifest asks for it, so a program that changes no manifest never meets one. The error then names the function and the line whose check isn't proved.

A package's edition is part of its manifest, not of its API ([versions.edition](../21-versions.md#versions.edition)). An edition changes how the package's own files read, never what another package can use, so moving to a newer edition needs no new number.

## The change a version needs

The rules of [versions.change-needed](../21-versions.md#versions.change-needed) follow one test: whether a dependent that checked against the earlier version can fail against the later one. Removing or changing anything it uses can break it. So can a fact it inherits, a tier that rises, or new effects or `unsafe` code that its manifest must then grant. An operation added to an effect breaks every handler of the effect, because a handler implements every operation ([handlers.handler-literals](../12-effects.md#handlers.handler-literals)).

Adding can't break a dependent, with three exceptions ([versions.minor-changes-that-break](../21-versions.md#versions.minor-changes-that-break)). An added impl can make a method call ambiguous. An added inherent member can clash with a method of a trait that a dependent implements. An added item can hide a child module. They count as minor, as Rust's guidelines count added impls, because counting every addition as major would make almost every release major. Every package of a program is checked against the versions selected for it, so a dependent that breaks fails at its check, never at run time.

Versions declared in the dependency's own manifest, as a `[package] version` key, are rejected. A declared number only promises compatibility, while a tag checked against the API ([versions.checked-versions](../21-versions.md#versions.checked-versions)) shows it. Elm computes versions in the same spirit. Tags taken on trust are rejected too: a wrong number would break dependents without a word. The API is checked at the two places where a wrong number hurts: when a version is pinned, and when a selection serves a request for a lower one.

## Selecting versions

A program holds one version of each package, the highest that any of its manifests asks for ([versions.selection](../21-versions.md#versions.selection)). This is minimal version selection, as Go's modules use it. Selecting the newest compatible version, as Cargo does, is rejected: a new release upstream would change a program that nobody edited. Minimal version selection changes a program only when a manifest changes. A lockfile, as Cargo and npm keep one, is rejected too. The manifests already give the same versions on every machine, so a second file would only restate them, and the two could disagree.

Each manifest that asks for a lower version gets one whose API must keep everything it had ([versions.compatible-selections](../21-versions.md#versions.compatible-selections)). So each compatible version is checked where it is used, and its author doesn't have to promise it. Several major versions of one package in a program, under different paths, as Go's semantic import versioning allows, are rejected. A program with two majors would name one module two ways, which the rule that every name has one home forbids.

## Across releases of the toolchain

Every release keeps every program that the release before it accepted ([versions.programs-kept](../21-versions.md#versions.programs-kept)). The words that new features need are reserved ahead of them or contextual. New names of the standard library live in its modules, never in the prelude. So no name in an accepted program changes what it refers to. A program that needs a breaking change gets it only through an edition, which its author chooses to move to.

A manifest records no release, so every release checks every version against the API as the current rules define it ([versions.checks-across-releases](../21-versions.md#versions.checks-across-releases)). Reading a fact only between two versions written under a release that infers it is rejected. A version's check would then depend on the release that wrote it, which nothing records. Storing each version's facts as the release that wrote it inferred them is rejected too. Nothing is stored beside a manifest, and two machines would need the same releases to agree.

The cost is that a version whose number an earlier toolchain accepted can be found to understate its change. That happens when the API holds a fact that the earlier toolchain didn't infer. Its repository then tags a new major version. That is the one way a release can reject a program that the release before it accepted.
