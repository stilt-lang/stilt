# Glossary

The terms that more than one chapter uses, each with the paragraph that defines it. Where a word has two meanings, as *part* and *namespace* do, each has its own entry.

**Adapter.** A method of `Iter<T>` that returns an iterator over the elements of others, computed only as they are consumed. [views.adapters](13-modes.md#views.adapters)

**Annotation.** A line comment of a conformance test that starts with `//~` and states what an implementation must give for the test. [conformance.annotations](01-conformance.md#conformance.annotations)

**Anonymous record type.** A structural record type written `{ f: T, … }`, the same as any other with the same fields and types, in any order. [records.anonymous-types](07-types.md#records.anonymous-types)

**API.** What another package can use of a package: the `pub` items of its modules with their signatures and limitable facts, which its version numbers follow. [versions.api](21-versions.md#versions.api)

**Array.** A value of the native type `Array<T, n>`, a sequence of exactly `n` values of type `T`. [generics.arrays](07-types.md#generics.arrays)

**Body.** A function body, a test body, a doc example, a property or a constant's initializer: the unit that type inference, the phases of checking and verification each read alone. [errors.phases](18-errors.md#errors.phases)

**Bound.** A trait, or a record's fields, that a type parameter's types must implement or have, written as `T: Ord + Show`. [traits.bounds](11-traits.md#traits.bounds)

**Bound test.** The condition `T: B` of an `if`, true when the type that instantiates `T` implements `B`. [meta.bound-tests](16-meta.md#meta.bound-tests)

**Break.** What a part of a file with a syntax error does at its first grammar error, or at the lexical error that ends it, after which reading resumes at the next declaration. [errors.breaks](18-errors.md#errors.breaks)

**Canonical text.** The text that `stilt fmt` writes for a declaration or a body standing alone, which an edit's hash covers. [edits.canonical-text](19-tools.md#edits.canonical-text)

**Capability.** One of eight inferred facts below `io`, `fs`, `net`, `clock`, `env`, `console`, `rand`, `spawn` and `exec`, which says which part of the world a function reaches. [facts.capabilities](15-facts.md#facts.capabilities)

**Catch-all.** An arm of a `catch` without a guard whose pattern is `_` or a variable, which gives a reason with `because` unless it raises or uses its variable. [effects.catch-alls-need-reason](12-effects.md#effects.catch-alls-need-reason)

**`check-error`.** The kind of panic with which code that has an error stops, where a program with errors reaches it. [program.bodies-with-errors](04-programs.md#program.bodies-with-errors)

**Conformance suite.** The programs, each annotated with what an implementation must give for it, that every implementation of Stilt is judged against. [conformance.implementations](01-conformance.md#conformance.implementations)

**Constructor trait.** A trait whose members write `Self` with type arguments, which abstracts over a type constructor such as `List`. [traits.constructor-traits](11-traits.md#traits.constructor-traits)

**Content hash.** The BLAKE3 digest of a package's manifest and source files, with which a manifest pins a fetched dependency. [packages.content-hash](04-programs.md#packages.content-hash)

**Copy.** A point in a body where a binding's value, or a part of it of a copy-on-write type, comes to be held by another binding or value too, as by a `let`, a capture or a store. [modes.copies](13-modes.md#modes.copies)

**`copy`.** The implicit effect of a write that copies data that another value shares. [facts.copy](15-facts.md#facts.copy)

**Copy-on-write type.** `str`, a list, a map, a function type, a recursive type, or a type that holds one: the types whose values share storage until one of them changes. [modes.copy-on-write-types](13-modes.md#modes.copy-on-write-types)

**Core module.** A module that uses only features of the core tier. [program.module-tier](04-programs.md#program.module-tier)

**Cycle.** A value that reaches itself, which only a `Shared<T>` can make. [cycles.through-shared-values](14-tasks.md#cycles.through-shared-values)

**Debug build.** The build that `stilt build` writes by default, which keeps every check. [builds.release-builds](20-builds.md#builds.release-builds)

**Demand.** The least mode that a use of a value accepts, as a closure that `std.par` runs demands `calm` and `portable`. [modes.demands](13-modes.md#modes.demands)

**Dependency.** A package that a manifest's `[dependencies]` names, by a `path` on the machine or a git repository it is fetched `from`. [packages.dependencies](04-programs.md#packages.dependencies)

**Dictionary.** The value through which a debug build passes a generic function the impls of its bounds. [builds.specialization](20-builds.md#builds.specialization)

**Directory program.** A program made of a directory that holds `main.lt` and no `stilt.toml`. [program.forms](04-programs.md#program.forms)

**Directory test.** A conformance test made of a directory that holds `main.lt`. [conformance.directory-tests](01-conformance.md#conformance.directory-tests)

**`div`.** The implicit effect of code that may not end, such as a `while` loop or a recursive call. [facts.div](15-facts.md#facts.div)

**Doc.** A run of `///` comments that documents the declaration on the next line. [program.doc-comments](04-programs.md#program.doc-comments)

**Doc example.** A doc line `/// ex: expr`, a `bool` expression that `stilt test` runs as a test. [program.doc-examples](04-programs.md#program.doc-examples)

**Edition.** The version of the language that a package's files are read with, named by a year in its manifest. [editions.edition](04-programs.md#editions.edition)

**Effect.** A user-defined set of operations, declared with `effect`, which a function performs and a handler implements. [handlers.declaring-effect](12-effects.md#handlers.declaring-effect)

**Error type.** The type of a name or an expression with an error: it fits every type, has every member, satisfies every bound and gives rise to no diagnostic. [errors.error-type](18-errors.md#errors.error-type)

**Escapes.** What a binding of a copy-on-write type does where its value leaves the function that binds it, as by a return, a raise or a store in another value. [modes.escaping](13-modes.md#modes.escaping)

**`escaping` parameter.** A parameter of function type that the function may keep beyond the call, whose row is exactly the one its type writes. [effects.escaping-parameters](12-effects.md#effects.escaping-parameters)

**Exhaustive.** Said of the arms of a `match` or a `catch` that cover every value of its type, as every `match` must. [patterns.non-exhaustive-matches](09-patterns.md#patterns.non-exhaustive-matches)

**Exported function.** A `pub extern fn` with a body, which a C program linked with the program's library calls. [c.exported-functions](20-builds.md#c.exported-functions)

**Fact.** What the compiler infers about a function from its body, such as whether it can panic, allocate or reach the file system, which tools show and `without` limits. [facts.inferred-facts](15-facts.md#facts.inferred-facts)

**Failed use.** A use of a macro that raised, didn't finish or comes from a module with an error, which has the error type and causes no other diagnostic. [macros.failed-uses](16-meta.md#macros.failed-uses)

**Foreign function.** An `extern fn` without a body, which C gives, and which only `unsafe` code calls. [c.foreign-functions](20-builds.md#c.foreign-functions)

**Format spec.** The part `:spec` of an interpolation that sets width, fill, alignment, precision and kind. [lexical.format-specs](02-lexical.md#lexical.format-specs)

**Handler.** A value that implements each operation of an effect, installed around a block with `with`. [handlers.handler-literals](12-effects.md#handlers.handler-literals)

**Hash.** The first four hexadecimal digits of the BLAKE3 digest of a part's canonical text, with which an edit says which text it replaces. [edits.hash](19-tools.md#edits.hash)

**Header (module).** `module` and the module's path at the start of a file, with an optional `without` clause. [program.module-header](04-programs.md#program.module-header)

**Hole.** `?`, an expression that stands for code not yet written, takes the type its context expects, gets a warning, and panics if it is reached. [declarations.typed-holes](10-declarations.md#declarations.typed-holes)

**Implicit effects.** `panic`, `overflow`, `alloc`, `div` and `copy`: effects that the compiler infers from bodies, and that no signature writes. [facts.implicit-effects](15-facts.md#facts.implicit-effects)

**In place.** Said of a write into a list element that reuses the list's storage, with no allocation. [facts.writes-in-place](15-facts.md#facts.writes-in-place)

**Inherent impl.** A block `impl Type { … }` in the type's own module, which holds its methods, functions and constants. [traits.impl-blocks](11-traits.md#traits.impl-blocks)

**`inout` argument.** An argument marked `inout`, a place that the callee may change, and that keeps every change the callee made. [expressions.inout-arguments](08-expressions.md#expressions.inout-arguments), [values.inout-arguments](05-values.md#values.inout-arguments)

**Instantiation.** One list of type and value arguments of a generic function, for which a release build compiles the function once. [builds.specialization](20-builds.md#builds.specialization)

**Interpolation.** `{expr}` or `{expr:spec}` inside a string literal, which shows the value of `expr` there. [lexical.interpolation](02-lexical.md#lexical.interpolation)

**Iterator.** A value of type `Iter<T>`, a lazy sequence of values drawn from its sources. [views.what-view-is](13-modes.md#views.what-view-is)

**Key path.** `.field` and the chains that start with one, standing for the function that reads them, as `.paid` stands for `|x| x.paid`. [expressions.key-paths](08-expressions.md#expressions.key-paths)

**Law of exclusivity.** While an access to a place is in progress, no access to an overlapping place may begin if either is a modification. [modes.law](13-modes.md#modes.law)

**Lazy value.** A value of type `Lazy<T>`, computed by its function the first time it is read. [polymorphism.lazy-values](07-types.md#polymorphism.lazy-values)

**Let-else.** `let P = e else x`, which binds the names of a refutable pattern `P` or runs `x`, which never returns. [patterns.let-else](09-patterns.md#patterns.let-else)

**Limit.** A fact that a `without` clause rules out of a module or a function, such as `panic` or `alloc`. [facts.without](15-facts.md#facts.without)

**Limitable fact.** A fact that a `without` can name and that callers inherit, and so is part of a package's API. [versions.limitable-facts](21-versions.md#versions.limitable-facts)

**Manifest.** A package's `stilt.toml`, which names the package, its edition and its dependencies. [packages.manifest](04-programs.md#packages.manifest)

**Member type.** `C.Item`, the type that the impl of a bound's trait for a type parameter `C` gives the trait's parameter `Item`. [traits.member-types](11-traits.md#traits.member-types)

**Mode.** A fact of a binding, a point on each of five axes, such as whether its value escapes or is shared, which the compiler infers and tools show. [modes.bindings-and-axes](13-modes.md#modes.bindings-and-axes)

**Module.** A `.lt` file below the module root, named by its path, as `a/b.lt` is module `a.b`. [program.module-names](04-programs.md#program.module-names)

**Namespace (of modules).** A module name or a prefix of one, as `std` is, which a `use` may name. [program.namespaces](04-programs.md#program.namespaces)

**Namespaces (of a module).** The type namespace, which holds a module's types, traits and effects, and the value namespace, which holds its variants, functions, constants, macros and imported modules. [declarations.namespaces](10-declarations.md#declarations.namespaces)

**Native.** A function, constant or type of the standard library that each implementation provides itself, written `?` in the library's sources. [declarations.native-items](10-declarations.md#declarations.native-items)

**`Never`.** The type with no values, of `raise`, `return`, `break`, `continue` and calls that never return. [declarations.never](10-declarations.md#declarations.never)

**Non-escaping parameter.** A parameter of function type that the function doesn't keep, whose effects pass through to the caller. [effects.non-escaping-parameters](12-effects.md#effects.non-escaping-parameters)

**Observable.** What an implementation is judged on: its diagnostics' codes, files and lines, what `run` prints and how it exits, and which tests pass. [conformance.observables](01-conformance.md#conformance.observables)

**Open record type.** `{ f: T, .. }` as a parameter's type, which accepts any record with those fields. [records.open-parameter-types](07-types.md#records.open-parameter-types)

**Operation.** A function of an effect, which code performs and a handler implements. [handlers.declaring-effect](12-effects.md#handlers.declaring-effect)

**Orphan impl.** An impl outside both its trait's module and its type's module, which is an error. [traits.orphan-rule](11-traits.md#traits.orphan-rule)

**Overlap.** What two places do when, with their indexes removed, one is a prefix of the other. [modes.overlap](13-modes.md#modes.overlap)

**Own code.** The functions and methods of a package itself, whose effects, capabilities and `unsafe` blocks its dependents' manifests grant. [packages.own-effects](04-programs.md#packages.own-effects)

**Pack.** A type parameter `..Ts` that stands for a sequence of zero or more types. [variadics.packs](07-types.md#variadics.packs)

**Paired row variable.** A row variable that a signature holds in a row beside a `raise<E>`, so that what it may raise is `E`. [effects.paired-row-variables](12-effects.md#effects.paired-row-variables)

**Panic.** The end of a program at an operation that can't go on, such as an index out of bounds, with a kind and a two-line report. [effects.panic-kinds](12-effects.md#effects.panic-kinds), [program.panic-report](04-programs.md#program.panic-report)

**Part (of a file with a syntax error).** The tokens of a file from one declaration's word to the next, parsed alone so that each declaration reports its first syntax error. [errors.parts](18-errors.md#errors.parts)

**Part (an edit's).** A declaration of a module, or the body of one, which an edit addresses by its path. [edits.parts](19-tools.md#edits.parts)

**Part (of a macro use).** A piece of a procedural macro use's group between commas, which goes to one of the macro's parameters. [macros.parts](16-meta.md#macros.parts)

**Path (of a declaration).** The module's name followed by the declaration's own, as `main.totals`, which addresses it. [edits.paths](19-tools.md#edits.paths)

**Pattern macro.** A macro declared with `syntax`, whose arms match the tokens of a use and substitute a template. [macros.syntax-declarations](16-meta.md#macros.syntax-declarations)

**Phase.** One of the three steps in which a body is checked, names and types, analyses and warnings, each of which runs only if the earlier ones found no error. [errors.phases](18-errors.md#errors.phases)

**Pinned doc.** A doc whose hash and whose declaration's signature hash `docs.lock` records, so that a change of the signature alone makes it stale. [docs.pins](04-programs.md#docs.pins)

**Place.** A variable followed by fields, tuple fields and indexes, as `p.items[i]`: what can be assigned and passed `inout`. [modes.places](13-modes.md#modes.places)

**Polymorphic function type.** A function type with type parameters of its own, as `fn<T: Show>(T) -> str`. [polymorphism.function-types](07-types.md#polymorphism.function-types)

**Prelude.** The fixed set of types, variants, traits and functions in scope in every module without a `use`. [program.contents](04-programs.md#program.contents)

**Primary span.** The place a diagnostic is reported at, which the registry gives for each code, and whose first line conformance compares. [errors.primary-spans](18-errors.md#errors.primary-spans)

**Primitive type name.** One of `bool`, the integer and float types and `str`, which can name nothing else. [lexical.primitive-type-names](02-lexical.md#lexical.primitive-type-names)

**Procedural macro.** A compile-time function declared with `macro`, from syntax to syntax. [macros.procedural-declarations](16-meta.md#macros.procedural-declarations)

**Profile.** The counts that a debug run writes of how often each body, branch and loop runs, which a release build reads. [builds.profiles](20-builds.md#builds.profiles)

**Projection.** A function whose result type is `inout T`, whose call is a place. [projections.declaring-projection](13-modes.md#projections.declaring-projection)

**Property.** A doc line `/// prop: closure`, a statement about every value of the closure's parameters, which `stilt test` checks on generated cases. [tests.prop-lines](19-tools.md#tests.prop-lines)

**Quote.** `quote { … }` and its forms, an expression that writes code inside a procedural macro. [macros.quote](16-meta.md#macros.quote)

**Record bound.** A bound `P: { f: T, .. }` that a type meets when it is a record with those fields. [records.record-bounds](07-types.md#records.record-bounds)

**Reference interpreter.** The implementation of Stilt that every other is compared with, program by program. [conformance.implementations](01-conformance.md#conformance.implementations)

**Refusal.** An edit that a command doesn't apply, because its address names nothing or its hash isn't that of the text there, with a code of its own. [edits.refusals](19-tools.md#edits.refusals)

**Release build.** The build that `stilt build --release` writes, which means what the debug build means and drops only the checks that can't fail. [builds.release-builds](20-builds.md#builds.release-builds)

**Root cause.** A diagnostic that no other diagnostic caused, the only kind an implementation reports. [errors.root-causes](18-errors.md#errors.root-causes)

**Row.** The effects of a function, written after its return type, as `/ {io, raise<ParseError>}`. [effects.rows](12-effects.md#effects.rows)

**Row variable.** A lowercase name in a row, declared among a function's generics, that stands for effects the signature doesn't spell out, as those of the functions it is given. [effects.rows](12-effects.md#effects.rows)

**Scope (of tasks).** A value of type `Scope<E>`, whose tasks may raise `E` and which ends once all of them have ended. [tasks.scopes](14-tasks.md#tasks.scopes)

**Sequential run.** The run under `task.sequential()`, in which each task runs to its end when it starts: the meaning of every program with tasks. [tasks.sequential-run](14-tasks.md#tasks.sequential-run)

**Session.** A run of `stilt repl` on a program, which evaluates inputs in a module's scope. [repl.sessions](19-tools.md#repl.sessions)

**Shared (mode).** Said of a modification of a `var` binding or an `inout` parameter while a copy of the modified part may still last, so that the write copies the data first. [modes.shared-writes](13-modes.md#modes.shared-writes)

**Shared value.** A value of type `Shared<T>`, a handle on one value that every copy of the handle reaches, inside a `when`. [shared.std-sync](14-tasks.md#shared.std-sync)

**Shrinking.** What `stilt test` does to the values of a property's failing case, replacing each by smaller ones while the property still fails. [tests.shrinking](19-tools.md#tests.shrinking)

**Source (of a view).** The value that a view or an iterator reads from. [views.what-view-is](13-modes.md#views.what-view-is)

**Stale doc.** A pinned doc whose declaration's signature has changed while the doc hasn't, which is a warning. [docs.stale](04-programs.md#docs.stale)

**Staging annotation.** `comptime` before a `for`, an `if` or a `match`, which marks a part of a body known at compile time without changing what it means. [meta.staging-annotations](16-meta.md#meta.staging-annotations)

**Structural impls.** The impls of the prelude's traits that tuples, records, variant types, lists, maps, `Option` and `Result` get without one being written. [traits.structural-impls](11-traits.md#traits.structural-impls)

**Syntax error.** A lexical error or an error of the grammar, after which the rest of the declaration reports nothing. [errors.syntax-errors](18-errors.md#errors.syntax-errors)

**Task.** A function run by `spawn`, whose handle `await` waits for. [tasks.std-task](14-tasks.md#tasks.std-task)

**Terminator.** A newline that ends a statement, inserted where a line ends with a token that can end an expression. [lexical.terminator-insertion](02-lexical.md#lexical.terminator-insertion)

**Test.** `test "name" { body }`, a block that `stilt test` runs and that passes when it finishes without raising, panicking or calling `exit`. [program.test-declarations](04-programs.md#program.test-declarations)

**Tier.** One of `core`, `advanced`, `meta` and `systems`, the ordered levels of the language, each allowing more features than the one before. [program.tiers](04-programs.md#program.tiers)

**Tier (of a module).** The first tier that allows every feature the module uses, inferred, never declared. [program.module-tier](04-programs.md#program.module-tier)

**Trait.** A set of function signatures, with optional default bodies, that types implement in impls. [traits.declaring-trait](11-traits.md#traits.declaring-trait)

**Trait parameter.** A type parameter of a trait, as `T` in `trait Collection<T>`. [traits.trait-parameters](11-traits.md#traits.trait-parameters)

**`unsafe` block.** `unsafe because "reason" { … }`, the only place where unsafe operations, such as calls of foreign functions, may stand. [c.unsafe-because](20-builds.md#c.unsafe-because), [c.unsafe-operations](20-builds.md#c.unsafe-operations)

**Value parameter.** A generic `n: i64` whose argument is a value known at compile time, as in `Array<T, n>`. [generics.value-parameters](07-types.md#generics.value-parameters)

**Value semantics.** The property of every core value that it can appear to change only through a binding the program names as mutable. [values.value-semantics](05-values.md#values.value-semantics)

**Verification.** The part of `stilt check` that proves operations safe, such as an index in bounds, from each body alone. [facts.verification](15-facts.md#facts.verification)

**Version.** A tag `vMAJOR.MINOR.PATCH` of a dependency's repository, whose number says how its API changed. [packages.versions](04-programs.md#packages.versions), [versions.change-needed](21-versions.md#versions.change-needed)

**View.** A value of type `View<T>`, a window into part of a value, which reads its source without copying it. [views.what-view-is](13-modes.md#views.what-view-is)

**`when`.** `when a, b { … }`, the block that waits to hold the values of shared handles and then reaches them. [shared.when](14-tasks.md#shared.when)

**`without`.** The clause, in a module header or after a function's signature, that names the limits its code keeps. [facts.without](15-facts.md#facts.without)
