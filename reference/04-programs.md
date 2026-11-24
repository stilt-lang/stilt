# 4. Programs, modules and packages

A program is a set of modules, read from files. This chapter says how files become modules, what a module header holds, how modules see and import one another, and what the prelude gives every module. It then says where a program starts, how it ends, how its tests run, and how `run` runs a program with errors. Its last sections cover packages: their manifests and dependencies, what a manifest grants them, editions, pinned docs, duplicate bodies and the documentation that `stilt doc` writes.

[Inferred facts and limits](15-facts.md) says what a `without` limits, [Effects, failure and handlers](12-effects.md) defines rows and panics, and [Versions and compatibility](21-versions.md) defines the versions of fetched packages.

## Programs and modules

<a id="program.forms"></a>
A program takes one of three forms:

| Form | Root directory | Module root |
| --- | --- | --- |
| A single file | The directory that holds the file | The file itself, which is module `main` whatever its name |
| A directory program: a directory that holds `main.lt` | The directory | The directory |
| A package: a directory that holds `stilt.toml` | The directory | Its `src/` folder |

A directory that holds `stilt.toml` is a package, even when it also holds `main.lt`. The `stilt.toml` file is the package's manifest ([packages.manifest](#packages.manifest)). A package without a `src/` folder has no modules. A program's modules are its own and those of the packages it depends on ([packages.modules-of-dependencies](#packages.modules-of-dependencies)).

Tests: [names/header_mismatch.lt](../conformance/names/header_mismatch.lt), [program/directory_program](../conformance/program/directory_program/), [program/package](../conformance/program/package/), [program/package_manifest_not_toml](../conformance/program/package_manifest_not_toml/), [program/package_without_src](../conformance/program/package_without_src/), [program/single-file.lt](../conformance/program/single-file.lt).

<a id="program.module-names"></a>
Below the module root, every `.lt` file is a module. The file `a/b.lt` is module `a.b`, and `main.lt` at the module root is module `main`.

A program's modules are found through symbolic links to files and directories, each at the link's path. A link to a directory that is, or holds, one of the directories it is found through would make a cycle, and is skipped. Only regular files, and links to them, are modules. Any other entry whose name ends in `.lt`, such as a named pipe or a link that names nothing, is skipped. Entries whose names start with `.`, files and directories alike, are not part of the program: `stilt fmt` skips them, and a macro is given none of them ([macros.named-files](16-meta.md#macros.named-files)).

Each segment of the file's path below the module root, without the `.lt`, must be a lowercase identifier ([lexical.identifiers](02-lexical.md#lexical.identifiers)) that is neither a reserved word nor a primitive type name. The first segment must be neither `std`, which names the standard library, nor the name of a dependency of the package ([packages.imports](#packages.imports)). So `a.b.lt`, `Util.lt`, `my-module.lt` and `type.lt` are invalid.

A file whose module name is invalid is E0200, *invalid module name*, on its first line. Its declarations are still checked, but no other module can name it. A `use` declaration or a path that names it has the error type ([errors.error-type](18-errors.md#errors.error-type)) and is no further error. So does one that names a prefix of its name that isn't a namespace ([program.namespaces](#program.namespaces)).

Tests: [names/header_mismatch_nested](../conformance/names/header_mismatch_nested/), [names/invalid_module_names](../conformance/names/invalid_module_names/), [packages/module_named_like_dependency](../conformance/packages/module_named_like_dependency/), [program/hidden_and_linked](../conformance/program/hidden_and_linked/), [program/invalid_name_checked](../conformance/program/invalid_name_checked/).

Checked by: also the toolchain's tests of links that would make cycles and of named pipes, which a repository can't hold (`compiler/stilt-cli/tests/program_files.rs`, `compiler/stilt-pkg/src/files/tests.rs` and `compiler/stilt-pkg/src/git/tree/tests.rs`), and the reference interpreter's (`interpreter/test/test_program.ml`).

<a id="program.report-paths"></a>
Every path that an implementation reports, in a diagnostic, a panic report or a tool's output, is relative to the root directory and uses `/` as the separator.

Tests: [program/package](../conformance/program/package/).

## Module headers and tiers

<a id="program.module-header"></a>
A file may begin with a **header**: `module` and a path (the `file` production, [syntax.programs](03-syntax.md#syntax.programs)). The path must be the file's module name. Otherwise the header is E0201, *module header doesn't match its file*, at the path. So a single file's header always says `module main`.

A `without` clause may follow the path: on the same line, on the next line, which continues the header ([lexical.continuation-lines](02-lexical.md#lexical.continuation-lines)), or after a `;`. Indentation inside the header has no meaning. The clause limits facts that the compiler infers about the bodies of the module's functions: `panic`, `overflow`, `alloc`, `div`, `copy`, `locks`, the eight capabilities ([facts.capabilities](15-facts.md#facts.capabilities)) and `unsafe`. Code beyond a limit is E0204 ([facts.without](15-facts.md#facts.without)). A module without a `without` clause has no limit.

Tests: [implicit/unlimited_alloc.lt](../conformance/implicit/unlimited_alloc.lt), [implicit/without_alloc](../conformance/implicit/without_alloc/), [lexical/contextual_keywords.lt](../conformance/lexical/contextual_keywords.lt), [names/header_mismatch.lt](../conformance/names/header_mismatch.lt), [names/header_mismatch_nested](../conformance/names/header_mismatch_nested/), [program/directory_program](../conformance/program/directory_program/), [program/header_limits_on_path_line.lt](../conformance/program/header_limits_on_path_line.lt), [program/header_options.lt](../conformance/program/header_options.lt), [program/header_separators.lt](../conformance/program/header_separators.lt), [program/single-file.lt](../conformance/program/single-file.lt).

<a id="program.header-limits"></a>
A header holds at most one `without`, and a `without` names each limit at most once. A second `without` in a header is E0202, *`without` given twice*, at the second occurrence, and so is a limit named twice in one clause. The second occurrence is otherwise ignored. A word after `without` that isn't a limit is a syntax error (E0100), and the name of a tier is such a word. So is a `without` that stands neither in a header nor after a function's signature, where a function's own clause stands ([declarations.limits](10-declarations.md#declarations.limits)).

Tests: [declarations/repeated_limit.lt](../conformance/declarations/repeated_limit.lt), [lexical/tier_after_without.lt](../conformance/lexical/tier_after_without.lt), [names/repeated_option.lt](../conformance/names/repeated_option.lt), [names/repeated_without_is_ignored.lt](../conformance/names/repeated_without_is_ignored.lt), [program/header_limits_on_path_line.lt](../conformance/program/header_limits_on_path_line.lt), [program/option_after_item.lt](../conformance/program/option_after_item.lt), [program/unknown_limit.lt](../conformance/program/unknown_limit.lt), [program/unknown_option.lt](../conformance/program/unknown_option.lt).

<a id="program.tiers"></a>
The language has four **tiers**, ordered `core`, `advanced`, `meta` and `systems`. Each tier allows everything that the tiers before it allow. Each feature belongs to one tier, and the paragraph that defines a feature of a later tier says which uses of it put a module in that tier:

| Tier | Features |
| --- | --- |
| `advanced` | Views and iterators ([views.std-view](13-modes.md#views.std-view)), projections ([projections.declaring-projection](13-modes.md#projections.declaring-projection)), polymorphic function types ([polymorphism.advanced-tier](07-types.md#polymorphism.advanced-tier)) and `Lazy` ([polymorphism.lazy-values](07-types.md#polymorphism.lazy-values)), anonymous and open records and record bounds ([records.advanced-tier](07-types.md#records.advanced-tier)), packs ([variadics.advanced-tier](07-types.md#variadics.advanced-tier)), trait parameters, trait constants, member types and constructor traits ([traits.advanced-tier](11-traits.md#traits.advanced-tier)), user-defined effects and handlers ([handlers.advanced-tier](12-effects.md#handlers.advanced-tier)), tasks and shared values ([tasks.advanced-tier](14-tasks.md#tasks.advanced-tier)), and pattern macros ([macros.advanced-tier](16-meta.md#macros.advanced-tier)) |
| `meta` | Value parameters ([generics.meta-tier](07-types.md#generics.meta-tier)), staging annotations ([meta.staging-tier](16-meta.md#meta.staging-tier)), reflection and bound tests ([meta.reflection-tier](16-meta.md#meta.reflection-tier)), and procedural macros and quotes ([macros.meta-tier](16-meta.md#macros.meta-tier)) |
| `systems` | Foreign functions, `unsafe` blocks and `std.c` ([c.systems-tier](20-builds.md#c.systems-tier)) |

Every other feature is a core feature, `std.par` among them ([par.core-tier](14-tasks.md#par.core-tier)). A word reserved for a feature that the language doesn't define is no part of the language ([lexical.reserved-words](02-lexical.md#lexical.reserved-words)). Using one is the syntax error that any reserved word used as a name is.

Checked by: the facts suite, whose files state their module's tier with `//~ tier:`, which `just facts` checks (`compiler/stilt-cli/tests/facts.rs`).

<a id="program.module-tier"></a>
A module's **tier** is the first tier that allows every feature the module uses. It is inferred, never declared, chosen or limited. No header names a tier, and a `without` that names one is a syntax error ([program.header-limits](#program.header-limits)).

The tier is recorded in the module's interface and shown as the inferred facts are ([facts.visibility](15-facts.md#facts.visibility)). `stilt show` prints it with each of the module's functions, and the language server shows it beside them. The module's skeleton leaves it out.

A module that uses only core features is a **core module**. A module that only uses an item declared elsewhere stays in its tier, unless the paragraph of the item's feature says otherwise, as for a module that names `View`.

Checked by: the facts suite, whose `//~ tier:` annotations `just facts` checks (`compiler/stilt-cli/tests/facts.rs`), and the toolchain's tests of `stilt show` and of the language server (`compiler/stilt-cli/tests/show.rs`, `compiler/stilt-cli/tests/lsp_reading.rs`).

<a id="program.unsupported-tiers"></a>
A feature of a tier that an implementation doesn't support is E0203, *feature of an unsupported tier*, at the feature.

Checked by: no test, since the reference interpreter and the compiler support every tier, so no program can get E0203 from them.

## Visibility

<a id="program.visibility"></a>
Items are private to their module unless marked `pub`. Naming another module's private item, or a private member of an `impl` block, is E0213, *private item*, at its name. The fields and variants of a type have the type's visibility. A function or a constant of an inherent `impl` block is private unless marked `pub`, and other modules see a `pub` one only if they see its type.

The methods of a trait impl are visible wherever both the trait and the type are. They are written without `pub`, which is a syntax error there (E0100). A call of a trait's method needs the method to be visible, and its trait to be in scope as well ([traits.traits-in-scope](11-traits.md#traits.traits-in-scope)).

Tests: [names/private_item](../conformance/names/private_item/), [names/private_method](../conformance/names/private_method/), [packages/private_item](../conformance/packages/private_item/), [program/pub_in_trait_impl.lt](../conformance/program/pub_in_trait_impl.lt), [program/visibility](../conformance/program/visibility/), [program/visibility_accepted](../conformance/program/visibility_accepted/), [traits/trait_through_parent](../conformance/traits/trait_through_parent/), [traits/trait_through_use](../conformance/traits/trait_through_use/), [traits/trait_visibility](../conformance/traits/trait_visibility/).

<a id="program.private-in-signatures"></a>
A private type or trait can't appear in a signature that other modules see: that of a `pub` item, or of a `pub` member of a `pub` type. One that does is E0214, *private item in a public signature*, at the path that names it. A function's signature is its generics, parameter types, return type and row. A constant's signature is its type, a type's is the types of its fields and payloads, and a trait's is the signatures of its methods.

Tests: [names/private_in_public.lt](../conformance/names/private_in_public.lt), [program/private_in_signatures.lt](../conformance/program/private_in_signatures.lt).

## Imports

<a id="program.what-use-binds"></a>
`use a.b.c` makes module `a.b.c` available under the name `c`. Code names the module's items through that name, by qualified names such as `fs.read(…)` and `orders.Order`. `use` imports modules, never individual items. There are no import aliases and no re-exports.

A `use` whose path names no namespace ([program.namespaces](#program.namespaces)), but names an item of a module as a path in code does, is E0230, *`use` of an item*, at the `use`. Its path names an item when, after the first name along it that is a module, the next name is an item that the module declares, whatever its visibility. The item is a function, a constant, a type or one of its variants, a trait, an effect or a macro.

So `use std.sync.Shared`, `use std.io.read_line` and `use std.sync.Shared.new` are E0230. The message names the item as code names it through its module, as `sync.Shared`, and the fix writes the module's path, `use std.sync`.

Tests: [expressions/qualified_struct_literal](../conformance/expressions/qualified_struct_literal/), [names/item_import](../conformance/names/item_import/), [names/unknown_module.lt](../conformance/names/unknown_module.lt), [names/unknown_names.lt](../conformance/names/unknown_names.lt), [names/unqualified_imported_function.lt](../conformance/names/unqualified_imported_function.lt), [names/wrong_kind.lt](../conformance/names/wrong_kind.lt), [ported/hamming_numbers.lt](../conformance/ported/hamming_numbers.lt), [program/directory_program](../conformance/program/directory_program/), [program/namespace_import.lt](../conformance/program/namespace_import.lt), [program/visibility](../conformance/program/visibility/), [program/visibility_accepted](../conformance/program/visibility_accepted/), [traits/trait_visibility](../conformance/traits/trait_visibility/).

<a id="program.namespaces"></a>
A **namespace** is a module name or a prefix of one: `std` is a namespace because `std.io` is a module. A `use` may name any namespace. Its path is a lowercase name followed by names of either case (the `use_path` production, [syntax.paths](03-syntax.md#syntax.paths)), so naming an item is no syntax error. A `use` whose path names neither a namespace nor an item is E0205, *unknown module*, at the `use`, as `use std.Io`, `use std.io.nothing` and `use nothing` are. The name that the `use` of an E0205 or an E0230 binds has the error type, so the code that names it gets no error of its own.

Tests: [names/item_import](../conformance/names/item_import/), [names/unknown_module.lt](../conformance/names/unknown_module.lt), [packages/misspelled_dependency](../conformance/packages/misspelled_dependency/), [program/namespace_import.lt](../conformance/program/namespace_import.lt).

<a id="program.child-modules"></a>
A child module can be reached through its parent: after `use a`, `a.b.c.f()` works. In a path, `n.x` names the item `x` of `n` when `n` is a module that declares one, and the namespace `n.x` otherwise. So an item hides a child module of its name. A path through the item to the module's items is a wrong kind of name (E0212, [declarations.wrong-kind-of-name](10-declarations.md#declarations.wrong-kind-of-name)). A module's `use` declarations are not its items, so a path never reaches a module through another module's imports.

Tests: [names/import_parent_of_one](../conformance/names/import_parent_of_one/), [names/item_hides_child_module](../conformance/names/item_hides_child_module/), [names/own_item_through_parent](../conformance/names/own_item_through_parent/), [program/imports_are_not_items](../conformance/program/imports_are_not_items/).

<a id="program.import-clashes"></a>
Two `use` declarations that bind the same name are a name defined twice (E0208, [declarations.unique-names](10-declarations.md#declarations.unique-names)), at the later one. The fix is to import the parent of one of the two modules instead and reach the module through it, as `use std` with `std.io.read_line()`.

Tests: [names/import_clash](../conformance/names/import_clash/), [names/import_parent_of_one](../conformance/names/import_parent_of_one/).

<a id="program.no-cycles"></a>
A module depends on each module that it imports with `use` or `meta use` ([macros.meta-use](16-meta.md#macros.meta-use)). It also depends on each other module whose item it names in a path, as `fs.read` names an item of `std.fs`. These dependencies must be acyclic. So a module that imports itself is an error, while one that names its own item through its parent, as `a.b.f()` does inside `a.b`, is not.

Each group of modules that depend on one another in a cycle is one E0206, *import cycle*. It is reported at the last of the `use` declarations and paths through which they name one another ([errors.several-places](18-errors.md#errors.several-places)), and its message shows a whole cycle.

Tests: [names/import_cycle_1.lt](../conformance/names/import_cycle_1.lt), [names/import_cycle_2](../conformance/names/import_cycle_2/), [names/import_cycle_3](../conformance/names/import_cycle_3/), [names/import_cycle_through_path](../conformance/names/import_cycle_through_path/), [names/import_cycles_sharing_a_module](../conformance/names/import_cycles_sharing_a_module/), [names/own_item_through_parent](../conformance/names/own_item_through_parent/), [protocol/cycle_in_last_path](../conformance/protocol/cycle_in_last_path/).

<a id="program.one-value-namespace"></a>
The names that `use` declarations bind share the value namespace with the functions, constants, variants and macros of the module ([declarations.namespaces](10-declarations.md#declarations.namespaces)). So a local binding named after an imported module is E0207, *local named after an imported module*, at the binding's name. Every use of that binding has the error type. A `use` that binds the name of an item of its module is a name defined twice (E0208). A module is no value, so `let m = fs` after `use std.fs` is a wrong kind of name (E0212).

Tests: [names/local_hides_module.lt](../conformance/names/local_hides_module.lt), [names/wrong_kind.lt](../conformance/names/wrong_kind.lt), [program/local_named_like_module.lt](../conformance/program/local_named_like_module.lt), [program/use_and_item_clash.lt](../conformance/program/use_and_item_clash.lt).

## The prelude

<a id="program.contents"></a>
The **prelude** is in scope in every module without a `use`. Its items live in `std.prelude`, and it contains exactly:

- **types:** the primitive types `bool`, `i8` to `i64`, `u8` to `u64`, `f32`, `f64` and `str`, and `Never`, `Option`, `Result`, `List`, `Map`, `Set` and `Ordering`;
- **variants:** `Some`, `None`, `Ok`, `Err`, `Less`, `Equal` and `Greater`;
- **traits:** `Eq`, `Ord`, `Hash` and `Show`;
- **functions:** `print`, `eprint`, `panic`, `unreachable` and `exit` ([program.prelude-functions](#program.prelude-functions)).

No library extends it, so every other name of `std` is reached through its module, as `sync.Shared` is.

Tests: [program/prelude.lt](../conformance/program/prelude.lt), [values/no_copy_trait.lt](../conformance/values/no_copy_trait.lt), [values/shared_is_advanced.lt](../conformance/values/shared_is_advanced.lt).

<a id="program.prelude-names"></a>
A module other than `std.prelude` can't declare an item, or bind a name with `use`, that has the name of a prelude item in the same namespace. It can't declare a type or a trait named after a prelude type or trait. It can't declare a variant, a function, a constant or an imported module named after a prelude variant or function.

Doing so is E0209, *name of a prelude item*, at the declared name or the `use`. In that module, every use of the name in that namespace has the error type, so it refers to neither item. Other modules still reach the module's item by its qualified name. A primitive type name used as a name is E0210 instead ([lexical.primitive-type-names](02-lexical.md#lexical.primitive-type-names)).

Tests: [names/prelude_names.lt](../conformance/names/prelude_names.lt), [names/primitive_names.lt](../conformance/names/primitive_names.lt), [patterns/shadowed_prelude_name_in_pattern.lt](../conformance/patterns/shadowed_prelude_name_in_pattern.lt), [program/prelude_qualified](../conformance/program/prelude_qualified/), [program/prelude_same_namespace.lt](../conformance/program/prelude_same_namespace.lt).

<a id="program.prelude-namespaces"></a>
A name is read in one namespace at a time ([declarations.name-lookup](10-declarations.md#declarations.name-lookup)), so the prelude item of the other namespace keeps its meaning. A module may declare a variant `Eq` or `Show` beside the traits, or a variant `List` beside the type. It can't declare a type `Option`, a variant `Less` or a module `print`. A pattern that names a variant through the type it matches ([patterns.variants-by-type](09-patterns.md#patterns.variants-by-type)) names the prelude's variant even so. With `o: Option<i64>`, `Some(x)` names the prelude's `Some` in a module that declares a variant `Some`.

Tests: [patterns/prelude_variant_through_type.lt](../conformance/patterns/prelude_variant_through_type.lt), [program/prelude_other_namespace.lt](../conformance/program/prelude_other_namespace.lt).

<a id="program.qualified-names"></a>
A module uses its own items, and the prelude's, unqualified. Every other name is written qualified: an item of another module through its module, as `fs.read`, and a member of a type through the type, as `f64.PI`. So a function of an imported module called without its module is an unknown name (E0211). The one exception is a pattern, which names a variant through the type it matches ([patterns.variants-by-type](09-patterns.md#patterns.variants-by-type)). So `Seq(items)` names `ebnf.Seq` where an `ebnf.Expr` is matched.

Tests: [names/unknown_names.lt](../conformance/names/unknown_names.lt), [names/unqualified_imported_function.lt](../conformance/names/unqualified_imported_function.lt), [patterns/bare_variant_errors](../conformance/patterns/bare_variant_errors/), [patterns/bare_variants](../conformance/patterns/bare_variants/), [ported/josephus.lt](../conformance/ported/josephus.lt).

<a id="program.prelude-functions"></a>
The prelude's functions are:

| Function | Behaviour |
| --- | --- |
| `print(s: str) / io` | Writes `s` and a newline to stdout |
| `eprint(s: str) / io` | Writes `s` and a newline to stderr |
| `exit(code: u8) -> Never / io` | Flushes both output streams and ends the process with `code` |
| `panic(msg: str) -> Never` | Panics with the kind `explicit` |
| `unreachable() -> Never` | Panics with the kind `unreachable` |

Because `exit` has type `Never`, a `catch` arm or an `else` branch that calls it checks wherever a value is expected.

Tests: [effects/panic_explicit.lt](../conformance/effects/panic_explicit.lt), [effects/panic_unreachable.lt](../conformance/effects/panic_unreachable.lt), [numerics/divide_by_zero.lt](../conformance/numerics/divide_by_zero.lt), [program/empty_panic.lt](../conformance/program/empty_panic.lt), [program/exit_status.lt](../conformance/program/exit_status.lt), [program/explicit_panic.lt](../conformance/program/explicit_panic.lt), [program/prelude.lt](../conformance/program/prelude.lt), [program/print_integer.lt](../conformance/program/print_integer.lt), [program/unreachable.lt](../conformance/program/unreachable.lt).

<a id="program.output-flushing"></a>
Each line that `print` writes reaches stdout when `print` returns. What `io.write` writes without a newline reaches stdout at the first of these ([std.io](17-std.md#std.io)):

- the next newline;
- a call of `io.flush()`;
- a read by `io.read_line`, `io.read_all` or `io.poll_line`, before it reads;
- the end of the process.

`eprint` and `io.ewrite` reach stderr when they return. Everything written reaches its stream before the process exits with status 0, 1, 2 or 101, or with the status that `exit` gives. It also reaches its stream before a panic report is written. After an abort, which exits with status 134, or with 2 in a program with errors, how much of it was written is unspecified.

Tests: [handlers/body_panics_after_printing.lt](../conformance/handlers/body_panics_after_printing.lt), [handlers/body_raises_after_printing.lt](../conformance/handlers/body_raises_after_printing.lt), [program/exit_flushes.lt](../conformance/program/exit_flushes.lt), [program/flush_with_errors.lt](../conformance/program/flush_with_errors.lt), [program/output_before_panic.lt](../conformance/program/output_before_panic.lt), [std/io_flush.lt](../conformance/std/io_flush.lt).

Checked by: also the toolchain's tests of programs read through a pipe while they run, under `run`, as built executables and under `test` (`compiler/stilt-cli/tests/streams.rs`), since a conformance test captures stdout whole.

## The entry point

<a id="program.main"></a>
A program's entry point is the function `main` of module `main`. It has no parameters and returns `()`. Its row holds at most these effects:

- `io`;
- a `raise<E>` whose `E` implements `Show`;
- `async`, under which its tasks run in sequence ([tasks.sequential-run](14-tasks.md#tasks.sequential-run)).

A user-defined effect in its row is E0512 ([handlers.no-effect-reaches-main](12-effects.md#handlers.no-effect-reaches-main)). Any other signature is E0310, *invalid `main`*, at its name, a generic one, one with a row variable and one that returns `Never` among them. The command-line arguments come from `std.cli` ([std.cli](17-std.md#std.cli)). A function `main` of any other module is an ordinary function.

Tests: [declarations/main_raising_unshowable.lt](../conformance/declarations/main_raising_unshowable.lt), [declarations/main_with_parameters.lt](../conformance/declarations/main_with_parameters.lt), [declarations/main_with_result.lt](../conformance/declarations/main_with_result.lt), [program/main_generic.lt](../conformance/program/main_generic.lt), [program/main_in_library](../conformance/program/main_in_library/), [program/main_returns_never.lt](../conformance/program/main_returns_never.lt), [program/main_returns_unit.lt](../conformance/program/main_returns_unit.lt), [program/main_row_variable.lt](../conformance/program/main_row_variable.lt), [program/raise_escapes_main.lt](../conformance/program/raise_escapes_main.lt), [program/raise_record_escapes_main.lt](../conformance/program/raise_record_escapes_main.lt), [program/raise_str_escapes_main.lt](../conformance/program/raise_str_escapes_main.lt).

<a id="program.missing-main"></a>
`check` and `test` don't require a `main`. `run` reports a program that has no `main`, and exits with status 2 without running anything.

Tests: [program/main_in_library](../conformance/program/main_in_library/), [program/missing_main.lt](../conformance/program/missing_main.lt), [program/package_without_src](../conformance/program/package_without_src/), [protocol/main_in_other_module](../conformance/protocol/main_in_other_module/).

## How a program ends

<a id="program.exit-statuses"></a>
How a program ends decides its exit status:

| How the program ends | Exit status |
| --- | --- |
| `main` returns | `0` |
| It calls `exit(code)` | `code` |
| A raise escapes `main` | `1`, after writing `error: {e}` and a newline to stderr |
| A panic | `101`, after the panic report ([program.panic-report](#program.panic-report)) |
| A stack overflow, or running out of memory | `134`, after writing `fatal: <reason>` to stderr |
| A write to standard output finds it closed, as a pipe is once the program reading it has ended | `141`, the status a shell reports for a process that a broken pipe's signal ends, after writing nothing more |
| The program has errors | `2`, however it ends ([program.programs-with-errors](#program.programs-with-errors)) |
| `run` finds no `main` | `2`, without running anything ([program.missing-main](#program.missing-main)) |

How much memory a program may use is up to the implementation, which documents it. The reference interpreter allows 512 MiB of heap. A stack overflow or running out of memory isn't a panic: it aborts the process. A closed standard output isn't a panic either. So a program that prints forever ends when the output it feeds is closed, as `stilt run gen | head -1` closes it.

Tests: [handlers/body_panics_after_printing.lt](../conformance/handlers/body_panics_after_printing.lt), [handlers/body_raises_after_printing.lt](../conformance/handlers/body_raises_after_printing.lt), [program/exit_flushes.lt](../conformance/program/exit_flushes.lt), [program/exit_status.lt](../conformance/program/exit_status.lt), [program/main_returns_unit.lt](../conformance/program/main_returns_unit.lt), [program/raise_escapes_main.lt](../conformance/program/raise_escapes_main.lt), [program/raise_record_escapes_main.lt](../conformance/program/raise_record_escapes_main.lt), [program/raise_str_escapes_main.lt](../conformance/program/raise_str_escapes_main.lt), [program/stack_overflow.lt](../conformance/program/stack_overflow.lt), [std/invalid_utf8_escapes_main](../conformance/std/invalid_utf8_escapes_main/), [std/result_get_escapes_main.lt](../conformance/std/result_get_escapes_main.lt).

Checked by: also, for a closed standard output, which no conformance test can close, the toolchain's tests of streams (`compiler/stilt-cli/tests/streams.rs`), under `stilt run` and in a built program, one that has started a child among them.

<a id="program.panic-report"></a>
A panic writes these two lines to stderr, then ends the program with status 101:

```text
panic: <kind>: <detail>
  at <path>:<line>:<col>
```

`<kind>` is one of the kinds of [effects.panic-kinds](12-effects.md#effects.panic-kinds). Nothing is written after the two lines, so they are always the last two lines of stderr.

Tests: [ported/fibonacci.lt](../conformance/ported/fibonacci.lt), [program/output_before_panic.lt](../conformance/program/output_before_panic.lt), [program/package](../conformance/program/package/), [program/single-file.lt](../conformance/program/single-file.lt), [std/map_compares_in_insertion_order.lt](../conformance/std/map_compares_in_insertion_order.lt), [std/map_compares_only_equal_hashes.lt](../conformance/std/map_compares_only_equal_hashes.lt), [std/map_hashes_every_key.lt](../conformance/std/map_hashes_every_key.lt).

<a id="program.panic-detail"></a>
`<detail>` is one line of non-empty text. For the kind `explicit`, it is the message passed to `panic`. For the kind `unwrap` that `expect` raises, it is the message passed to `expect`. Each of these two messages is written as a nested string is shown, quoted and escaped ([std.show-names-and-escapes](17-std.md#std.show-names-and-escapes)), so `panic("")` gives `panic: explicit: ""`. For every other panic, `unwrap` included, the wording of `<detail>` is up to the implementation.

Tests: [effects/panic_expect.lt](../conformance/effects/panic_expect.lt), [effects/panic_expect_err.lt](../conformance/effects/panic_expect_err.lt), [effects/panic_unwrap.lt](../conformance/effects/panic_unwrap.lt), [effects/panic_unwrap_err.lt](../conformance/effects/panic_unwrap_err.lt), [program/empty_panic.lt](../conformance/program/empty_panic.lt), [program/explicit_panic.lt](../conformance/program/explicit_panic.lt), [program/panic_message_escapes.lt](../conformance/program/panic_message_escapes.lt).

<a id="program.panic-location"></a>
`<path>`, `<line>` and `<col>` locate the operation that panicked in the program's own files. They locate the start of the expression that performs it, such as the left operand of `a + b`, the list of `xs[i]` or the callee of a call. For a failed `assert`, they locate its `assert` keyword. For a panic inside the standard library, `panic`, `unreachable` and indexing included, they locate the call from the program into the standard library. A `check-error` panic is located as [program.check-error-report](#program.check-error-report) says.

`<path>` is written as [program.report-paths](#program.report-paths) says. `<line>` and `<col>` are 1-based, and the column counts Unicode scalar values, with a tab counting as one.

Tests: [program/error_reached_in_function.lt](../conformance/program/error_reached_in_function.lt), [program/panic_in_callback.lt](../conformance/program/panic_in_callback.lt), [program/panic_in_interpolation.lt](../conformance/program/panic_in_interpolation.lt), [program/panic_in_operator.lt](../conformance/program/panic_in_operator.lt), [program/panic_in_std.lt](../conformance/program/panic_in_std.lt), [program/panic_location_columns.lt](../conformance/program/panic_location_columns.lt), [program/panic_location_in_interpolation.lt](../conformance/program/panic_location_in_interpolation.lt), [program/panic_location_in_std.lt](../conformance/program/panic_location_in_std.lt), [program/unreachable.lt](../conformance/program/unreachable.lt).

<a id="program.recursion-depth"></a>
Every implementation supports a call depth of at least 10,000 frames of ordinary functions.

Tests: [program/deep_mutual_recursion.lt](../conformance/program/deep_mutual_recursion.lt), [program/deep_recursion.lt](../conformance/program/deep_recursion.lt), [program/stack_overflow.lt](../conformance/program/stack_overflow.lt).

<a id="program.stderr-with-status-2"></a>
`run` exits with status 2 when the program has errors or has no `main`. What it then writes to stderr is unspecified, apart from the panic report that ends a program with errors that panics.

Checked by: the conformance runner, for which a test that expects status 2 together with a `stderr` block is malformed ([conformance.malformed-tests](01-conformance.md#conformance.malformed-tests)), and its own tests of malformed annotations.

## Tests and doc examples

<a id="program.test-declarations"></a>
`test "name" { body }` is a top-level item that declares a **test**. Its body is a block of type `()`. It may perform `io`, a `raise<E>` whose `E` implements `Show`, and `async` ([tasks.sequential-run](14-tasks.md#tasks.sequential-run)), but no user-defined effect ([handlers.no-effect-reaches-main](12-effects.md#handlers.no-effect-reaches-main)). Test names are unique within a module, so a second test of one name is a name defined twice (E0208), at its `test` keyword.

Tests: [declarations/tests_raise_showable_errors.lt](../conformance/declarations/tests_raise_showable_errors.lt), [names/defined_twice.lt](../conformance/names/defined_twice.lt), [program/test_body_type.lt](../conformance/program/test_body_type.lt), [program/test_effects.lt](../conformance/program/test_effects.lt), [program/test_names_per_module](../conformance/program/test_names_per_module/).

<a id="program.test-results"></a>
A test passes when its body finishes without raising, panicking or calling `exit`. A panic or an `exit` ends only the test that does it, and the remaining tests still run. A stack overflow or running out of memory ends every test, as it ends a program. `test` then reports no result, writes `fatal: <reason>` to stderr and exits with status 134.

Tests: [declarations/hole_in_test.lt](../conformance/declarations/hole_in_test.lt), [effects/without_panic_tests_assert.lt](../conformance/effects/without_panic_tests_assert.lt), [numerics/shift_amount_edges.lt](../conformance/numerics/shift_amount_edges.lt), [numerics/shift_edges.lt](../conformance/numerics/shift_edges.lt), [numerics/signed_overflow_edges.lt](../conformance/numerics/signed_overflow_edges.lt), [numerics/unsigned_overflow_edges.lt](../conformance/numerics/unsigned_overflow_edges.lt), [program/test_effects.lt](../conformance/program/test_effects.lt), [program/tests_and_examples.lt](../conformance/program/tests_and_examples.lt), [std/bounds_edges.lt](../conformance/std/bounds_edges.lt), [threads/testing.lt](../conformance/threads/testing.lt).

<a id="program.running-tests"></a>
`stilt test` reports a result for every test, doc example and property ([tests.prop-lines](19-tools.md#tests.prop-lines)) of the program's own modules. `stilt check` and `stilt run` run none of them. `stilt test` never runs those of the standard library ([std.examples](17-std.md#std.examples)), nor those of a dependency, a path dependency included ([packages.no-build-time-code](#packages.no-build-time-code)). When the program has errors, it reports them and runs none of its tests.

What tests print isn't part of their result, and `test --json` writes only its JSON object to stdout. An implementation may reuse the cached result of a test whose code and dependencies haven't changed, unless the test's inferred effects include `io`.

Tests: [packages/dependency_tests](../conformance/packages/dependency_tests/), [program/doc_example_errors.lt](../conformance/program/doc_example_errors.lt), [program/doc_examples.lt](../conformance/program/doc_examples.lt), [program/run_skips_tests.lt](../conformance/program/run_skips_tests.lt), [program/tests_and_examples.lt](../conformance/program/tests_and_examples.lt), [protocol/test_lines.lt](../conformance/protocol/test_lines.lt).

<a id="program.test-order"></a>
`stilt test` runs the tests, doc examples and properties of each file in source order, and the files in the order of their paths, as `parse --sexp` prints them.

Checked by: the reference interpreter's tests of `stilt test` (`interpreter/test/test_order.ml`), since what tests print isn't part of their result.

<a id="program.assert-expr"></a>
`assert expr` is a statement that panics with the kind `assert` when `expr` is false.

Tests: [effects/panic_assert.lt](../conformance/effects/panic_assert.lt), [effects/without_panic_tests_assert.lt](../conformance/effects/without_panic_tests_assert.lt), [program/assert.lt](../conformance/program/assert.lt), [program/prelude.lt](../conformance/program/prelude.lt), [program/tests_and_examples.lt](../conformance/program/tests_and_examples.lt).

<a id="program.doc-comments"></a>
A run of `///` comments on consecutive lines, each alone on its line, is a **doc**. It documents the declaration that starts on the next line ([syntax.doc-comment-runs](03-syntax.md#syntax.doc-comment-runs)). That declaration is a function, a type, a trait, a constant, a test, an effect or a macro, at module level or inside an `impl` or `trait` block. Its first line is the declaration's **summary**. A doc comment anywhere else is a syntax error ([syntax.doc-comment-placement](03-syntax.md#syntax.doc-comment-placement)). A doc line's text ends before any `//~` ([syntax.doc-comment-text](03-syntax.md#syntax.doc-comment-text)).

Tests: [lexical/commented_out_code.lt](../conformance/lexical/commented_out_code.lt), [lexical/doc_comment_after_code.lt](../conformance/lexical/doc_comment_after_code.lt), [lexical/four_slashes.lt](../conformance/lexical/four_slashes.lt), [program/misplaced_docs](../conformance/program/misplaced_docs/).

<a id="program.doc-examples"></a>
A doc line whose text, after `///` and any spaces, starts with `ex:` is an **example**. Its text after `ex:` is lexed and parsed as an expression ([syntax.doc-examples](03-syntax.md#syntax.doc-examples)). The expression must have type `bool`, or it is a type mismatch (E0311).

An example is checked as a test body of its module, except that its row must not hold `async` ([tasks.sequential-run](14-tasks.md#tasks.sequential-run)). As in a test body, its names resolve as at module level, it may use `try`, and it is exempt from every `without` limit ([facts.without](15-facts.md#facts.without)). An example passes when it evaluates to `true`. It fails when it evaluates to `false`, raises, panics or calls `exit`.

A doc line that starts with `prop:` is a property, which `stilt test` runs beside the examples ([tests.prop-lines](19-tools.md#tests.prop-lines)).

Tests: [declarations/tests_raise_showable_errors.lt](../conformance/declarations/tests_raise_showable_errors.lt), [lexical/doc_example_malformed_spec.lt](../conformance/lexical/doc_example_malformed_spec.lt), [lexical/doc_property_malformed_spec.lt](../conformance/lexical/doc_property_malformed_spec.lt), [lexical/example_comments.lt](../conformance/lexical/example_comments.lt), [program/doc_example_errors.lt](../conformance/program/doc_example_errors.lt), [program/doc_examples.lt](../conformance/program/doc_examples.lt), [program/tests_and_examples.lt](../conformance/program/tests_and_examples.lt).

## Programs with errors

<a id="program.programs-with-errors"></a>
`run` runs a program that has errors. It first writes the program's diagnostics to stderr, as `check` reports them, in a form each implementation chooses. It then runs `main`, and exits with status 2 however the program ends. Its stdout holds what the program printed, and the reports of [program.exit-statuses](#program.exit-statuses) and [program.panic-report](#program.panic-report) still end its stderr.

A program without `main` has nothing to run ([program.missing-main](#program.missing-main)). A program without errors runs as the rest of this chapter says, whatever its warnings. A hole is a warning, and panics only where it is reached ([declarations.running-holes](10-declarations.md#declarations.running-holes)).

Tests: [program/error_in_main.lt](../conformance/program/error_in_main.lt), [program/error_never_reached.lt](../conformance/program/error_never_reached.lt), [program/flush_with_errors.lt](../conformance/program/flush_with_errors.lt), [program/missing_main.lt](../conformance/program/missing_main.lt), [program/run_with_warnings.lt](../conformance/program/run_with_warnings.lt), [reflection/impl_of_an_unknown_type.lt](../conformance/reflection/impl_of_an_unknown_type.lt).

<a id="program.bodies-with-errors"></a>
Code with an error is replaced by a panic of kind `check-error` ([effects.panic-kinds](12-effects.md#effects.panic-kinds)), raised where the code is reached. The unit replaced is a body ([errors.phases](18-errors.md#errors.phases)) with its declaration. A function or method with an error panics as soon as it is called, so a `main` with one panics as soon as the program starts. A constant with an error panics when it is read.

A body has an error when an error lies in it ([program.errors-in-bodies](#program.errors-in-bodies)) or when it meets the error type ([program.meeting-the-error-type](#program.meeting-the-error-type)). Everything else runs.

Tests: [patterns/broken_module_in_pattern.lt](../conformance/patterns/broken_module_in_pattern.lt), [patterns/shadowed_prelude_name_in_pattern.lt](../conformance/patterns/shadowed_prelude_name_in_pattern.lt), [procedural/reaching_io/main.lt](../conformance/procedural/reaching_io/main.lt), [program/error_in_constant.lt](../conformance/program/error_in_constant.lt), [program/error_in_main.lt](../conformance/program/error_in_main.lt), [program/error_never_reached.lt](../conformance/program/error_never_reached.lt), [program/error_reached_in_function.lt](../conformance/program/error_reached_in_function.lt), [program/limit_error_in_a_body.lt](../conformance/program/limit_error_in_a_body.lt).

<a id="program.errors-in-bodies"></a>
An error lies in a body when its primary span starts in the body's declaration. The declaration runs from the first token of its function, constant or test, after its doc comments, to its last token. A method's declaration also holds the header of the impl around it, from after its `impl` keyword up to its `{`, but no other member of the block. An error at the `impl` keyword is about the impl as a whole, such as a method it lacks (E0305), and lies in none of its members. The error counts whether or not it is reported ([errors.part-reports](18-errors.md#errors.part-reports)), so an error that a syntax error in the same part holds back still counts.

Tests: [program/error_in_constant.lt](../conformance/program/error_in_constant.lt), [program/error_reached_in_function.lt](../conformance/program/error_reached_in_function.lt).

<a id="program.meeting-the-error-type"></a>
A body without an error of its own **meets the error type** ([errors.error-type](18-errors.md#errors.error-type)) in two ways:

- **Names with errors elsewhere.** A name in its declaration, in the header of the impl around it, or in its body stands for nothing because of an error elsewhere. Such a name has the error type, and is one of these:
  - a module that a `use` declaration with an error names;
  - a path into a module whose name is invalid ([program.module-names](#program.module-names));
  - a prelude name that its module shadows ([program.prelude-names](#program.prelude-names));
  - a name that a part with a syntax error leaves with the error type ([program.syntax-errors-at-run](#program.syntax-errors-at-run));
  - a member of an impl that an error keeps out of the program.

  An error keeps an impl out when its type or trait has an error, or when it lies outside the modules that may hold it ([traits.impl-blocks](11-traits.md#traits.impl-blocks), [traits.orphan-rule](11-traits.md#traits.orphan-rule)). A program's impl adds no member to the library's types, so the standard library's code meets no such member.

- **Declarations with error types.** It uses a declaration whose signature holds the error type. It calls or names a function or method whose parameter types, return type or row hold it. It calls or names a trait's method whose declaration in the trait holds it, as the call is checked against that declaration. Or it reads a constant whose type holds it, builds a value of a type whose fields or payloads hold it, or reads or matches such a field or payload.

A body that meets it has an error. No other way leads the error type into a body. So a body without an error checks as it would in a program without errors, and runs.

Tests: [checking/spread_of_a_broken_item.lt](../conformance/checking/spread_of_a_broken_item.lt), [names/item_import](../conformance/names/item_import/), [packages/ungranted_run](../conformance/packages/ungranted_run/), [patterns/broken_module_in_pattern.lt](../conformance/patterns/broken_module_in_pattern.lt), [patterns/prelude_variant_through_type.lt](../conformance/patterns/prelude_variant_through_type.lt), [patterns/shadowed_prelude_name_in_pattern.lt](../conformance/patterns/shadowed_prelude_name_in_pattern.lt), [program/error_in_signature.lt](../conformance/program/error_in_signature.lt), [program/error_in_type.lt](../conformance/program/error_in_type.lt), [program/error_through_import.lt](../conformance/program/error_through_import.lt), [reflection/impl_of_an_unknown_type.lt](../conformance/reflection/impl_of_an_unknown_type.lt)

<a id="program.errors-outside-bodies"></a>
An error in a module header, a `use` declaration, or the declaration of a type or a trait replaces no code by itself. The bodies that meet its error type have errors. So after `type Point = { x: i64, y: Nope }`, a function that takes a `Point` and reads its `x` runs, while one that builds a `Point` or reads its `y` panics. A method that a trait impl lacks (E0305) panics when it is called, as code with an error.

Tests: [program/error_in_type.lt](../conformance/program/error_in_type.lt), [program/error_through_import.lt](../conformance/program/error_through_import.lt), [program/missing_method_reached.lt](../conformance/program/missing_method_reached.lt).

<a id="program.syntax-errors-at-run"></a>
A file with a syntax error is read a part at a time ([syntax.parts](03-syntax.md#syntax.parts)). Each function, constant and test that a part that breaks declares has an error. A name that the part leaves with the error type is a name with an error elsewhere, for the bodies that use it. A syntax error lies in no body by its span. So the part that breaks where a `}` was left out ends before the next declaration, which runs.

Tests: [program/syntax_error_in_constant.lt](../conformance/program/syntax_error_in_constant.lt), [program/syntax_error_in_exported_function.lt](../conformance/program/syntax_error_in_exported_function.lt), [program/syntax_error_in_function.lt](../conformance/program/syntax_error_in_function.lt), [program/syntax_error_in_method.lt](../conformance/program/syntax_error_in_method.lt), [program/syntax_error_in_type.lt](../conformance/program/syntax_error_in_type.lt).

<a id="program.check-error-report"></a>
A `check-error` panic is located at the name of its function, method or constant, or at the `impl` keyword of the impl that lacks the method. Its detail is up to the implementation, as for every kind but `explicit` ([program.panic-detail](#program.panic-detail)).

Tests: [patterns/broken_module_in_pattern.lt](../conformance/patterns/broken_module_in_pattern.lt), [patterns/shadowed_prelude_name_in_pattern.lt](../conformance/patterns/shadowed_prelude_name_in_pattern.lt), [program/error_in_constant.lt](../conformance/program/error_in_constant.lt), [program/error_in_signature.lt](../conformance/program/error_in_signature.lt), [program/error_in_type.lt](../conformance/program/error_in_type.lt), [program/error_through_import.lt](../conformance/program/error_through_import.lt), [program/missing_method_reached.lt](../conformance/program/missing_method_reached.lt), [program/syntax_error_in_exported_function.lt](../conformance/program/syntax_error_in_exported_function.lt), [program/syntax_error_in_method.lt](../conformance/program/syntax_error_in_method.lt).

## Packages

<a id="packages.manifest"></a>
A package's **manifest**, `stilt.toml`, is a TOML 1.0 document with at most two tables, `[package]` and `[dependencies]`. A file that isn't TOML 1.0 is E0600, *malformed manifest*. So is any other table or key, and a value of a type or a form other than this chapter gives. An empty file is a manifest with no name and no dependencies.

Tests: [packages/manifest_empty](../conformance/packages/manifest_empty/), [packages/manifest_named](../conformance/packages/manifest_named/), [packages/manifest_not_toml_with_use](../conformance/packages/manifest_not_toml_with_use/), [packages/manifest_unknown_keys](../conformance/packages/manifest_unknown_keys/), [packages/manifest_unknown_table](../conformance/packages/manifest_unknown_table/), [packages/manifest_wrong_types](../conformance/packages/manifest_wrong_types/), [program/package_manifest_not_toml](../conformance/program/package_manifest_not_toml/).

<a id="packages.package-table"></a>
`[package]` holds three keys:

- `name`, a string that is a valid first segment of a module's name ([program.module-names](#program.module-names)) other than `main`;
- `edition`, the edition that the package's files are read with ([editions.edition](#editions.edition));
- `link`, the C libraries that its foreign functions need ([c.linking](20-builds.md#c.linking)).

Any other key, and any other name, is E0600. A package that only runs needs no name. A package that another package depends on must have one (E0603, [packages.dependency-names](#packages.dependency-names)).

Tests: [packages/dependency_names](../conformance/packages/dependency_names/), [packages/manifest_named](../conformance/packages/manifest_named/), [packages/manifest_unknown_keys](../conformance/packages/manifest_unknown_keys/), [packages/manifest_wrong_types](../conformance/packages/manifest_wrong_types/), [packages/name_capitalized](../conformance/packages/name_capitalized/), [packages/name_keyword](../conformance/packages/name_keyword/), [packages/name_main](../conformance/packages/name_main/), [packages/name_std](../conformance/packages/name_std/).

<a id="packages.dependencies"></a>
Each key of `[dependencies]` names a **dependency**. Its value is an inline table or a table of its own, as `[dependencies.json]`, and holds these keys:

| Key | Value |
| --- | --- |
| `path` | The directory that holds the dependency, relative to the manifest's directory, with `/` as the separator |
| `from` | The git repository that holds it: `HOST/PATH`, fetched from `https://HOST/PATH`, whose host may give a port, as `HOST:PORT`, or a `file://` URL that names a repository on the machine |
| `version` | Its version, `MAJOR.MINOR.PATCH`: three decimal numbers without leading zeros |
| `hash` | Its content hash ([packages.content-hash](#packages.content-hash)): `b3:` and 64 lowercase hexadecimal digits |
| `may` | What it is granted ([packages.grants](#packages.grants)), as a list of strings |

A value of another form than the table gives, as a `version` with a leading zero, is E0600. An entry holds `path` or `from`, not both. `version` and `hash` go only with `from`, and `hash` only with `version`. Any other combination is E0600.

Tests: [packages/entry_sources](../conformance/packages/entry_sources/), [packages/manifest_unknown_keys](../conformance/packages/manifest_unknown_keys/), [packages/manifest_wrong_types](../conformance/packages/manifest_wrong_types/), [packages/path_of_path](../conformance/packages/path_of_path/).

<a id="packages.dependency-names"></a>
An entry's key is the dependency's name, which must be the name that the dependency's own manifest gives it. An entry named otherwise is E0603, *dependency named unlike its package*, at the entry's key. So is a dependency whose manifest gives no name. A package therefore has one name wherever it is used.

Tests: [packages/dependency_names](../conformance/packages/dependency_names/).

<a id="packages.path-dependencies"></a>
A `path` dependency is the package in that directory, as it is, with no version and no hash. Only the root package and its path dependencies may have path dependencies. A fetched package is built from its own content alone. So each entry of its manifest gives `from`, `version` and `hash`, or the package can't be built ([packages.fetch-failures](#packages.fetch-failures)).

Tests: [packages/path_of_path](../conformance/packages/path_of_path/), [packages/path_without_package](../conformance/packages/path_without_package/).

<a id="packages.manifest-diagnostics"></a>
A manifest's diagnostic is placed in the manifest, as `stilt.toml:5:1`. An error about an entry is at the entry's key. The key is the one before its `=`, or the name in its header `[dependencies.NAME]` when the entry is a table of its own. E0600 is at the key or the value it is about. For a file that isn't TOML 1.0, E0600 is at the first character from which no TOML document can continue. An error that this chapter places at an entry of the root's manifest is at that entry's key too.

Tests: [packages/entry_sources](../conformance/packages/entry_sources/), [packages/grant_values](../conformance/packages/grant_values/), [packages/manifest_unknown_keys](../conformance/packages/manifest_unknown_keys/), [packages/ungranted_in_middle](../conformance/packages/ungranted_in_middle/).

## Fetched dependencies

<a id="packages.versions"></a>
A version of a `from` repository is a tag `vMAJOR.MINOR.PATCH` of it, and no other tag is a version. The package is the repository's tree at that tag, with its manifest at the root. Versions are ordered by their major number, then their minor, then their patch.

Checked by: the toolchain's tests of versions (`compiler/stilt-cli/tests/versions.rs`) and `compiler/stilt-pkg/src/version.rs`, since only repositories have versions.

<a id="packages.content-hash"></a>
A package's **content hash** covers its manifest and the files of its modules ([program.module-names](#program.module-names)), which are all that building it reads. It takes a line for each of these files, in the byte order of its path from the package's root, written with `/`. The line is the 64 lowercase hexadecimal digits of the BLAKE3 digest of the file's bytes, two spaces, the path and `\n`. The content hash is the BLAKE3 digest of those lines, written `b3:` and 64 lowercase hexadecimal digits.

Checked by: the toolchain's tests of fetched dependencies, which serve local repositories by `file://` (`compiler/stilt-cli/tests/fetched.rs`), and `compiler/stilt-pkg/src/hash.rs`.

<a id="packages.filling-in"></a>
Every command that reads a package's dependencies fills in the entries that need it:

- **`from` alone.** It fetches the repository, takes its highest version, checks it ([versions.checked-versions](21-versions.md#versions.checked-versions)), and writes `version` and `hash` into the entry.
- **`from` and `version`.** It fetches that version, checks it, and writes `hash` into the entry.
- **All three.** It never changes the entry. To move to another version, the manifest's author writes the new `version`, or removes it, and removes `hash`.

It changes nothing else in the manifest. It writes the root's manifest and those of its path dependencies, never a fetched package's. A `check` or `test` whose edits are refused writes no file ([edits.all-or-nothing](19-tools.md#edits.all-or-nothing)), so it fills in nothing.

Checked by: the toolchain's tests of fetched dependencies (`compiler/stilt-cli/tests/fetched.rs`).

<a id="packages.fetch-report"></a>
A command reports each package it fetched, with its version and hash, on stderr. With `--json`, it reports them in the list `fetched` of the object it writes, as objects with the fields `name`, `from`, `version` and `hash`.

Checked by: the toolchain's tests of fetched dependencies (`compiler/stilt-cli/tests/fetched.rs`).

<a id="packages.fetching"></a>
A command fetches only the packages it doesn't hold. It keeps fetched packages in a cache keyed by their hashes, in the directory that `STILT_HOME` names, or else in `.stilt` in the home directory. It reaches `HOST/PATH` over HTTPS by git's smart HTTP protocol by itself, and needs nothing else installed. It trusts Mozilla's root certificates, which it holds, the system's, and those of the file that `SSL_CERT_FILE` names. It takes at most 1 GiB in one answer from a server, and reads objects of at most 1 GiB, each stored whole or at the end of a chain of at most 4,095 deltas, as git writes them; a pack past those limits, or one that isn't well formed, is a dependency that can't be fetched ([packages.fetch-failures](#packages.fetch-failures)).

Checked by: the toolchain's tests of fetched dependencies (`compiler/stilt-cli/tests/fetched.rs`), of fetching over HTTPS from a local server with a test certificate authority (`compiler/stilt-cli/tests/https.rs`), and of reading corrupt and hostile packs (`compiler/stilt-pkg/tests/packs.rs`).

<a id="packages.checked-content"></a>
A command computes a package's content hash each time it reads the package, from the cache or from the network. Content whose hash isn't the one that a manifest gives it is E0602, *content that doesn't match its hash*, and nothing is built from it. Two hashes that two manifests give one version are E0602 too ([versions.selection](21-versions.md#versions.selection)). E0602 is at the `hash` value that the content doesn't match, when the root's manifest or a path dependency's gives it. Otherwise it is at the first entry of the root's manifest through which the package arrives.

Checked by: the toolchain's tests of fetched dependencies, a cache entry changed on disk and a retagged version (`compiler/stilt-cli/tests/fetched.rs`, `compiler/stilt-cli/tests/https.rs`).

<a id="packages.fetch-failures"></a>
A dependency that can't be had is E0601, *dependency that can't be fetched*. It is one of these:

- a `path` that names no directory holding a `stilt.toml`;
- a repository that can't be reached or has no version;
- a version that a repository doesn't have, or sends past the limits of [packages.fetching](#packages.fetching) or not well formed;
- a version whose tree holds no `stilt.toml` at its root;
- a fetched package whose manifest has a `path` entry, or a `from` entry without its `version` or `hash`, which can't be built from its content.

E0601 is at the entry's key in the manifest that holds it. For a fetched package that can't be built from its content, it is at the first entry of the root's manifest through which the package arrives.

Tests: [packages/path_without_package](../conformance/packages/path_without_package/).

Checked by: also the toolchain's tests of fetched dependencies (`compiler/stilt-cli/tests/fetched.rs`, `compiler/stilt-cli/tests/https.rs`).

## Dependencies in a program

<a id="packages.modules-of-dependencies"></a>
A program's modules are its own and those of every package it depends on. In a package that depends on a package `D`, the module `main` of `D` is named `D`, and the module `a.b` of `D` is named `D.a.b`. Inside `D`, they keep their names. So after `use json.decode`, `decode.parse(text)` calls the function `parse` of the file `src/decode.lt` of the package `json`. An item `x` of the module `main` of `D` hides the module `x` of `D` from the packages that depend on `D` ([program.child-modules](#program.child-modules)).

Tests: [packages/module_named_like_indirect_dependency](../conformance/packages/module_named_like_indirect_dependency/), [packages/module_names](../conformance/packages/module_names/), [packages/path_of_path](../conformance/packages/path_of_path/), [packages/private_item](../conformance/packages/private_item/).

<a id="packages.imports"></a>
A module's `use` declarations and paths may name modules of its own package, of `std`, and of the packages that its package's manifest names as dependencies. Naming a module of another package of the program, such as a dependency of a dependency, is E0218, *package that isn't a dependency*, at the `use` or the path. Its fix adds the entry, with the `from` and `version` of the manifest that names that package. A `use` that names a module of no package is E0205 ([program.namespaces](#program.namespaces)), whose message lists the manifest's dependencies.

A module of a package whose name has a dependency's name as its first segment is invalid (E0200, [program.module-names](#program.module-names)). So `src/json.lt`, in a package that depends on `json`, can't be named.

Tests: [packages/dependency_of_dependency](../conformance/packages/dependency_of_dependency/), [packages/misspelled_dependency](../conformance/packages/misspelled_dependency/), [packages/module_named_like_dependency](../conformance/packages/module_named_like_dependency/), [packages/module_named_like_indirect_dependency](../conformance/packages/module_named_like_indirect_dependency/), [packages/module_names](../conformance/packages/module_names/).

<a id="packages.one-name-one-package"></a>
Two packages of one name in a program are E0606, *two packages with one name*. They may come from two repositories, from a repository and a directory, or from two directories. E0606 is at the first entry of the root's manifest that, with the entries before it, brings both.

Tests: [packages/two_packages_one_name](../conformance/packages/two_packages_one_name/).

<a id="packages.dependency-cycles"></a>
A package that depends on itself is E0609, *dependency cycle*. The cycle runs through its own manifest or through those of the packages it names, at the versions selected. E0609 is at the first entry of the root's manifest through which a package of the cycle arrives.

Tests: [packages/cycle_of_two](../conformance/packages/cycle_of_two/), [packages/cycle_through_root](../conformance/packages/cycle_through_root/).

Checked by: also the toolchain's tests of versions, a version that depends on an earlier version of its own repository (`compiler/stilt-cli/tests/versions.rs`).

<a id="packages.dependencies-with-errors"></a>
A path dependency is checked as part of the program. Its files are among the program's own, its diagnostics are reported in them, at paths relative to the root directory, and its parts take edits ([edits.parts](19-tools.md#edits.parts)).

A fetched dependency is checked with the program too, against the versions that the program selects ([versions.selection](21-versions.md#versions.selection)). Its diagnostics, those of its code and of its manifest, aren't reported. Each fetched dependency that has an error gives the program one E0607, *dependency with errors*, at the first entry of the root's manifest through which it arrives. None of its warnings is reported. Wherever the program uses an item of a dependency whose declaration has an error, the item has the error type.

Tests: [packages/dependency_errors](../conformance/packages/dependency_errors/), [packages/granted_macro_run](../conformance/packages/granted_macro_run/).

Checked by: also the toolchain's tests of versions, for fetched dependencies (`compiler/stilt-cli/tests/versions.rs`).

<a id="packages.manifests-with-errors"></a>
A dependency entry with an error other than E0607 and E0608 still declares its name. A `use` or a path that names a module of it has the error type. A manifest that isn't TOML 1.0, or whose `[dependencies]` isn't a table, declares no dependency. A `use` or a path that names a module of no package of the program then has the error type. Neither is a further error.

An E0607 or an E0608 leaves its entry's package in the program. Which of its items have errors is decided by [packages.dependencies-with-errors](#packages.dependencies-with-errors) and [packages.running-with-ungranted-effect](#packages.running-with-ungranted-effect).

Tests: [packages/cycle_of_two](../conformance/packages/cycle_of_two/), [packages/cycle_through_root](../conformance/packages/cycle_through_root/), [packages/manifest_not_toml_with_use](../conformance/packages/manifest_not_toml_with_use/), [packages/two_packages_one_name](../conformance/packages/two_packages_one_name/).

## Granted effects

<a id="packages.grants"></a>
A dependency's entry grants it what its `may` lists, and nothing when it has no `may`. Each string of `may` is one of these:

- `io`, which grants every capability and `io` without one;
- one of the eight capabilities, which grants that capability ([facts.capability-grants](15-facts.md#facts.capability-grants));
- `unsafe`, which grants C code ([c.granting-unsafe](20-builds.md#c.granting-unsafe)).

Any other string is E0600, and so are a string listed twice and `io` listed with a capability. A raise needs no grant. Neither do `panic`, `alloc` and the other facts, which `without` limits ([facts.without](15-facts.md#facts.without)).

Tests: [packages/grant_values](../conformance/packages/grant_values/), [packages/granted_macro_run](../conformance/packages/granted_macro_run/), [packages/granted_print](../conformance/packages/granted_print/), [packages/ungranted_print](../conformance/packages/ungranted_print/).

<a id="packages.own-effects"></a>
A package's **own code** is its functions and methods, and the closure literals in them. Its own code performs `io` when it calls a function of another package whose declared row holds `io`, or names one as a value. `std` is another package here. A call of a trait method names an impl's method as [facts.inference](15-facts.md#facts.inference) says.

A call through a function value adds nothing, whether the value is a parameter, a field, a local or a bound. So the effects that reach a package's code from a function that its caller gives it are the caller's, and need no grant ([facts.calls-through-function-values](15-facts.md#facts.calls-through-function-values)). Test bodies, doc examples and properties don't count. Nor does a body with an error, which panics with `check-error` instead of running ([program.bodies-with-errors](#program.bodies-with-errors)). A package's own capabilities and its own `unsafe` blocks are counted the same way ([facts.own-capabilities](15-facts.md#facts.own-capabilities), [c.unsafe-in-api](20-builds.md#c.unsafe-in-api)).

Tests: [capabilities/own_impl](../conformance/capabilities/own_impl/), [packages/callback_effects](../conformance/packages/callback_effects/), [packages/closure_and_value](../conformance/packages/closure_and_value/), [packages/granted_print](../conformance/packages/granted_print/), [packages/test_prints](../conformance/packages/test_prints/), [packages/ungranted_print](../conformance/packages/ungranted_print/), [packages/ungranted_trait](../conformance/packages/ungranted_trait/), [packages/ungranted_with_type_error](../conformance/packages/ungranted_with_type_error/).

<a id="packages.ungranted-effects"></a>
A dependency whose own code performs an effect that its entry doesn't grant is E0608, *effect that the manifest doesn't grant*, at its entry, once for each effect. So is a dependency whose own code has a capability that its entry doesn't grant ([facts.ungranted-capabilities](15-facts.md#facts.ungranted-capabilities)), or holds an `unsafe` block without the grant ([c.granting-unsafe](20-builds.md#c.granting-unsafe)).

The error names the first function that performs the effect by its address ([edits.paths](19-tools.md#edits.paths)), with the call that performs it, and offers the narrowest grant. That function is the first in the order of the dependency's modules' paths, and then of its source. This holds for the entries of the root's manifest and of its path dependencies' manifests, in their own files. A fetched package's manifest is checked as part of that package ([packages.dependencies-with-errors](#packages.dependencies-with-errors)).

Tests: [packages/callback_effects](../conformance/packages/callback_effects/), [packages/closure_and_value](../conformance/packages/closure_and_value/), [packages/ungranted_in_middle](../conformance/packages/ungranted_in_middle/), [packages/ungranted_print](../conformance/packages/ungranted_print/), [packages/ungranted_quote](../conformance/packages/ungranted_quote/), [packages/ungranted_trait](../conformance/packages/ungranted_trait/).

<a id="packages.running-with-ungranted-effect"></a>
A manifest, the root's or a dependency's, can fail to grant a dependency an effect, a capability or `unsafe` that the dependency's own code has. When `run` runs such a program, each function of that dependency whose own code has it is code with an error ([program.bodies-with-errors](#program.bodies-with-errors)), and panics with `check-error` when it is called. That manifest has an E0608. When it is a fetched package's manifest, the program has that package's E0607 instead. So no command performs an effect that a manifest doesn't grant.

Tests: [packages/ungranted_macro_run](../conformance/packages/ungranted_macro_run/), [packages/ungranted_run](../conformance/packages/ungranted_run/).

Checked by: also the toolchain's tests of versions, a fetched manifest that doesn't grant its own dependency `io` (`compiler/stilt-cli/tests/versions.rs`).

<a id="packages.no-build-time-code"></a>
Fetching, checking and building a program run none of its dependencies' code but their procedural macros ([macros.running](16-meta.md#macros.running)), which perform nothing ([macros.procedural-bodies](16-meta.md#macros.procedural-bodies)). A package has no build script. `stilt test` runs only the tests, examples and properties of the root package's own modules, never those of a dependency, a path dependency included. So a dependency's code reaches the world only when the running program, or one of those tests, calls it.

Tests: [packages/dependency_tests](../conformance/packages/dependency_tests/).

## Editions

<a id="editions.edition"></a>
`[package]` holds a key `edition`, a string that names the **edition** the package's files are read with, as `edition = "2027"`. The editions are 2027 alone. Any other string, and a value of another type, is E0600. A package whose manifest has no `edition` is of the first edition, 2027, and so is a program with no manifest. The edition is part of the manifest, not of the package's API ([versions.edition](21-versions.md#versions.edition)).

Tests: [editions/edition_absent](../conformance/editions/edition_absent/), [editions/edition_integer](../conformance/editions/edition_integer/), [editions/edition_named](../conformance/editions/edition_named/), [editions/edition_unknown](../conformance/editions/edition_unknown/).

<a id="editions.what-an-edition-changes"></a>
An edition may change what a package's own files mean: what parses, which words are keywords, and the names by which they reach the items of `std`. It never changes what an item of `std` does, nor how the packages of a program reach each other's items. Each package's files are read with its own edition, and an item means the same whichever edition names it. So packages of every edition make one program, and a package's dependencies keep their editions when it moves to another.

Checked by: the toolchain's tests of `stilt migrate` (`compiler/stilt-cli/src/migrate/tests.rs`), with a second edition that only they define.

<a id="editions.only-editions-break"></a>
An edition is the only way in which the language breaks a program that an earlier release of the toolchain accepted. Only a January release introduces one, named for its year, and a year with nothing to break introduces none. A package keeps its edition until its author moves it ([editions.migrate](#editions.migrate)), so every release keeps every program of every edition ([versions.programs-kept](21-versions.md#versions.programs-kept)).

Checked by: no program, since it governs the toolchain's releases.

<a id="editions.renames"></a>
An edition may rename methods of the types of `std`. In a package of that edition or a later one, the method is written by its new name, and its old name names nothing. A call `xs.old(…)` is E0314 ([traits.method-resolution](11-traits.md#traits.method-resolution)). Its message says which edition renames `old` to `new`, and its fix writes the new name. Edition 2027 renames nothing.

Checked by: the toolchain's tests of `stilt migrate` (`compiler/stilt-cli/src/migrate/tests.rs`), with a second edition that only they define.

<a id="editions.migrate"></a>
`stilt migrate [PATH]` moves the package at `PATH`, by default the working directory, to the newest edition:

- It checks the package as it is. With an error, it prints the errors, writes nothing and exits with status 1.
- For each edition after the package's, in order, it rewrites each use of a method that the edition renames to its new name. It then writes the edition into the manifest: in place of the old value, or as a line `edition = "…"` after `name`, or after the `[package]` header.
- It checks the rewritten package with its new edition. Its report names each file it rewrote, with the line and what it wrote, as `src/main.lt:14: includes, for contains`. The report ends with `csvq: edition 2027 → 2028, 1 file rewritten`.
- A package at the newest edition is left as it is, with `csvq: edition 2027, the newest`. A program with no manifest is no package: `migrate` says so and exits with status 2.

Checked by: the toolchain's tests of `stilt migrate` (`compiler/stilt-cli/src/migrate/tests.rs`).

## Pinned docs

<a id="docs.pins"></a>
A declaration's doc ([program.doc-comments](#program.doc-comments)), its examples and properties included, is **pinned** to the declaration's signature by a line of `docs.lock`. The line holds the declaration's path ([edits.paths](19-tools.md#edits.paths)), a space, `#` and the hash of its signature, a space, and `#` and the hash of its doc, as `main.weight #3c2e #a91f`. Each hash is that of [edits.hash](19-tools.md#edits.hash), of the text that [docs.pinned-texts](#docs.pinned-texts) gives.

A declaration with a syntax error has no canonical text ([edits.files-with-syntax-errors](19-tools.md#edits.files-with-syntax-errors)), so it has no pin. A path that names two declarations ([edits.one-part-per-path](19-tools.md#edits.one-part-per-path)) names neither alone, so neither has a pin.

Checked by: the toolchain's tests of pins (`compiler/stilt-cli/tests/docs_lock.rs` and `compiler/stilt-edit/src/pins.rs`), since no conformance test holds a `docs.lock` ([docs.warnings-in-conformance](#docs.warnings-in-conformance)).

<a id="docs.pinned-texts"></a>
The **doc's text** is its lines as the declaration's canonical text ([edits.canonical-text](19-tools.md#edits.canonical-text)) writes them, joined by `\n`. The **signature's text** is the canonical text of the declaration with each body it holds written `{}`. It holds no doc: neither its own nor those of the methods a trait declares. The bodies it holds are its own body and the default bodies of a trait's methods.

So the signature of `fn weight(o: Order, unit: Unit) -> f64 { … }` is `fn weight(o: Order, unit: Unit) -> f64 {}`, and a type has no body to leave out. Formatting a file never changes a pin's hashes, and editing a body never changes its declaration's signature.

Checked by: the toolchain's tests of pins (`compiler/stilt-edit/src/pins.rs`), the signature's text of each kind of declaration.

<a id="docs.lock-file"></a>
A package has one `docs.lock`, at its root, beside its manifest, and it is committed with the package. It holds one line for each pin, each ending in `\n`, sorted by the bytes of their paths, and nothing else. A package with no pin has no `docs.lock`.

A pin's path is the one that the package's own module has when the package is the root. So a dependency's module is named in it without the dependency's name ([packages.modules-of-dependencies](#packages.modules-of-dependencies)). A line of another form, or whose path names no declaration with a doc, pins nothing.

A single file or a directory program has no `docs.lock`, and its docs are never pinned. A fetched package's `docs.lock` is never read or written, and it isn't part of the content hash ([packages.content-hash](#packages.content-hash)).

Checked by: the toolchain's tests of pins (`compiler/stilt-cli/tests/docs_lock.rs`).

<a id="docs.stale"></a>
A doc is **stale** when its pin's signature hash isn't its signature's hash now, while its pin's doc hash is its doc's hash now. `check` and `test` report each stale doc as W0002, *stale doc*, at the doc's first line. W0002 is a warning outside bodies, reported whenever the program has no syntax error, in a declaration with errors too ([errors.phases](18-errors.md#errors.phases)).

A doc without a pin is never stale. Neither is a doc whose hash isn't its pin's, whatever its signature. W0002's fix pins again a doc that is still right: an edit of the declaration through `check --edit` ([edits.fixes-as-edits](19-tools.md#edits.fixes-as-edits)), which sends it back as it is.

Checked by: the toolchain's tests of pins (`compiler/stilt-cli/tests/docs_lock.rs`) and W0002's snapshot in `tests/diagnostics/`, which `just diagnostics` checks.

<a id="docs.writing-pins"></a>
Every command that writes source writes `docs.lock`:

- `stilt fmt`, for the package that its path lies in: the nearest directory with a manifest that is the path or holds it;
- `check` and `test` when they apply edits ([edits.writing](19-tools.md#edits.writing)), for the package of each file they edit.

Once its files are written, the command pins each declaration of the package that has a doc:

- a doc without a pin is pinned, with the current hashes of its signature and its doc;
- a doc whose hash isn't its pin's is pinned again, with both current hashes;
- a doc whose declaration, not its body, an edit of the command replaces is pinned again if the new text keeps the signature and the doc;
- every other pin stays as it is, a stale one included.

A pin whose path names no declaration with a doc goes, unless the declaration has a syntax error, whose pin stays. `check` and `test` without edits never write `docs.lock`. Nor does a command whose edits are refused, which writes no file ([edits.all-or-nothing](19-tools.md#edits.all-or-nothing)). Between reading `docs.lock` and writing it, no other command writes it.

Checked by: the toolchain's tests of pins (`compiler/stilt-cli/tests/docs_lock.rs`).

## Duplicate bodies

<a id="docs.bodies-compared"></a>
The bodies compared are the bodies of functions and methods that are blocks, in the program's own modules: those whose diagnostics are reported. The bodies of the standard library and of a fetched package aren't compared ([packages.dependencies-with-errors](#packages.dependencies-with-errors)). A body in which phase 1 or 2 finds an error ([errors.phases](18-errors.md#errors.phases)) isn't compared, and neither is a procedural macro's body ([macros.procedural-bodies](16-meta.md#macros.procedural-bodies)). A test's body, a constant's initializer, a doc example and a property aren't compared.

Tests: [hygiene/copies.lt](../conformance/hygiene/copies.lt), [hygiene/copy_with_error.lt](../conformance/hygiene/copy_with_error.lt), [hygiene/methods.lt](../conformance/hygiene/methods.lt), [hygiene/not_functions.lt](../conformance/hygiene/not_functions.lt), [procedural/copies.lt](../conformance/procedural/copies.lt).

<a id="docs.body-size"></a>
A body is compared when it holds at least 20 tokens, from its `{` to its `}`, as the lexer reads them ([lexical.tokens](02-lexical.md#lexical.tokens)). Comments don't count, and neither do separators, written `;` or inserted. A string literal counts as one token, even when it interpolates. So `{ x }`, of 3 tokens, is never compared, and neither is `{ o.qty * 2 + o.extra }`, of 11.

Tests: [hygiene/sizes.lt](../conformance/hygiene/sizes.lt), [hygiene/strings.lt](../conformance/hygiene/strings.lt).

Checked by: also the reference interpreter's tests (`interpreter/test/test_phases_copies.ml`).

<a id="docs.same-body"></a>
Two bodies are the **same** when their typed bodies are. A typed body is the body as type checking elaborates it. The two are compared with each one's parameters and locals numbered in the order they are bound, its parameters first, so their names never matter. They must have:

- each construct the same, with the same literals, operators, fields, modes of arguments and format specs. So a field punned and the same field written out, which `stilt fmt` makes one text, are one.
- each name, method, variant and record type referring to the same declaration. So one text that calls different functions in two modules isn't a copy.
- each local, literal and type argument of the same type, with type parameters compared by name and function types without their rows. So `x * x + 1` with `x: i64` and with `x: i32` aren't one.

Tests: [hygiene/copies.lt](../conformance/hygiene/copies.lt), [hygiene/copies_across_modules](../conformance/hygiene/copies_across_modules/), [hygiene/layout.lt](../conformance/hygiene/layout.lt), [hygiene/methods.lt](../conformance/hygiene/methods.lt), [hygiene/renamed.lt](../conformance/hygiene/renamed.lt), [hygiene/typed.lt](../conformance/hygiene/typed.lt).

<a id="docs.duplicate-bodies"></a>
Of the bodies that are the same, the **first** is the one that comes first in the program. It is in the file whose path sorts first by bytes, then at the first position in it. The later ones are those at which an error of several places is reported ([errors.several-places](18-errors.md#errors.several-places)). Each later one is W0302, *duplicate body*, at its function's name, naming the first by its path ([edits.paths](19-tools.md#edits.paths)). It is a warning of phase 3 of the later body, and neither body has an error ([docs.bodies-compared](#docs.bodies-compared)). Three copies give two W0302, each naming the first.

Tests: [hygiene/copies.lt](../conformance/hygiene/copies.lt), [hygiene/copies_across_modules](../conformance/hygiene/copies_across_modules/), [hygiene/methods.lt](../conformance/hygiene/methods.lt), [hygiene/three_copies.lt](../conformance/hygiene/three_copies.lt), [procedural/copies.lt](../conformance/procedural/copies.lt).

<a id="docs.duplicate-body-fix"></a>
W0302 offers a fix when two conditions hold:

- The two functions have the same signature but for their names and their parameters' names. They have the same generics with their bounds, the same modes, types and `escaping` marks of parameters, the same return type and the same row.
- The later's module can call the first without a new `use`. The first is a function of the later's own module or of an inherent impl in it. Or it is a `pub` function of a module that the later's module imports, whose type is `pub` too when it is a member of an impl. No parameter of the later has the name that the call starts with.

The fix replaces the later body with a call of the first, with the later's parameters in order. Each is marked `inout` where it is an `inout` parameter, and the call is marked with `try` when the row raises: `{ mass(p) }`, `{ orders.mass(p) }`, `{ Point.norm(self) }` or `{ try parse(text) }`.

Checked by: `just diagnostics`, which applies the fix in W0302's snapshots in `tests/diagnostics/` and checks that no diagnostic is left, since a conformance test's results carry no fixes.

<a id="docs.warnings-in-conformance"></a>
W0302 depends on the program alone, so it is part of conformance. The reference interpreter and the compiler both report it, and conformance tests expect it. W0002 depends on `docs.lock`, the toolchain's record of what each doc was written against, which isn't part of the program. No conformance test holds one, and the reference interpreter never reads it.

Tests: [hygiene/copies.lt](../conformance/hygiene/copies.lt).

## Rendered documentation

<a id="docs.stilt-doc"></a>
`stilt doc [PATH]` writes, as HTML, the documentation of the root package of the program at `PATH`, or of the working directory when no `PATH` is given. It writes these files:

- `index.html`, which names the package and lists its modules, each with its tier and the first line of its description;
- a page for each of its modules, `ADDRESS.html`;
- `style.css`.

A module's address is the package's name for its module `main`. For any other module, it is that name followed by `.` and the module's name, as a program that depends on the package names them ([packages.modules-of-dependencies](#packages.modules-of-dependencies)). A dependency's modules have no pages. The package's name is the one its manifest gives. A program without such a name takes its directory's name, or its file's name without `.lt`.

The pages are written into `doc` in the package's root: the directory of its manifest, the directory program itself, or a file program's directory. With `-o DIR`, they are written into `DIR` instead, which is created. The command prints the path of `index.html`. A program with an error is refused with the code and place of its first error, with exit status 2, and its documentation isn't written.

Checked by: the toolchain's tests of rendered docs (`compiler/stilt-cli/tests/doc.rs`).

<a id="docs.module-pages"></a>
A module's page shows its address and tier ([program.module-tier](#program.module-tier)), its description, and each of its `pub` declarations in the order of its file. A module's **description** is the run of `//` comment lines that its file starts with, after its header if it writes one. The declarations shown are its types, traits, functions, constants, effects and macros. Each shows its signature as `stilt show` prints it, the declaration's text without its doc and its body, and then its doc, with each example and property shown as code.

A function's signature is followed by its limitable facts, those that its package's API holds ([versions.limitable-facts](21-versions.md#versions.limitable-facts)). They are in the order that `stilt show` prints them, as `[panic, alloc]`, and a function without one shows `[]`.

Under a type are the `pub` members of the module's inherent impls for it, each as a function. They are followed by the first line of each of the module's trait impls for it, as `impl Show for Point`. Under a trait are its methods, each with the facts of its default body, and none for a method without one. Private declarations, tests, imports and bodies have no place on a page.

Checked by: the toolchain's tests of rendered docs (`compiler/stilt-cli/tests/doc.rs`).

<a id="docs.markdown"></a>
The text of a doc and of a description is Markdown. A page renders its paragraphs, lists whose items start with `-`, fenced code blocks, code spans, emphasis, strong emphasis and links. It shows any other text as it is.

Checked by: the toolchain's tests of rendered docs (`compiler/stilt-cli/tests/doc.rs`), which check Markdown rendered and HTML escaped.

<a id="docs.json"></a>
With `--json`, `stilt doc` writes no file and prints the pages as one JSON object, `{"package": NAME, "modules": [MODULE, …]}`. Each module is `{"address", "tier", "description", "items"}`, and each item is `{"kind", "name", "signature", "facts", "doc", "examples", "members"}`. In an item:

- `kind` is `type`, `trait`, `fn`, `const`, `effect`, `macro` or `impl`;
- `doc` is the text of the doc's lines joined by newlines;
- `examples` is the text of each example and property;
- `members` is the items under it.

Checked by: the toolchain's tests of rendered docs (`compiler/stilt-cli/tests/doc.rs`).

<a id="docs.std"></a>
`stilt doc --std` documents the standard library in place of a program. It writes the pages of a package named `std` whose modules are the library's, each at its own name, as `std.fs`. The pages are written into `doc` in the working directory, or into the directory that `-o DIR` names, or printed with `--json`. Each page is a module's page ([docs.module-pages](#docs.module-pages)), with the library's own examples ([std.examples](17-std.md#std.examples)) and the facts of its native functions ([facts.native-allocation](15-facts.md#facts.native-allocation), [facts.capability-natives](15-facts.md#facts.capability-natives)).

The built-in types have no declaration, and their home is `std.prelude` ([traits.impl-blocks](11-traits.md#traits.impl-blocks)). They are on the page of `std.prelude`, after its declarations, in the order of their first inherent impl. Each is an item of kind `type` whose signature is the type as that impl writes it, as `List<T>`, with no doc. The `pub` members of the module's inherent impls for it are under it.

Checked by: the toolchain's tests of rendered docs (`compiler/stilt-cli/tests/doc.rs`).
