# 18. Programs with errors

This chapter says which diagnostics an implementation reports for a program with mistakes, and what the rest of such a program means. A file with a syntax error is read a part at a time. A name or an expression with an error gets the error type, from which no diagnostic arises. Each body is checked in phases, and an error that involves several places is reported at one of them. [Conformance](01-conformance.md) compares diagnostics exactly, so every implementation reports the same ones. How a program with errors runs is the subject of [Programs, modules and packages](04-programs.md#program.programs-with-errors).

## Root causes

<a id="errors.root-causes"></a>
An implementation reports only **root-cause** diagnostics: those that no other diagnostic caused. The rules of this chapter decide which diagnostics those are. Under them, one mistake gives one diagnostic, the same in every implementation, and mistakes that don't depend on each other are each reported.

Tests: [checking/operator_error_once.lt](../conformance/checking/operator_error_once.lt), [records/bound_without_rest.lt](../conformance/records/bound_without_rest.lt), [records/closed_bound_read_as_open.lt](../conformance/records/closed_bound_read_as_open.lt), [types/error_type_cascades.lt](../conformance/types/error_type_cascades.lt), [types/independent_errors.lt](../conformance/types/independent_errors.lt), [variadics/misplaced_pack_named_bare.lt](../conformance/variadics/misplaced_pack_named_bare.lt), [views/view_types_in_signatures.lt](../conformance/views/view_types_in_signatures.lt).

## Syntax errors

<a id="errors.syntax-errors"></a>
The **syntax errors** are the lexical errors of [Lexical structure](02-lexical.md) and the errors of the grammar (E0100, [syntax.grammar-errors](03-syntax.md#syntax.grammar-errors)). The grammar's errors include these:

- a declared name of the wrong case ([lexical.case.wrong-case](02-lexical.md#lexical.case.wrong-case));
- a keyword or a reserved word used as a name ([lexical.keywords](02-lexical.md#lexical.keywords), [lexical.reserved-words](02-lexical.md#lexical.reserved-words));
- a word after `without` that isn't a limit ([program.header-limits](04-programs.md#program.header-limits));
- a type alias ([declarations.no-aliases](10-declarations.md#declarations.no-aliases));
- a row variable declared by anything but a function ([effects.row-variables](12-effects.md#effects.row-variables));
- a bound on a type's parameter ([traits.bounds](11-traits.md#traits.bounds));
- a misplaced doc comment ([syntax.doc-comment-placement](03-syntax.md#syntax.doc-comment-placement));
- a doc example or a property that doesn't parse ([syntax.doc-examples](03-syntax.md#syntax.doc-examples)).

The grammar fixes where each one is reported. A primitive type name used as a name is no syntax error: name resolution rejects it (E0210, [lexical.primitive-type-names](02-lexical.md#lexical.primitive-type-names)).

Tests: [lexical/core_keywords_as_names](../conformance/lexical/core_keywords_as_names/), [lexical/invalid_escapes](../conformance/lexical/invalid_escapes/), [lexical/later_tier_words_as_names](../conformance/lexical/later_tier_words_as_names/), [lexical/malformed_floats](../conformance/lexical/malformed_floats/), [lexical/malformed_format_specs](../conformance/lexical/malformed_format_specs/), [lexical/malformed_integers](../conformance/lexical/malformed_integers/), [lexical/primitive_type_names.lt](../conformance/lexical/primitive_type_names.lt), [lexical/reserved_tokens](../conformance/lexical/reserved_tokens/), [lexical/unexpected_characters](../conformance/lexical/unexpected_characters/), [lexical/unterminated_strings](../conformance/lexical/unterminated_strings/), [lexical/wrong_case](../conformance/lexical/wrong_case/).

## Reading a file in parts

<a id="errors.parts"></a>
A file with a syntax error is read a part at a time. Each declaration reports its first syntax error, and the rest of the program is checked as usual. The file is read from its start, and again from each line where reading resumes ([errors.resuming](#errors.resuming)). Each time, the text from there on is lexed as a file is, up to its first lexical error, which ends the tokens.

The tokens are cut into **parts** before each of these tokens that follows a separator outside every bracket:

- `use`, `impl`, `pub`, `extern`, `fn`, `type`, `trait`, `const`, `test`, `syntax`, `effect` and `macro`;
- each `meta` that `use` follows;
- each doc comment;
- each word that another language begins a declaration with, as [syntax.parts](03-syntax.md#syntax.parts) lists them: `def`, `func`, `function`, `fun`, `struct`, `class`, `enum`, `interface`, `protocol`, `extension`, `let` and `var` when a name follows, and `async` and `mutating` when `fn` follows. None of them begins a declaration of Stilt, so such a part always breaks, and the declarations around it stay whole.

In counting brackets, a closing bracket closes the innermost open bracket, whatever its kind ([syntax.parts](03-syntax.md#syntax.parts)). When no token comes before the lexical error, there is one part, which holds no token and starts at the error. Each part is parsed alone, as a file of its own. A part that parses declares its items. The file's header is that of its first part, if that part parses.

Tests: [checking/foreign_declarations.lt](../conformance/checking/foreign_declarations.lt), [procedural/meta_use_begins_a_part.lt](../conformance/procedural/meta_use_begins_a_part.lt), [procedural/part_words.lt](../conformance/procedural/part_words.lt), [protocol/syntax_errors_per_part](../conformance/protocol/syntax_errors_per_part/).

<a id="errors.invalid-source-text"></a>
A file that isn't valid source text has no tokens ([lexical.source-text](02-lexical.md#lexical.source-text)). Its E0001 is its only diagnostic, and it declares nothing. Every path into its module has the error type ([errors.error-type](#errors.error-type)).

Tests: [lexical/source_text](../conformance/lexical/source_text/).

<a id="errors.breaks"></a>
A part **breaks** at its grammar error, or at the lexical error that ends it when the parser accepts every token before it ([syntax.lexical-errors](03-syntax.md#syntax.lexical-errors)). A doc example or a property that doesn't parse breaks no part: the part declares its items without it.

Tests: [program/misplaced_docs](../conformance/program/misplaced_docs/), [protocol/syntax_errors_per_part](../conformance/protocol/syntax_errors_per_part/).

<a id="errors.resuming"></a>
A part that breaks ends early, at the first line that meets all of these conditions:

- it starts in its first column with one of the words that begin a part, as a whole word, other than the words of other languages;
- it comes after the line of the part's first token after its doc comments;
- it is no earlier than the line on which the part breaks, and is after that line when the part breaks at a lexical error.

Such a line counts when it lies in the part, even inside a bracket that the part leaves open. When a lexical error ends the part, it also counts anywhere after that error. Reading resumes at that line, or at the first of the doc comments that document the declaration on it ([program.doc-comments](04-programs.md#program.doc-comments)). The part ends just before. So a `}` left out costs one diagnostic, and the declarations after it are read.

Tests: [procedural/broken_part](../conformance/procedural/broken_part/), [procedural/part_words.lt](../conformance/procedural/part_words.lt), [protocol/syntax_errors_per_part](../conformance/protocol/syntax_errors_per_part/).

<a id="errors.part-reports"></a>
A part reports its first syntax error ([syntax.first-error](03-syntax.md#syntax.first-error)). That is the earliest of the error at which it breaks and the errors of the doc examples and properties in it. In a part with a syntax error, nothing else is reported. No other diagnostic whose primary span starts in the part is reported, warnings included, except E0200, which is about the file's name ([program.module-names](04-programs.md#program.module-names)). Here the part runs from its first token up to the next part, the line where reading resumes, or the end of the file.

Tests: [checking/phases_syntax_and_analyses.lt](../conformance/checking/phases_syntax_and_analyses.lt), [checking/phases_syntax_and_items.lt](../conformance/checking/phases_syntax_and_items.lt), [checking/phases_syntax_and_types.lt](../conformance/checking/phases_syntax_and_types.lt), [checking/phases_syntax_and_warnings.lt](../conformance/checking/phases_syntax_and_warnings.lt), [procedural/meta_use_begins_a_part.lt](../conformance/procedural/meta_use_begins_a_part.lt), [protocol/syntax_errors_per_part](../conformance/protocol/syntax_errors_per_part/).

## What a part that breaks declares

<a id="errors.broken-parts"></a>
A part that breaks declares the item it begins, after its doc comments, `pub` and `extern`, with an error ([errors.declarations-with-errors](#errors.declarations-with-errors)):

| It begins with | It declares |
| --- | --- |
| `fn` and a name, a `lower` or an `Upper` | That function. If the part breaks after the token that opens the body, the first `=` or the first `{` that doesn't follow `/` outside brackets, the function has the signature written before that token, when that is a whole signature, its result type included if an `->` is written. Otherwise, as when the `{` begins an anonymous record type after `->` ([records.anonymous-types](07-types.md#records.anonymous-types)) and the part breaks inside it, every use of its name has the error type |
| `const` and a name, an `Upper` or a `lower` | That constant. If the part breaks after its `=`, it has the type written before it and no value, so a value argument that names it has the error type. Otherwise every use of its name has the error type |
| `type` and a name | That type, and every use of its name has the error type |
| `syntax` and a name | That pattern macro, which expands no use ([macros.matching](16-meta.md#macros.matching)) |
| `effect` and a name | That effect, and every use of its name has the error type |
| `macro` and a name | That procedural macro, which expands no use ([macros.expansion-order](16-meta.md#macros.expansion-order)) |
| `trait` or `impl` | What [errors.broken-blocks](#errors.broken-blocks) says |
| `test` and a string | That test |
| `def`, `func`, `function` or `fun`, and a name; or `async` or `mutating`, `fn` and a name | That function, and every use of its name has the error type |
| `struct`, `class` or `enum`, and a name | That type, and every use of its name has the error type |
| `interface` or `protocol`, and a name | That trait, and every use of its name has the error type |
| Anything else | Nothing |

A function written `extern` that breaks is declared by the first row, as a function with an error. It is never a foreign function ([c.foreign-functions](20-builds.md#c.foreign-functions)), so a call of it needs no `unsafe`.

Tests: [checking/broken_constant_as_value_argument.lt](../conformance/checking/broken_constant_as_value_argument.lt), [checking/broken_procedural_macro.lt](../conformance/checking/broken_procedural_macro.lt), [checking/broken_signature_not_whole.lt](../conformance/checking/broken_signature_not_whole.lt), [checking/foreign_declarations.lt](../conformance/checking/foreign_declarations.lt), [checking/foreign_members.lt](../conformance/checking/foreign_members.lt), [checking/names_in_the_other_case.lt](../conformance/checking/names_in_the_other_case.lt), [procedural/broken_macro](../conformance/procedural/broken_macro/), [program/syntax_error_in_constant.lt](../conformance/program/syntax_error_in_constant.lt), [program/syntax_error_in_exported_function.lt](../conformance/program/syntax_error_in_exported_function.lt), [program/syntax_error_in_type.lt](../conformance/program/syntax_error_in_type.lt).

<a id="errors.broken-blocks"></a>
The first `{` outside brackets in a trait or an impl opens its block. A trait or an impl whose part breaks after that `{` declares the trait or the impl written before it, with the members that its block declares. The block, up to the bracket that closes it, is read as a file is, without resuming. It is cut before each `fn`, `const` and `pub`, each doc comment, and each `def`, `func`, `function` or `fun` that a name follows and `async` or `mutating` that `fn` follows, that follows a separator directly inside it. Each part is parsed as the block's only member.

A part of the block that has an error declares as [errors.broken-parts](#errors.broken-parts) says, but only a function or a constant, the members that a block can hold. A member that the table leaves without a signature or a type takes no parameters, and its result or its type is the error type. A trait whose part breaks before that `{` declares its name, and every use of it has the error type. An impl whose part breaks before that `{` declares nothing.

Tests: [checking/bound_on_a_broken_trait.lt](../conformance/checking/bound_on_a_broken_trait.lt), [checking/foreign_members.lt](../conformance/checking/foreign_members.lt), [checking/trait_broken_before_its_block.lt](../conformance/checking/trait_broken_before_its_block.lt), [program/syntax_error_in_method.lt](../conformance/program/syntax_error_in_method.lt), [reflection/broken_own_shape.lt](../conformance/reflection/broken_own_shape.lt).

<a id="errors.declarations-with-errors"></a>
A declaration with an error still declares its name. The rest of the program sees one declaration of that name. Each part of its signature that has an error becomes the error type.

Tests: [checking/declarations_with_errors.lt](../conformance/checking/declarations_with_errors.lt), [checking/method_declared_twice.lt](../conformance/checking/method_declared_twice.lt), [polymorphism/placement_errors.lt](../conformance/polymorphism/placement_errors.lt), [program/prelude_qualified](../conformance/program/prelude_qualified/), [program/prelude_same_namespace.lt](../conformance/program/prelude_same_namespace.lt), [promises/copies_after_a_name_defined_twice.lt](../conformance/promises/copies_after_a_name_defined_twice.lt).

## The error type

<a id="errors.error-type"></a>
A name that fails to resolve, a name of an item that isn't visible ([program.visibility](04-programs.md#program.visibility)), and a type or an expression that fails to check get the **error type**. The error type is compatible with every type, has every field and method, satisfies every bound and performs no effects. A body with an error performs no implicit effects either ([facts.bodies-with-errors](15-facts.md#facts.bodies-with-errors)). No diagnostic ever arises from the error type.

Tests: [checking/assignment_to_unknown_name.lt](../conformance/checking/assignment_to_unknown_name.lt), [checking/broken_constant_as_value_argument.lt](../conformance/checking/broken_constant_as_value_argument.lt), [checking/call_spreading_a_broken_tuple.lt](../conformance/checking/call_spreading_a_broken_tuple.lt), [checking/copies_of_a_broken_field.lt](../conformance/checking/copies_of_a_broken_field.lt), [checking/error_typed_arguments.lt](../conformance/checking/error_typed_arguments.lt), [checking/hole_called_with_a_broken_spread.lt](../conformance/checking/hole_called_with_a_broken_spread.lt), [checking/spread_into_a_broken_parameter.lt](../conformance/checking/spread_into_a_broken_parameter.lt), [checking/spread_of_a_broken_item.lt](../conformance/checking/spread_of_a_broken_item.lt), [checking/spread_of_a_broken_tuple.lt](../conformance/checking/spread_of_a_broken_tuple.lt), [checking/view_of_a_broken_type.lt](../conformance/checking/view_of_a_broken_type.lt), [effects/without_panic_reported_once/](../conformance/effects/without_panic_reported_once/), [foreign/broken_pointee.lt](../conformance/foreign/broken_pointee.lt), [generics/arguments_of_a_broken_path.lt](../conformance/generics/arguments_of_a_broken_path.lt), [patterns/or_pattern_types.lt](../conformance/patterns/or_pattern_types.lt), [program/invalid_name_checked/](../conformance/program/invalid_name_checked/), [protocol/error_type_effects.lt](../conformance/protocol/error_type_effects.lt), [records/update_errors.lt](../conformance/records/update_errors.lt), [records/update_of_a_declared_record_as_an_operand.lt](../conformance/records/update_of_a_declared_record_as_an_operand.lt), [reflection/impl_of_an_unknown_type.lt](../conformance/reflection/impl_of_an_unknown_type.lt), [types/error_type_cascades.lt](../conformance/types/error_type_cascades.lt), [variadics/function_type_of_no_pack.lt](../conformance/variadics/function_type_of_no_pack.lt), [variadics/spread_of_no_pack.lt](../conformance/variadics/spread_of_no_pack.lt)

<a id="errors.error-type-raises"></a>
Code that holds an expression of the error type may raise the error type, as a call does whose row names an unknown type ([effects.error-type-raises](12-effects.md#effects.error-type-raises)). So a `try` around it marks something, a `catch` around it handles the error type, and arms matched against the error type are never unreachable. A pattern on a value of the error type covers it ([patterns.non-exhaustive-matches](09-patterns.md#patterns.non-exhaustive-matches)).

Tests: [checking/error_type_in_try_and_match.lt](../conformance/checking/error_type_in_try_and_match.lt), [effects/raise_of_error_type.lt](../conformance/effects/raise_of_error_type.lt), [patterns/error_payloads.lt](../conformance/patterns/error_payloads.lt).

<a id="errors.primitive-type-bindings"></a>
A binding named with a primitive type name, by a `let`, a pattern or a parameter, is E0210 ([lexical.primitive-type-names](02-lexical.md#lexical.primitive-type-names)). The binding has the error type wherever it is used, as a binding named after an imported module does ([program.one-value-namespace](04-programs.md#program.one-value-namespace)).

Tests: [names/primitive_binding_used.lt](../conformance/names/primitive_binding_used.lt).

## Unknown names

<a id="errors.unknown-names"></a>
A body reports one E0211 for each name that doesn't resolve in it ([declarations.unknown-names](10-declarations.md#declarations.unknown-names)), at the place where that name starts first. The other places in the body where the same name doesn't resolve have the error type, with no diagnostic. A name here is a path as written, up to and including the name in it that doesn't resolve. So `countt` and `orders.countt` are two names, while `Item`, which resolves neither as a type nor as a value, is one. Outside bodies, every place where a name doesn't resolve is reported.

Tests: [checking/assignment_to_unknown_name.lt](../conformance/checking/assignment_to_unknown_name.lt), [checking/bound_on_a_broken_trait.lt](../conformance/checking/bound_on_a_broken_trait.lt), [checking/open_record_with_unknown_names.lt](../conformance/checking/open_record_with_unknown_names.lt), [parameters/where_on_a_missing_member.lt](../conformance/parameters/where_on_a_missing_member.lt), [patterns/bare_variant_errors](../conformance/patterns/bare_variant_errors/), [types/error_type_cascades.lt](../conformance/types/error_type_cascades.lt).

## Bodies and phases

<a id="errors.phases"></a>
A **body** is a function body, a test body, a doc example, a property or a constant's initializer. Each body is checked in three **phases**, and each phase runs only if the earlier ones found no error in that body:

1. Name resolution and type checking. This phase includes fitting the body's effects to its declared row ([effects.inference](12-effects.md#effects.inference)). It also includes the marks and places of `inout` arguments and assignments ([expressions.inout-arguments](08-expressions.md#expressions.inout-arguments), [expressions.places](08-expressions.md#expressions.places)).
2. The analyses: marking and handling ([effects.marking](12-effects.md#effects.marking)), exhaustiveness ([patterns.non-exhaustive-matches](09-patterns.md#patterns.non-exhaustive-matches)), modes and exclusivity ([Modes and exclusivity](13-modes.md)) and implicit effects ([facts.without](15-facts.md#facts.without)). They all run, and all of their errors are reported.
3. Warnings.

Errors outside bodies, in module headers, imports, declarations and impls, are all reported.

Tests: [checking/phases.lt](../conformance/checking/phases.lt), [effects/phase_interplay.lt](../conformance/effects/phase_interplay.lt), [modes/inout_marks_in_phase_one.lt](../conformance/modes/inout_marks_in_phase_one.lt), [types/independent_errors.lt](../conformance/types/independent_errors.lt).

<a id="errors.registry-phases"></a>
The registry of codes, [`errors.toml`](errors.toml), gives each code the phase in which it is checked, and so decides when it is reported:

| Phase | Meaning |
| --- | --- |
| `syntax` | A syntax error ([errors.syntax-errors](#errors.syntax-errors)) |
| `items` | An error that arises only outside bodies: in module headers, imports, declarations and impls. Every one is reported |
| `types` | Phase 1 of a body. The same code outside a body, in a signature or a declaration, is always reported |
| `analyses` | Phase 2 of a body |
| `warnings` | Phase 3 of a body, and warnings outside bodies |
| `refusal` | The refusal of an edit that a command was given ([edits.refusals](19-tools.md#edits.refusals)), which no diagnostic of the program accompanies |

Tests: [checking/phases_analyses_and_warnings.lt](../conformance/checking/phases_analyses_and_warnings.lt), [checking/phases_items_and_analyses.lt](../conformance/checking/phases_items_and_analyses.lt), [checking/phases_items_and_types.lt](../conformance/checking/phases_items_and_types.lt), [checking/phases_items_and_warnings.lt](../conformance/checking/phases_items_and_warnings.lt), [checking/phases_syntax_and_analyses.lt](../conformance/checking/phases_syntax_and_analyses.lt), [checking/phases_syntax_and_items.lt](../conformance/checking/phases_syntax_and_items.lt), [checking/phases_syntax_and_types.lt](../conformance/checking/phases_syntax_and_types.lt), [checking/phases_syntax_and_warnings.lt](../conformance/checking/phases_syntax_and_warnings.lt), [checking/phases_types_and_analyses.lt](../conformance/checking/phases_types_and_analyses.lt), [checking/phases_types_and_warnings.lt](../conformance/checking/phases_types_and_warnings.lt).

Checked by: also `just coverage`, which checks the files generated from the registry, and so that every code of the registry has a phase.

<a id="errors.phase-by-form"></a>
An error that name resolution reports inside a body, such as a name bound twice in one pattern, is an error of phase 1 in that body. So are the errors that the form of the code decides:

- a refutable pattern where none may stand (E0321);
- a float in a pattern (E0328);
- alternatives that bind different names (E0217);
- a reason on an arm that isn't a catch-all (E0504);
- `break` or `continue` outside a loop (E0216).

Assigning to what can't be modified (E0403) is an error of phase 2, with modes and exclusivity ([modes.what-can-be-modified](13-modes.md#modes.what-can-be-modified)).

Tests: [checking/phase_one_by_form.lt](../conformance/checking/phase_one_by_form.lt), [checking/resolution_errors.lt](../conformance/checking/resolution_errors.lt), [checking/unmodifiable_with_missing_arm.lt](../conformance/checking/unmodifiable_with_missing_arm.lt), [checking/unmodifiable_with_type_error.lt](../conformance/checking/unmodifiable_with_type_error.lt).

<a id="errors.undecided-types-last"></a>
A type that a body leaves undecided (E0312, [types.undecided-types](07-types.md#types.undecided-types)) is an error of phase 1, reported only when phase 1 found no other error in the body.

Tests: [declarations/hole_uninferred.lt](../conformance/declarations/hole_uninferred.lt), [expressions/undecided_types.lt](../conformance/expressions/undecided_types.lt), [traits/bound_argument_left_open.lt](../conformance/traits/bound_argument_left_open.lt).

<a id="errors.warnings-with-errors"></a>
A warning about a comment, such as W0001 ([lexical.commented-out-code](02-lexical.md#lexical.commented-out-code)), is reported even inside a body with errors. So is every warning outside the bodies. Neither is reported when it lies in a part with a syntax error ([errors.part-reports](#errors.part-reports)).

Tests: [checking/warning_outside_bodies.lt](../conformance/checking/warning_outside_bodies.lt), [protocol/comment_inside_failing_body.lt](../conformance/protocol/comment_inside_failing_body.lt), [protocol/comment_warnings_with_errors.lt](../conformance/protocol/comment_warnings_with_errors.lt).

## Where diagnostics are reported

<a id="errors.primary-spans"></a>
Each diagnostic is reported at its **primary span**, which the registry gives for each code. Its line is the line on which that span starts ([conformance.diagnostic-lines](01-conformance.md#conformance.diagnostic-lines)). For E0404, the primary span is the modification, not the loop ([modes.change-while-iterating](13-modes.md#modes.change-while-iterating)).

Tests: [modes/change_while_reading.lt](../conformance/modes/change_while_reading.lt), [protocol/primary_span_start_line.lt](../conformance/protocol/primary_span_start_line.lt).

<a id="errors.several-places"></a>
Unless the registry says otherwise, an error that involves several places is reported at the one that comes last in the program. That place is in the file whose path sorts last by bytes, at the last position in that file. So for two declarations with the same name, the later one is the error, and the earlier one is the declaration that the rest of the program sees. The same holds for these errors:

- two `use` declarations that clash ([program.import-clashes](04-programs.md#program.import-clashes));
- the `use` declarations and paths of an import cycle ([program.no-cycles](04-programs.md#program.no-cycles));
- a constant cycle ([declarations.constant-cycles](10-declarations.md#declarations.constant-cycles));
- overlapping impls ([traits.coherence](11-traits.md#traits.coherence)).

Tests: [declarations/constant_cycles.lt](../conformance/declarations/constant_cycles.lt), [declarations/duplicate_cycles.lt](../conformance/declarations/duplicate_cycles.lt), [declarations/namespaces.lt](../conformance/declarations/namespaces.lt), [declarations/record_contains_itself.lt](../conformance/declarations/record_contains_itself.lt), [modes/overlap_reported_at_later.lt](../conformance/modes/overlap_reported_at_later.lt), [names/defined_twice.lt](../conformance/names/defined_twice.lt), [names/import_clash](../conformance/names/import_clash/), [names/import_cycle_3](../conformance/names/import_cycle_3/), [names/import_cycle_through_path](../conformance/names/import_cycle_through_path/), [names/import_cycles_sharing_a_module](../conformance/names/import_cycles_sharing_a_module/), [program/use_and_item_clash.lt](../conformance/program/use_and_item_clash.lt), [protocol/cycle_in_last_path](../conformance/protocol/cycle_in_last_path/).

## Running a program with errors

<a id="errors.running"></a>
A program with errors still runs ([program.programs-with-errors](04-programs.md#program.programs-with-errors)). `run` reports its diagnostics, runs the program, and exits with status 2 however it ends. Each body that has an error, or that meets the error type, is replaced by a panic of kind `check-error` where it is reached ([program.bodies-with-errors](04-programs.md#program.bodies-with-errors), [program.meeting-the-error-type](04-programs.md#program.meeting-the-error-type)). This holds whether or not the error is reported. Each function, constant and test that a part that breaks declares is replaced in the same way ([program.syntax-errors-at-run](04-programs.md#program.syntax-errors-at-run)). Everything else runs as it would in a program without errors.

Tests: [program/error_never_reached.lt](../conformance/program/error_never_reached.lt), [program/run_with_warnings.lt](../conformance/program/run_with_warnings.lt), [program/syntax_error_in_constant.lt](../conformance/program/syntax_error_in_constant.lt), [program/syntax_error_in_exported_function.lt](../conformance/program/syntax_error_in_exported_function.lt), [program/syntax_error_in_method.lt](../conformance/program/syntax_error_in_method.lt), [program/syntax_error_in_type.lt](../conformance/program/syntax_error_in_type.lt).
