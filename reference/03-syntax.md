# 3. Syntax

This chapter gives the grammar of every tier, the canonical format that `stilt fmt` writes, and the tree form that `parse --sexp` prints. The grammar reads the tokens of [Lexical structure](02-lexical.md). Its productions restate, in a form a parser can follow, the forms whose meaning the other chapters give. Those chapters name a production, as `` `head` ``, and link here.

## One syntax

<a id="syntax.one-syntax"></a>
Stilt has exactly one surface syntax, which every implementation and every tool reads. These forms, which shorten common code, are part of it:

- let-else ([patterns.let-else](09-patterns.md#patterns.let-else));
- the expression-level `else` ([expressions.option-fallback](08-expressions.md#expressions.option-fallback));
- key paths ([expressions.key-paths](08-expressions.md#expressions.key-paths));
- field punning ([expressions.struct-literal-fields](08-expressions.md#expressions.struct-literal-fields));
- blocks of one statement on one line ([syntax.format.short-blocks](#syntax.format.short-blocks));
- `/// ex:` examples ([program.doc-comments](04-programs.md#program.doc-comments)).

No form is a profile or a dialect of another.

Tests: [lexical/six_constructs.lt](../conformance/lexical/six_constructs.lt).

## Notation

<a id="syntax.grammar"></a>
The productions of this chapter are the grammar of every tier. The reference interpreter's parser, in `interpreter/lib/parser.mly` and the `parser_*.mly` files beside it, implements them production by production. If a production accepts a form that another chapter rejects, that chapter's error is reported after parsing, and is not a syntax error.

Checked by: `just parse`, which compares the trees and the first syntax error of each file under the compiler's parser and the reference interpreter's, over the conformance suite, the guide's examples, generated programs and edits of them that plant syntax errors (`tools/runner/src/judge.rs`); and the conformance tests of the paragraphs that the productions restate.

<a id="syntax.notation"></a>
The grammar is written in EBNF:

| Notation | Meaning |
| --- | --- |
| `a b` | `a` followed by `b` |
| `a \| b` | `a` or `b` |
| `[ a ]` | `a`, optionally |
| `{ a }` | `a`, zero or more times |
| `( a )` | grouping |
| `"fn"` | the token spelled `fn` |
| `list(a)` | `[ list1(a) ]`: zero or more `a` |
| `list1(a)` | `a { "," a } [ "," ]`: one or more `a`, separated by commas, with an optional comma at the end ([expressions.precedence](08-expressions.md#expressions.precedence)) |

Checked by: the grammar generator's reader of the notation (`tools/grammar/src/ebnf.rs`), which reads every production of this chapter, and `just grammar`.

<a id="syntax.token-classes"></a>
These names stand for classes of tokens:

| Name | Tokens |
| --- | --- |
| `lower` | An identifier whose first letter is lowercase, the primitive type names included |
| `Upper` | An identifier whose first letter is uppercase |
| `INT`, `FLOAT` | Number literals |
| `STRING` | A string literal with no interpolation |
| `STRING_HEAD`, `STRING_MID`, `STRING_TAIL`, `FORMAT` | The parts of an interpolated string, as [lexical.interpolation](02-lexical.md#lexical.interpolation) lexes it |
| `SEP` | A separator: `;`, or a terminator inserted at the end of a line ([lexical.terminator-insertion](02-lexical.md#lexical.terminator-insertion)) |
| `DOC` | A run of doc comments ([syntax.doc-comment-runs](#syntax.doc-comment-runs)) |

The grammar reads the tokens of [Lexical structure](02-lexical.md) after [lexical.separators](02-lexical.md#lexical.separators) has removed the separators it ignores.

Tests: [lexical/identifiers.lt](../conformance/lexical/identifiers.lt), [lexical/interpolation.lt](../conformance/lexical/interpolation.lt), [lexical/wrong_case/](../conformance/lexical/wrong_case/).

<a id="syntax.contextual-keywords"></a>
In the productions, the contextual keywords of [lexical.contextual-keywords](02-lexical.md#lexical.contextual-keywords) appear quoted, like keywords. The parser reads one as the keyword exactly where a production accepts the keyword at that point, and as a `lower` everywhere else.

Tests: [lexical/contextual_keywords.lt](../conformance/lexical/contextual_keywords.lt), [lexical/escaping_as_parameter.lt](../conformance/lexical/escaping_as_parameter.lt), [lexical/because_outside_catch.lt](../conformance/lexical/because_outside_catch.lt).

## Programs

<a id="syntax.programs"></a>
A file is a module header followed by items, or items alone. The members of a trait impl take no `pub` ([program.visibility](04-programs.md#program.visibility)).

```ebnf
file            = "module" lower_path { [ SEP ] limits } [ SEP item { SEP item } ]
                | [ item { SEP item } ] ;
limits          = "without" limit { "," limit } ;
limit           = "panic" | "overflow" | "alloc" | "div" | "copy"
                | "fs" | "net" | "clock" | "env" | "console" | "rand" | "spawn" | "exec" | "locks"
                | "unsafe" ;
item            = [ "meta" ] "use" use_path
                | [ DOC ] [ "pub" ] ( fn | type_decl | trait | const | syntax | macro | effect )
                | [ DOC ] "pub" "extern" fn
                | [ DOC ] [ "pub" ] "extern" fn_head [ limits ]
                | [ DOC ] test
                | "impl" [ impl_generics ] type [ where ] "{" [ inherent_member { SEP inherent_member } ] "}"
                | "impl" [ impl_generics ] bound "for" type [ where ] "{" [ trait_impl_member { SEP trait_impl_member } ] "}" ;
inherent_member = [ DOC ] [ "pub" ] ( fn | const ) ;
trait_impl_member = [ DOC ] ( fn | const ) ;
```

Tests: [program/single-file.lt](../conformance/program/single-file.lt), [program/header_separators.lt](../conformance/program/header_separators.lt), [program/pub_in_trait_impl.lt](../conformance/program/pub_in_trait_impl.lt), [program/option_after_item.lt](../conformance/program/option_after_item.lt).

<a id="syntax.extern-functions"></a>
Only a module's function can be exported or foreign. An exported function is written `pub extern fn` with a body ([c.exported-functions](20-builds.md#c.exported-functions)). A foreign function is written `extern fn` without a body, `pub` or not ([c.foreign-functions](20-builds.md#c.foreign-functions)). A foreign function ends at its signature, or at a `without` clause after it, which says what its C code doesn't do ([c.effects](20-builds.md#c.effects)). A `where` clause or `= ?` after its signature is a syntax error, and so is a body after an `extern` without `pub`. Which parts of a foreign function's signature C can take is decided after parsing ([c.types-c-takes](20-builds.md#c.types-c-takes)).

Tests: [export/accepted.lt](../conformance/export/accepted.lt), [foreign/where.lt](../conformance/foreign/where.lt), [foreign/body_without_pub.lt](../conformance/foreign/body_without_pub.lt), [export/without_pub.lt](../conformance/export/without_pub.lt).

## Declarations

<a id="syntax.declarations"></a>
Functions, types, traits, constants, tests and effects are declared by these productions. An operation of an effect has no generics and no body. A handler's types and its operations are checked after parsing ([handlers.declaring-effect](12-effects.md#handlers.declaring-effect), [handlers.handler-literals](12-effects.md#handlers.handler-literals)).

```ebnf
fn          = fn_head [ where ] [ limits ] fn_body ;
fn_head     = "fn" lower [ generics ] params [ "->" result ] [ "/" row ] ;
result      = [ "inout" ] type ;
fn_body     = block | "=" "?" ;
generics    = "<" list1(generic) ">" ;
generic     = type_param | ".." type_param | lower [ ":" type ] ;
value_param = lower ":" type ;
type_param  = Upper [ ":" bounds ] ;
bounds      = bound { "+" bound } ;
bound       = upper_path [ "<" list1(type) ">" ]
            | "{" list1(field) [ "," ".." ] "}" ;
where       = "where" list1(where_bound) ;
where_bound = upper_path ":" bounds ;
impl_generics = "<" list1(impl_generic) ">" ;
impl_generic  = type_param | value_param ;
params      = "(" ( list(param) | self_param [ "," list(param) ] ) ")" ;
self_param  = [ mode ] "self" [ ":" type ] ;
param       = [ mode ] lower ":" type
            | "escaping" lower ":" fn_type ;
mode        = "inout" ;

type_decl   = "type" Upper [ "<" list1(type_generic) ">" ] "=" ( type_def | "?" ) ;
type_generic = type_name | value_param ;
type_name   = Upper | ".." Upper ;
type_def    = "{" list(field) "}"
            | "|" variant { "|" variant }
            | variant "|" variant { "|" variant } ;
field       = lower ":" type ;
variant     = Upper [ "(" list1(payload) ")" ] ;
payload     = [ lower ":" ] type ;

trait       = "trait" Upper [ "<" list1(type_name) ">" ] "{" [ trait_member { SEP trait_member } ] "}" ;
trait_member = [ DOC ] ( fn_head [ where ] [ [ limits ] fn_body ] | "const" Upper ":" type [ "=" expr ] ) ;
const       = "const" Upper ":" type "=" expr ;
test        = "test" STRING block ;
effect      = "effect" Upper [ "<" list1(Upper) ">" ] "{" [ operation { SEP operation } ] "}" ;
operation   = [ DOC ] "fn" lower params [ "->" type ] [ "/" row ] ;
```

Tests: [declarations/functions.lt](../conformance/declarations/functions.lt), [declarations/variants.lt](../conformance/declarations/variants.lt), [declarations/default_parameter.lt](../conformance/declarations/default_parameter.lt), [declarations/const_without_type.lt](../conformance/declarations/const_without_type.lt).

<a id="syntax.projection-results"></a>
A result written `inout T` makes the function a projection, whose body yields a place of type `T` ([projections.declaring-projection](13-modes.md#projections.declaring-projection)). A function type has no such result, so `fn() -> inout i64` is a syntax error at the `inout`.

Tests: [projections/projection_basics.lt](../conformance/projections/projection_basics.lt), [projections/function_type_without_projection.lt](../conformance/projections/function_type_without_projection.lt).

<a id="syntax.lowercase-generics"></a>
A lowercase generic without a type is a row variable, which only a function declares ([effects.rows](12-effects.md#effects.rows)). A lowercase generic with a type is a value parameter. A function, a type and an impl may declare one, and its type is checked after parsing ([generics.value-parameters](07-types.md#generics.value-parameters), [generics.value-parameter-positions](07-types.md#generics.value-parameter-positions)). The generics of a trait, of an effect and of a function type take no value parameter, so `trait T<n: i64>` is a syntax error at the `n`.

Tests: [declarations/row_variable_on_type.lt](../conformance/declarations/row_variable_on_type.lt), [declarations/row_variable_on_impl.lt](../conformance/declarations/row_variable_on_impl.lt), [generics/placement_errors.lt](../conformance/generics/placement_errors.lt), [generics/declarations.lt](../conformance/generics/declarations.lt).

<a id="syntax.escaping-parameters"></a>
An `escaping` parameter takes no mode. Its type is written with `fn` ([declarations.function-declarations](10-declarations.md#declarations.function-declarations)), so `escaping f: (fn())` is not a parameter.

Tests: [declarations/escaping_parenthesized.lt](../conformance/declarations/escaping_parenthesized.lt), [declarations/escaping_after_mode.lt](../conformance/declarations/escaping_after_mode.lt), [declarations/escaping_non_function.lt](../conformance/declarations/escaping_non_function.lt).

<a id="syntax.bounds-placement"></a>
Only functions and impl blocks take bounds. The parameters of a type and of a trait are plain names ([traits.bounds](11-traits.md#traits.bounds), [traits.trait-parameters](11-traits.md#traits.trait-parameters)). These are errors after parsing, not syntax errors:

- a pack among a trait's parameters, and a type's pack before its last parameter or a type's second pack ([variadics.packs](07-types.md#variadics.packs));
- a `where` bound on anything but a member type, and a `where` clause on a function of a trait or of a trait impl ([traits.where](11-traits.md#traits.where));
- a receiver's written type where none is allowed, or a missing one where one is needed ([traits.receiver-types](11-traits.md#traits.receiver-types)).

`C.Item` is an `upper_path`. Name resolution reads it as a member type when `C` is a type parameter ([traits.member-types](11-traits.md#traits.member-types)).

Tests: [declarations/bound_on_type.lt](../conformance/declarations/bound_on_type.lt), [traits/bound_on_trait.lt](../conformance/traits/bound_on_trait.lt), [parameters/where_clauses.lt](../conformance/parameters/where_clauses.lt).

<a id="syntax.generic-lists"></a>
A list of generics or of type parameters, written `<…>`, holds at least one, so `fn f<>()`, `type P<> = …` and `impl<> P` are syntax errors.

Tests: [declarations/empty_function_generics.lt](../conformance/declarations/empty_function_generics.lt), [declarations/empty_type_parameters.lt](../conformance/declarations/empty_type_parameters.lt), [declarations/empty_impl_generics.lt](../conformance/declarations/empty_impl_generics.lt).

<a id="syntax.variants"></a>
A single variant needs its leading `|`, so `type Id = UserId` is not a declaration ([declarations.no-aliases](10-declarations.md#declarations.no-aliases)). A variant with a payload has at least one payload field, so `V()` is not a variant.

Tests: [declarations/single_variant_without_bar.lt](../conformance/declarations/single_variant_without_bar.lt), [declarations/empty_payload.lt](../conformance/declarations/empty_payload.lt), [declarations/variants.lt](../conformance/declarations/variants.lt).

<a id="syntax.limit-clauses"></a>
The grammar lets a header hold several `limits`. A second `without` in a header, and a limit named twice, are errors after parsing, not syntax errors ([program.module-header](04-programs.md#program.module-header), [declarations.function-declarations](10-declarations.md#declarations.function-declarations)). A newline between a signature and its `where` inserts a terminator, which ends the signature. So a `where` clause starts on the line where its signature ends. A line that begins with `without` and a limit continues the line before it ([lexical.continuation-lines](02-lexical.md#lexical.continuation-lines)). So a `without` clause starts on the line where its signature or its header's path ends, or on the next line, and a header's clause may also follow a `;`.

Tests: [lexical/without_on_next_line_rejected.lt](../conformance/lexical/without_on_next_line_rejected.lt), [lexical/without_on_next_line.lt](../conformance/lexical/without_on_next_line.lt), [program/header_limits_on_path_line.lt](../conformance/program/header_limits_on_path_line.lt), [declarations/repeated_limit.lt](../conformance/declarations/repeated_limit.lt).

## Macros

<a id="syntax.macros"></a>
These productions declare pattern macros and procedural macros, and write the uses of macros. `TOKEN` is any token but a bracket, `$` and `;`. So a template ends at the separator after it, and a group holds any balanced tokens. The tokens of a use are read by the macro's arms once its name is resolved ([macros.matching](16-meta.md#macros.matching)), never by this grammar.

```ebnf
syntax      = "syntax" lower "{" [ macro_arm { SEP macro_arm } ] "}" ;
macro_arm   = ( "(" { matcher | SEP } ")" | "[" { matcher | SEP } "]" ) [ "$" lower ":" lower ] "=>" template ;
matcher     = "$" lower ":" ( lower | Upper | "type" )
            | "$" "(" { matcher | SEP } ")" [ "," | ";" ] ( "*" | "+" )
            | "(" { matcher | SEP } ")" | "[" { matcher | SEP } "]" | "{" { matcher | SEP } "}"
            | TOKEN ;
template    = t_item { t_item } ;
t_item      = "$" lower
            | "$" "(" { t_item | SEP } ")" [ "," | ";" ] ( "*" | "+" )
            | "(" { t_item | SEP } ")" | "[" { t_item | SEP } "]" | "{" { t_item | SEP } "}"
            | TOKEN ;
macro_use   = lower_path "!" ( "(" tokens ")" | "[" tokens "]" ) ;
tokens      = { TOKEN | SEP | "(" tokens ")" | "[" tokens "]" | "{" tokens "}" } ;
macro       = "macro" lower [ generics ] params "->" type [ "/" row ] [ limits ] block ;
```

Tests: [macros/expressions.lt](../conformance/macros/expressions.lt), [macros/repetitions.lt](../conformance/macros/repetitions.lt), [procedural/forms/](../conformance/procedural/forms/).

<a id="syntax.macro-checks"></a>
A fragment's kind is a word that the grammar reads as a `lower`, an `Upper` or `type`. Which words are kinds, a trailing block's kind, and the rest of a pattern macro's patterns and templates are checked after parsing ([macros.patterns](16-meta.md#macros.patterns), [macros.templates](16-meta.md#macros.templates)). `$` stands only in a `syntax` declaration and in a quote ([macros.splices](16-meta.md#macros.splices)), and is a syntax error everywhere else. A procedural macro's result type must be written, so `macro m(e: meta.Expr) { … }` is a syntax error at the `{`. Its generics, its `without` clause and the types of its parameters and result are checked after parsing ([macros.procedural-declarations](16-meta.md#macros.procedural-declarations)).

Tests: [macros/dollar.lt](../conformance/macros/dollar.lt), [procedural/declaration_errors.lt](../conformance/procedural/declaration_errors.lt), [macros/declaration_errors.lt](../conformance/macros/declaration_errors.lt), [procedural/result_type_written.lt](../conformance/procedural/result_type_written.lt).

## Names and paths

<a id="syntax.paths"></a>
A `use_path` takes names of either case after its first. So a `use` of an item, as `use std.sync.Shared`, parses, and name resolution reports it ([program.what-use-binds](04-programs.md#program.what-use-binds)).

```ebnf
lower_path  = lower { "." lower } ;
use_path    = lower { "." ( lower | Upper ) } ;
upper_path  = ( Upper | "Self" | lower_path "." Upper ) { "." Upper } ;
```

Tests: [names/item_import/](../conformance/names/item_import/), [program/namespace_import.lt](../conformance/program/namespace_import.lt).

## Types

<a id="syntax.types"></a>
Types are written by these productions.

```ebnf
type        = lower
            | upper_path [ "<" list1(type_arg) ">" ]
            | "(" list(elem_type) ")"
            | "{" list1(field) [ "," ".." ] "}"
            | fn_type
            | "handler" effect_ref [ "->" type ] [ "/" row ]
            | macro_use
            | q_splice ;
effect_ref  = upper_path [ "<" list1(type) ">" ] | "async" ;
type_arg    = type | [ "-" ] INT | "true" | "false" ;
fn_type     = "fn" [ "<" list1(fn_generic) ">" ] "(" list(param_type) ")" [ "->" type ] [ "/" row ] ;
fn_generic  = type_param | ".." type_param ;
param_type  = [ mode ] type | ".." type ;
elem_type   = type | ".." type ;
row         = row_elem | "{" list(row_elem) "}" ;
row_elem    = "io" | "async" | "raise" "<" type ">" | upper_path [ "<" list1(type) ">" ] | lower ;
```

Tests: [declarations/unit_and_tuples.lt](../conformance/declarations/unit_and_tuples.lt), [polymorphism/fields.lt](../conformance/polymorphism/fields.lt), [records/anonymous.lt](../conformance/records/anonymous.lt), [handlers/values.lt](../conformance/handlers/values.lt).

<a id="syntax.lowercase-types"></a>
A `lower` type is a primitive type name, which takes no type arguments, or, as a type argument, a value parameter ([generics.value-arguments](07-types.md#generics.value-arguments)).

Tests: [lexical/primitive_names_as_types.lt](../conformance/lexical/primitive_names_as_types.lt), [generics/value_arguments/](../conformance/generics/value_arguments/).

<a id="syntax.value-arguments"></a>
A named type's arguments may be values: `Mod<7>`, `Array<T, -1>`, `Flag<true>`, `Mod<PRIME>` and `Array<T, n>`. Whether each argument must be a type or a value, and whether a path names a type or a constant, are decided after parsing ([generics.value-arguments](07-types.md#generics.value-arguments)). So the grammar reads `Mod<PRIME>` and `Array<T, n>` as it reads `List<T>`. A value argument is never computed, so `Array<T, n + 1>` is a syntax error at the `+`.

Tests: [generics/value_arguments/](../conformance/generics/value_arguments/), [generics/placement_errors.lt](../conformance/generics/placement_errors.lt), [generics/equal_types.lt](../conformance/generics/equal_types.lt).

<a id="syntax.record-types-and-spreads"></a>
`{ f: T }` is an anonymous record type and `{ f: T, .. }` an open one ([records.anonymous-types](07-types.md#records.anonymous-types), [records.open-parameter-types](07-types.md#records.open-parameter-types)). `..T` spreads a pack among a tuple type's elements or a function type's parameters ([variadics.type-spreads](07-types.md#variadics.type-spreads)). Where each may stand, a record bound's `..`, and which spreads name packs are decided after parsing ([records.record-bounds](07-types.md#records.record-bounds), [variadics.packs](07-types.md#variadics.packs)).

Tests: [records/anonymous.lt](../conformance/records/anonymous.lt), [records/bounds.lt](../conformance/records/bounds.lt), [variadics/types.lt](../conformance/variadics/types.lt).

<a id="syntax.polymorphic-function-types"></a>
A function type's generics are type parameters only, never row variables, so `fn<e>()` is a syntax error at the `e` ([polymorphism.function-types](07-types.md#polymorphism.function-types)). Where a polymorphic function type may stand is decided after parsing ([polymorphism.placement](07-types.md#polymorphism.placement)). So is a pack among its generics, which a function type never has ([variadics.packs](07-types.md#variadics.packs)).

Tests: [generics/placement_errors.lt](../conformance/generics/placement_errors.lt), [polymorphism/arguments.lt](../conformance/polymorphism/arguments.lt), [polymorphism/placement_errors.lt](../conformance/polymorphism/placement_errors.lt).

<a id="syntax.closing-angle-brackets"></a>
`>>` is one token ([lexical.tokens](02-lexical.md#lexical.tokens)). Wherever two lists of type arguments end together, one `>>` closes both, as in `Map<str, List<i64>>`, at any depth: `List<List<List<i64>>>` ends with `>>` and then `>`. The `<…>` of `raise` counts as a list of type arguments, so `List<fn() / raise<E>>` ends with one `>>`.

Tests: [std/show.lt](../conformance/std/show.lt), [cycles/task_value.lt](../conformance/cycles/task_value.lt), [lexical/bodiless_signatures.lt](../conformance/lexical/bodiless_signatures.lt), [effects/raise_list_closing_brackets.lt](../conformance/effects/raise_list_closing_brackets.lt).

<a id="syntax.type-parentheses"></a>
`()` is the empty tuple, `(T)` is `T`, and `(T,)` is a one-element tuple.

Tests: [declarations/unit_and_tuples.lt](../conformance/declarations/unit_and_tuples.lt), [variadics/types.lt](../conformance/variadics/types.lt).

<a id="syntax.rows"></a>
A `/` after a function type gives the row to the innermost function type or handler type that has none yet ([declarations.function-types](10-declarations.md#declarations.function-types), [handlers.handler-types](12-effects.md#handlers.handler-types)). So in `fn() -> fn() / io / e`, the inner function type has the row `io`, and the outer one has `e`. In a row, `io` is the label, and any other `lower` is a row variable ([effects.rows](12-effects.md#effects.rows)).

Tests: [declarations/function_type_rows.lt](../conformance/declarations/function_type_rows.lt), [effects/rows.lt](../conformance/effects/rows.lt), [handlers/rows.lt](../conformance/handlers/rows.lt), [declarations/nested_function_type_rows.lt](../conformance/declarations/nested_function_type_rows.lt).

## Patterns

<a id="syntax.patterns"></a>
Parentheses work in patterns as they do in types: `(p)` is `p`, and `(p,)` is a one-element tuple. An anonymous record's pattern names a field or holds `..` ([records.anonymous-patterns](07-types.md#records.anonymous-patterns)). So `{}` is no pattern, and `catch {}` holds no arms.

```ebnf
pattern        = alt { "|" alt } ;
alt            = "_" | lower | [ "-" ] INT | STRING | "true" | "false"
               | upper_path [ "(" list1(pattern) ")" | "{" field_patterns "}" ]
               | "(" list(pattern) ")"
               | "{" ( field_pattern [ "," field_patterns ] | ".." [ "," ] ) "}"
               | "[" list_patterns "]"
               | macro_use
               | q_splice ;
field_patterns = { field_pattern "," } [ field_pattern | ".." [ "," ] ] ;
field_pattern  = ( lower | q_splice ) [ ":" pattern ] ;
list_patterns  = { pattern "," } [ pattern | ".." [ lower ] [ "," ] ] ;
```

Tests: [patterns/pattern_forms.lt](../conformance/patterns/pattern_forms.lt), [patterns/range_pattern.lt](../conformance/patterns/range_pattern.lt), [patterns/unit_pattern.lt](../conformance/patterns/unit_pattern.lt), [records/catch_patterns.lt](../conformance/records/catch_patterns.lt).

## Statements and blocks

<a id="syntax.blocks"></a>
A block is a sequence of statements, separated by `SEP`, in braces.

```ebnf
block       = "{" [ stmt { SEP stmt } ] "}" ;
stmt        = "let" binding
            | "var" binding
            | "assert" expr
            | "yield" expr
            | expr assign_op expr
            | expr ;
binding     = pattern [ ":" type ] "=" expr ;
assign_op   = "=" | "+=" | "-=" | "*=" | "/=" | "%=" | "+%=" | "-%=" | "*%="
            | "&=" | "|=" | "^=" | "<<=" | ">>=" ;
```

Tests: [expressions/block_values.lt](../conformance/expressions/block_values.lt), [lexical/separators.lt](../conformance/lexical/separators.lt), [lexical/misplaced_separators/](../conformance/lexical/misplaced_separators/).

<a id="syntax.record-literal-braces"></a>
A `{` followed by a `lower` and a `:`, or by `..`, begins an anonymous record literal or an update, not a block ([records.anonymous-literals](07-types.md#records.anonymous-literals), [records.update](07-types.md#records.update)). So `{ x }` is a block and `{ x: x }` is a record. Like the braces of a struct literal, these braces can't stand unparenthesized in a head ([expressions.heads](08-expressions.md#expressions.heads)). `(..e)` is a tuple even with one element, because `..` makes a spread ([variadics.spread-expressions](07-types.md#variadics.spread-expressions)).

Tests: [records/anonymous.lt](../conformance/records/anonymous.lt), [records/update.lt](../conformance/records/update.lt), [expressions/block_values.lt](../conformance/expressions/block_values.lt).

<a id="syntax.statements"></a>
`yield` is a statement. The checks after parsing allow it only in a projection's body ([projections.yield](13-modes.md#projections.yield)). Whether `let p = e else x` is a let-else or a fallback depends on `p` ([patterns.let-else](09-patterns.md#patterns.let-else)): the grammar reads both as a `let` whose value is `e else x`.

Tests: [projections/reads.lt](../conformance/projections/reads.lt), [patterns/let_else.lt](../conformance/patterns/let_else.lt), [expressions/assignment_not_expression.lt](../conformance/expressions/assignment_not_expression.lt).

## Expressions

<a id="syntax.expressions"></a>
Expressions are written by these productions, which [syntax.heads](#syntax.heads) and [syntax.ambiguities](#syntax.ambiguities) complete.

```ebnf
expr          = ( "-" | "!" ) expr
              | expr binary_op expr
              | expr "else" expr
              | "try" expr [ "catch" ( catch_arm | "{" arms(catch_arm) "}" ) ]
              | "raise" expr
              | "return" [ expr ]
              | "break"
              | "continue"
              | "|" list(closure_param) "|" expr
              | "||" expr
              | "resume" "(" [ expr ] ")"
              | postfix ;
binary_op     = "*" | "/" | "%" | "*%" | "+" | "-" | "+%" | "-%" | "<<" | ">>"
              | "&" | "^" | "|" | "==" | "!=" | "<" | "<=" | ">" | ">="
              | "&&" | "||" ;
postfix       = path
              | built ;
path          = ( lower | Upper ) { "." ( lower | Upper ) } ;
built         = primary
              | path "." ( INT | "await" )
              | built "." ( lower | Upper | INT | "await" )
              | postfix "(" list(arg) ")"
              | postfix "[" expr "]"
              | postfix "." q_splice ;
arg           = [ "inout" ] expr | ".." expr | q_spread ;
primary       = INT | FLOAT | STRING | interpolated | "true" | "false"
              | "self" | "Self" | "?"
              | "." ( lower | INT )
              | "(" list(elem) ")"
              | "[" list(elem) "]"
              | "{" ( lower | q_splice ) ":" expr { "," field_init } [ "," ] "}"
              | "{" q_spread { "," field_init } [ "," ] "}"
              | "{" ".." expr { "," field_init } [ "," ] "}"
              | struct
              | block
              | if
              | "match" head "{" arms(match_arm) "}"
              | "loop" block
              | "while" head block
              | "for" pattern "in" iterable block
              | "comptime" ( if | "match" head "{" arms(match_arm) "}" | "for" pattern "in" iterable block )
              | macro_use [ "{" tokens "}" ]
              | "handler" effect_ref [ "->" type ] "{" [ fn { SEP fn } ] "}"
              | "with" list1(head) block
              | "when" list1(lower) block
              | "unsafe" "because" STRING block
              | quote
              | q_splice ;
struct        = ( path | "Self" ) "{" ( ".." expr { "," field_init } [ "," ] | list(field_init) ) "}" ;
elem          = expr | ".." expr | q_spread ;
field_init    = lower [ ":" expr ] | q_splice ":" expr | q_spread ;
if            = "if" ( "let" pattern "=" head | Upper ":" bounds | head ) block [ "else" ( block | if ) ] ;
iterable      = head [ ( ".." | "..=" ) head ] ;
match_arm     = pattern [ "if" expr ] "=>" expr ;
catch_arm     = pattern [ "if" expr | "because" STRING ] "=>" expr ;
arms(a)       = [ a { ( SEP | "," ) a } [ SEP | "," ] ] ;
closure_param = "inout" lower [ ":" type ]
              | alt [ ":" type ] ;
interpolated  = STRING_HEAD splice { STRING_MID splice } STRING_TAIL ;
splice        = expr [ FORMAT ] ;
quote         = "quote" ( block | "type" "{" type "}" | "pattern" "{" pattern "}" | "field" "{" field_init "}" ) ;
q_splice      = "$" ( lower | "(" expr ")" ) ;
q_spread      = "$" ".." ( lower | "(" expr ")" ) ;
```

Tests: [expressions/precedence_levels.lt](../conformance/expressions/precedence_levels.lt), [expressions/closure_forms.lt](../conformance/expressions/closure_forms.lt), [expressions/loop_forms.lt](../conformance/expressions/loop_forms.lt), [expressions/question_mark_operator.lt](../conformance/expressions/question_mark_operator.lt).

<a id="syntax.expression-paths"></a>
A `path` is a chain of identifiers, such as `fs.read` or `shapes.Circle`, which stands for a name followed by fields: `fs.read` is the field `read` of `fs`. Only a path, or `Self`, can come before the `{` of a struct literal, and the path's last name must be an `Upper` ([expressions.struct-literals](08-expressions.md#expressions.struct-literals)). So `orders.Order { … }` is a struct literal, while `f() { … }` and `(A) { … }` are syntax errors at the `{`.

Tests: [expressions/struct_after_call.lt](../conformance/expressions/struct_after_call.lt), [expressions/struct_after_parens.lt](../conformance/expressions/struct_after_parens.lt), [expressions/qualified_struct_literal/](../conformance/expressions/qualified_struct_literal/), [expressions/struct_lowercase_name.lt](../conformance/expressions/struct_lowercase_name.lt).

<a id="syntax.key-paths"></a>
The `.` that starts a key path is a primary, and the rest of the key path is built on it as fields, calls and indexes ([expressions.key-paths](08-expressions.md#expressions.key-paths)).

Tests: [types/key_paths.lt](../conformance/types/key_paths.lt), [expressions/key_path_forms.lt](../conformance/expressions/key_path_forms.lt), [lexical/leading_dot_key_path.lt](../conformance/lexical/leading_dot_key_path.lt).

<a id="syntax.holes-before-dots"></a>
`?` is always a hole, so `?.len()` is a call of the field `len` of a hole, and `?..3` a range from a hole ([types.hole-before-dot](07-types.md#types.hole-before-dot)).

Tests: [lexical/bare_hole_before_range.lt](../conformance/lexical/bare_hole_before_range.lt), [lexical/hole_before_dot_rejected.lt](../conformance/lexical/hole_before_dot_rejected.lt), [lexical/question_dot_is_two_tokens.lt](../conformance/lexical/question_dot_is_two_tokens.lt).

<a id="syntax.macro-uses"></a>
A `macro_use` is a primary, so `swap!(a, b)` stands as a statement and `m!(x).len()` calls a method of its expansion. Its trailing block starts on the line where its group ends, because a newline after the `)` or `]` ends the use ([lexical.terminator-insertion](02-lexical.md#lexical.terminator-insertion)). In a head, a use has no trailing block ([macros.uses](16-meta.md#macros.uses)). In a pattern, a use takes no trailing block either, and neither does a use in a type. A use in a type stands for a procedural macro whose result is a type ([macros.procedural-uses](16-meta.md#macros.procedural-uses)).

Tests: [macros/expressions.lt](../conformance/macros/expressions.lt), [procedural/newlines/](../conformance/procedural/newlines/), [macros/patterns.lt](../conformance/macros/patterns.lt).

<a id="syntax.quotes"></a>
A quote holds a block, or, after `type`, `pattern` or `field`, one form of that kind in braces ([macros.quote](16-meta.md#macros.quote)). Its splices, `$x` and `$(e)`, and its spreads, `$..x` and `$..(e)`, stand only inside a quote. Where a splice may stand, by its value's type, and which spreads a list holds are checked after parsing ([macros.splices](16-meta.md#macros.splices)). In a quote, a `{` followed by a spread, or by a splice and a `:`, begins an anonymous record literal, never a block.

Tests: [procedural/quote_syntax.lt](../conformance/procedural/quote_syntax.lt), [procedural/forms/](../conformance/procedural/forms/), [procedural/splices/](../conformance/procedural/splices/).

<a id="syntax.effect-forms"></a>
In a row, an `Upper` path is an effect ([handlers.effects-in-rows](12-effects.md#handlers.effects-in-rows)), and `async` the effect of [tasks.async](14-tasks.md#tasks.async). `Name.op(…)` is a call of a field of a path, which name resolution reads as a performance when `Name` is an effect ([handlers.performing-operation](12-effects.md#handlers.performing-operation)). `t.await()` reads `await`, a keyword, as a member's name ([tasks.std-task](14-tasks.md#tasks.std-task)). The handlers of a `with` are heads, so a handler literal is written in parentheses there, or bound first ([handlers.with](12-effects.md#handlers.with)).

Tests: [handlers/values.lt](../conformance/handlers/values.lt), [tasks/tasks.lt](../conformance/tasks/tasks.lt), [handlers/rows.lt](../conformance/handlers/rows.lt), [handlers/basic.lt](../conformance/handlers/basic.lt).

<a id="syntax.staging-annotations"></a>
`comptime` stands only before an `if`, a `match` or a `for`. The `else` of an `if` is followed by a block or an `if`, never by `comptime`, so an annotation covers its whole chain ([meta.staging-annotations](16-meta.md#meta.staging-annotations)).

Tests: [staging/syntax_errors.lt](../conformance/staging/syntax_errors.lt), [staging/branches.lt](../conformance/staging/branches.lt).

<a id="syntax.bound-tests"></a>
After `if`, an `Upper` followed by `:` begins a bound test, `if T: Show`, whose bounds end at the block. So a bound test is the whole condition of an `if` or an `else if` and stands nowhere else: `if a && T: Show` is a syntax error at the `:` ([meta.bound-tests](16-meta.md#meta.bound-tests)). Whether `T` names a type parameter is decided by resolving names.

Tests: [reflection/bound_test_syntax.lt](../conformance/reflection/bound_test_syntax.lt), [reflection/bound_tests.lt](../conformance/reflection/bound_tests.lt).

<a id="syntax.closure-parameters"></a>
A closure parameter marked `inout` is a name, never another pattern, so `|inout (a, b)|` is a syntax error at the `(` ([expressions.closures](08-expressions.md#expressions.closures)).

Tests: [expressions/closure_inout_not_a_pattern.lt](../conformance/expressions/closure_inout_not_a_pattern.lt), [expressions/closure_inout_parameters.lt](../conformance/expressions/closure_inout_parameters.lt).

## Heads

<a id="syntax.heads"></a>
`head` is the grammar of the heads of [expressions.heads](08-expressions.md#expressions.heads). It is `expr` without these forms:

- the `primary` forms `struct`, `block`, `if`, `match`, `loop`, `while`, `for`, `with`, `when` and `unsafe`, the handler literal and the staging annotations;
- the block form of `catch`;
- the trailing block of a `macro_use`.

Inside a `head`, every `expr` that appears within `(…)` or `[…]`, as an argument, an index or an interpolation, is a full `expr` again. Every other `expr` inside a head is a `head`, as are the guard and the body of a `catch_arm` and the body of a closure.

Tests: [expressions/head_struct_literal.lt](../conformance/expressions/head_struct_literal.lt), [expressions/head_catch_block.lt](../conformance/expressions/head_catch_block.lt), [expressions/bracketed_heads.lt](../conformance/expressions/bracketed_heads.lt), [expressions/parenthesized_heads.lt](../conformance/expressions/parenthesized_heads.lt).

## Settling ambiguities

<a id="syntax.ambiguities"></a>
The productions are ambiguous on their own. The rules of this section, with [syntax.closing-angle-brackets](#syntax.closing-angle-brackets) and [syntax.rows](#syntax.rows), settle every ambiguity, and nothing else does.

Tests: [expressions/precedence_levels.lt](../conformance/expressions/precedence_levels.lt), [expressions/chained_comparison.lt](../conformance/expressions/chained_comparison.lt), [expressions/bar_token.lt](../conformance/expressions/bar_token.lt).

<a id="syntax.operator-precedence"></a>
Operators bind as the precedence table of [expressions.precedence](08-expressions.md#expressions.precedence) says. Prefix `-` and `!` bind more tightly than every binary operator, and comparisons don't chain.

Tests: [expressions/precedence_levels.lt](../conformance/expressions/precedence_levels.lt), [expressions/chained_comparison.lt](../conformance/expressions/chained_comparison.lt).

<a id="syntax.longest-operands"></a>
The operand of `try`, `raise` and `return`, the body of a closure and the body of a `catch_arm` extend as far to the right as they can ([expressions.precedence](08-expressions.md#expressions.precedence)). `return` takes an operand whenever the next token can start one in that position, so `return -1` returns `-1`. In a head, `{` never starts an operand, so `if return {` is `if (return) {`. `break`, `continue` and a `return` with no operand are complete expressions, and can be the left operand of a binary operator: `return + 1` means `(return) + 1`.

Tests: [expressions/precedence_levels.lt](../conformance/expressions/precedence_levels.lt), [expressions/return_in_head.lt](../conformance/expressions/return_in_head.lt), [expressions/closure_return.lt](../conformance/expressions/closure_return.lt).

<a id="syntax.catch-attachment"></a>
A `catch` belongs to the innermost `try` whose operand is still open where the `catch` appears ([expressions.precedence](08-expressions.md#expressions.precedence)). In `try a(try b()) catch …`, the inner operand closed at `)`, so the `catch` belongs to the outer `try`.

Tests: [expressions/catch_binding.lt](../conformance/expressions/catch_binding.lt), [effects/closure_in_catch_operand.lt](../conformance/effects/closure_in_catch_operand.lt), [effects/raise_and_catch.lt](../conformance/effects/raise_and_catch.lt).

<a id="syntax.else-attachment"></a>
An `else` directly after the block of an `if` belongs to that `if` ([expressions.else-after-if](08-expressions.md#expressions.else-after-if)).

Tests: [expressions/else_after_if.lt](../conformance/expressions/else_after_if.lt), [expressions/if_else_chains.lt](../conformance/expressions/if_else_chains.lt), [expressions/if_let_chains.lt](../conformance/expressions/if_let_chains.lt).

<a id="syntax.if-let-heads"></a>
The pattern of an `if let` ends at the `=` after it, which no pattern holds. Its head ends at the first `{` outside parentheses and brackets, as every head does. An `else` before that `{` doesn't follow a block, so it is the fallback inside the head. The `let` of an `if let` is no statement, so it is never a let-else ([expressions.option-fallback](08-expressions.md#expressions.option-fallback), [expressions.let-else](08-expressions.md#expressions.let-else), [expressions.if](08-expressions.md#expressions.if)). So `if let Some(x) = a else b {` matches `a else b`.

A line that ends with the pattern or the head inserts a terminator, unless the next line begins with the `|` of another alternative. That terminator is a syntax error before the `=` or the `{`. A line that ends with `let` or `=` continues. So every `if let` parses one way.

Tests: [expressions/if_let.lt](../conformance/expressions/if_let.lt), [expressions/if_let_chains.lt](../conformance/expressions/if_let_chains.lt), [expressions/if_let_loops.lt](../conformance/expressions/if_let_loops.lt), [expressions/if_let_head_fallback.lt](../conformance/expressions/if_let_head_fallback.lt), [expressions/if_let_line_breaks.lt](../conformance/expressions/if_let_line_breaks.lt).

<a id="syntax.range-precedence"></a>
`..` and `..=` bind more loosely than every operator ([expressions.ranges](08-expressions.md#expressions.ranges)).

Tests: [expressions/ranges.lt](../conformance/expressions/ranges.lt), [expressions/range_outside_for.lt](../conformance/expressions/range_outside_for.lt), [lexical/range_starts_line.lt](../conformance/lexical/range_starts_line.lt).

<a id="syntax.expression-parentheses"></a>
`(e)` is `e`, `(e,)` is a one-element tuple, and `()` is the empty tuple.

Tests: [expressions/parenthesized_heads.lt](../conformance/expressions/parenthesized_heads.lt), [declarations/unit_and_tuples.lt](../conformance/declarations/unit_and_tuples.lt), [lexical/digits_after_dot.lt](../conformance/lexical/digits_after_dot.lt).

## Doc comments

<a id="syntax.doc-comment-runs"></a>
The parser reads doc comments as `DOC` tokens, which are made from the comments ([program.doc-comments](04-programs.md#program.doc-comments)). A run of `///` comments on consecutive lines, each alone on its line, becomes one `DOC` token, placed just before the first token of the next line. A line that holds only separators counts as a line without code.

Tests: [program/misplaced_docs/](../conformance/program/misplaced_docs/), [lexical/doc_comments_hold_code.lt](../conformance/lexical/doc_comments_hold_code.lt), [lexical/four_slashes.lt](../conformance/lexical/four_slashes.lt).

<a id="syntax.doc-comment-placement"></a>
The grammar accepts a `DOC` only directly before a declaration. Any other doc comment is a syntax error, reported at its first comment:

- a run followed by anything other than a declaration;
- a run whose next line holds no code;
- a doc comment that shares its line with code.

Tests: [program/misplaced_docs/](../conformance/program/misplaced_docs/), [lexical/doc_comment_after_code.lt](../conformance/lexical/doc_comment_after_code.lt).

<a id="syntax.doc-comment-text"></a>
A doc line's text is the comment's text without one leading space. It ends before any `//~`, which starts an annotation ([lexical.annotations](02-lexical.md#lexical.annotations)), and before the spaces that precede that `//~`.

Tests: [lexical/example_comments.lt](../conformance/lexical/example_comments.lt), [program/doc_examples.lt](../conformance/program/doc_examples.lt).

<a id="syntax.doc-examples"></a>
A doc line whose text, after `///` and any spaces, starts with `ex:` is an example, and one that starts with `prop:` is a property ([tests.prop-lines](19-tools.md#tests.prop-lines)). The text after `ex:` or `prop:` is lexed as a file is, starting at its position in the file, and must then parse as an `expr`.

Tests: [program/doc_examples.lt](../conformance/program/doc_examples.lt), [program/doc_example_errors.lt](../conformance/program/doc_example_errors.lt), [protocol/syntax_errors_per_part/bad_example.lt](../conformance/protocol/syntax_errors_per_part/bad_example.lt), [properties/syntax_error.lt](../conformance/properties/syntax_error.lt).

## Syntax errors

<a id="syntax.grammar-errors"></a>
Every grammar error is E0100, *syntax error*. A grammar error is at the first token from which no program can continue. A misplaced doc comment is at its first comment instead ([syntax.doc-comment-placement](#syntax.doc-comment-placement)). Which errors are syntax errors, and what a file with one reports, is given in [errors.syntax-errors](18-errors.md#errors.syntax-errors).

Tests: [protocol/syntax_errors_per_part/broken.lt](../conformance/protocol/syntax_errors_per_part/broken.lt), [program/syntax_error_in_function.lt](../conformance/program/syntax_error_in_function.lt), [lexical/missing_commas/](../conformance/lexical/missing_commas/), [program/misplaced_docs/](../conformance/program/misplaced_docs/).

<a id="syntax.inserted-token-positions"></a>
An inserted separator is on the line of the token before it ([lexical.terminator-positions](02-lexical.md#lexical.terminator-positions)). The end of the file is just after the file's last token, so an error at the end of a file is reported on the line of its last token. A part parsed alone ([syntax.parts](#syntax.parts)) ends where the separator after it is, or at the end of the file.

Tests: [lexical/end_of_file_error.lt](../conformance/lexical/end_of_file_error.lt), [lexical/no_terminator_in_parentheses.lt](../conformance/lexical/no_terminator_in_parentheses.lt), [lexical/brace_on_next_line.lt](../conformance/lexical/brace_on_next_line.lt).

<a id="syntax.lexical-errors"></a>
The parser reads the tokens before the first lexical error, without any separator that [lexical.terminator-insertion](02-lexical.md#lexical.terminator-insertion) would insert after the last of them. If it accepts all of them, the lexical error is reported.

Tests: [protocol/syntax_errors_per_part/grammar_before_lexical.lt](../conformance/protocol/syntax_errors_per_part/grammar_before_lexical.lt), [protocol/syntax_errors_per_part/lexical_before_grammar.lt](../conformance/protocol/syntax_errors_per_part/lexical_before_grammar.lt), [lexical/malformed_integers/](../conformance/lexical/malformed_integers/).

<a id="syntax.first-error"></a>
A part's first syntax error is the earliest, by line and then by column, of these errors:

- its grammar error;
- the lexical error that ends it;
- the errors in its doc examples and properties.

An error in the encoding of the file ([lexical.source-text](02-lexical.md#lexical.source-text)) is the exception: it is always the file's only error.

Tests: [protocol/syntax_errors_per_part/](../conformance/protocol/syntax_errors_per_part/), [lexical/source_text/](../conformance/lexical/source_text/), [protocol/syntax_errors_per_part/bad_example.lt](../conformance/protocol/syntax_errors_per_part/bad_example.lt).

<a id="syntax.parts"></a>
The tokens of a file, after [lexical.separators](02-lexical.md#lexical.separators), are cut into parts. A cut falls before each of these tokens that follows a `SEP` outside every bracket, where a closing bracket closes the innermost open one:

- `use`, `impl`, `pub`, `extern`, `fn`, `type`, `trait`, `const`, `test`, `syntax`, `effect`, `macro` and `DOC`;
- each `meta` that `use` follows;
- each word that another language begins a declaration with, when a `lower` or an `Upper` follows it: `def`, `func`, `function`, `fun`, `struct`, `class`, `enum`, `interface`, `protocol`, `extension`, `let` and `var`; and `async` and `mutating` when `fn` follows them.

Each part is parsed alone as a `file`.

A part that has a grammar error, or that a lexical error ends, ends early. It ends at the first later line that starts in its first column with one of the words of the first two items, the words of other languages left out. That line is no earlier than the line of the part's error, and is after it for a lexical error. It counts even inside a bracket the part leaves open, or past the lexical error. Reading resumes there, or at the `DOC` of the declaration there, and that text is lexed and read as a file is. The block of a trait or an impl whose part breaks after its `{` is cut the same way inside it, without resuming.

Each part reports its first syntax error and nothing else that lies in it ([errors.part-reports](18-errors.md#errors.part-reports)). A file without syntax errors is parsed whole, so reading in parts changes none of the trees that `parse --sexp` prints.

Checked by: `just parse`, which compares each file's first syntax errors under the compiler's parser and the reference interpreter's, over the conformance suite, generated programs and edits of them that plant syntax errors (`tools/runner/src/judge.rs`); the conformance tests of [errors.part-reports](18-errors.md#errors.part-reports) check what each part reports.

## The canonical format

<a id="syntax.format"></a>
There is one canonical format, which `stilt fmt` writes. The format depends on the syntax tree and the comments, never on where the source broke its lines. So two sources with one tree have one text, and path-and-hash edits hash one text ([edits.canonical-text](19-tools.md#edits.canonical-text)).

Tests: [lexical/six_constructs.lt](../conformance/lexical/six_constructs.lt).

Checked by: the formatter's tests (`compiler/stilt-fmt/tests/formatting.rs`), which format each input of `tests/format/` to the output paired with it, and format the conformance suite, the guide's examples and generated programs twice, checking that the second pass changes nothing and that the text keeps its tree.

<a id="syntax.format.indentation"></a>
Indentation is two spaces per level, and columns are never aligned.

Checked by: the pair `tests/format/indentation`.

<a id="syntax.format.braces"></a>
A brace opens on the same line as its construct. So these braces go with their `else` or `catch`, on the line where the expression before them ends:

- the block of a let-else, as in `let n = "12".to_i64() else {`, or of an expression-level `else`;
- the braces of a `catch` around its arms;
- the block that is the arm's body of a `catch` with one arm and no braces, as in `try f() catch e because "…" => {`.

The statements or arms inside them go one level deeper than that line.

Checked by: the pairs `braces`, `fallback_braces`, `let_else_breaks` and `nested_catch` of `tests/format/`.

<a id="syntax.format.short-blocks"></a>
If the whole line fits in 100 columns, a block of one statement or expression goes on one line, as in `if qty <= 0 { raise "…" }`. Every other block has one statement per line.

Checked by: the pairs `short_blocks`, `short_block_boundary` and `nested_blocks` of `tests/format/`.

<a id="syntax.format.if-chains"></a>
If the whole line fits, an `if` with an `else` is written on one line, `if let` and `else if let` included ([expressions.if](08-expressions.md#expressions.if)). Otherwise every branch is a block of its own lines: `if c {`, its statements, `} else if d {`, …, `} else {`, …, `}`.

Checked by: the pairs `if_chains`, `if_chain_in_closure`, `if_let_chain` and `if_let` of `tests/format/`.

<a id="syntax.format.arms"></a>
The arms of a `match`, and of a `catch` in block form, are written one per line, so a block that holds one is never written on one line.

Checked by: the pair `tests/format/arms`.

<a id="syntax.format.type-declarations"></a>
If it fits in 100 columns, a record or variant type is written on one line, as in `type Shape = | Circle(f64) | Square(f64)`. Otherwise each field or variant is written on a line of its own. Each field is then followed by a comma, the last one too, as each element of a broken list is.

Checked by: the pairs `type_declarations`, `record_last_list` and `record_last_function` of `tests/format/`.

<a id="syntax.format.line-width"></a>
A construct goes on one line when the whole line fits in 100 columns. Otherwise it breaks in these ways:

- An argument list, a parameter list, a list, a tuple, a record literal, a pattern or a payload has one element per line, with a comma after each. Its closing bracket goes on a line of its own.
- A binary expression breaks after each operator.
- A chain of two or more calls puts each call on a line of its own after a `.`.
- A call whose last argument is a closure with a block keeps its line up to the block's brace.
- Alternatives break before each `|`.

Checked by: the pairs `wrapped_arguments`, `wrapped_patterns`, `wrapped_operators`, `method_chains`, `closure_blocks`, `trailing_commas` and `negation` of `tests/format/`.

<a id="syntax.format.signatures"></a>
If a signature with a `without` clause fits on one line with the clause and the body's `{`, it goes on that line. Otherwise the clause starts the next line, a level in, followed by the `{`. The signature before it is then laid out as a signature that has no clause. A signature that doesn't fit breaks its parameter list first. Its return type breaks only when `) -> T {` still doesn't fit on its own line, or `) -> T` before a clause on the next line. A function type, as in `fn(str) -> T`, breaks its parameter list before its return type in the same way.

Checked by: the pairs `wrapped_signatures`, `parameters_first`, `return_type_breaks` and `without_clauses` of `tests/format/`.

<a id="syntax.format.literal-lists"></a>
Here, a literal is a number, possibly negated, a string or a boolean. A list whose elements are all literals fills each line with as many elements as fit in 100 columns, each followed by a comma. Its lines are one level deeper than the line that opens it, and its closing bracket is on a line of its own. A list that holds a comment, or any element that isn't a literal, keeps one element per line. A nested list of literals is not a literal, so a table written as a list of rows keeps one row per line.

Checked by: the pairs `literal_list`, `mixed_list`, `literal_rows` and `commented_list` of `tests/format/`.

<a id="syntax.format.comments"></a>
A comment keeps its line, and breaks the construct that holds it.

Checked by: the pairs `comments` and `commented_list` of `tests/format/`.

<a id="syntax.format.separators"></a>
The formatter never writes `;` ([lexical.explicit-separators](02-lexical.md#lexical.explicit-separators)) or a comma between arms. Every statement and arm it writes ends its line.

Checked by: the pairs `separators`, `arms` and `module_header` of `tests/format/`.

<a id="syntax.format.punning"></a>
A record field whose value is a variable with the field's name is written punned: `stilt fmt` turns `Order { customer: customer }` into `Order { customer }`, and does the same in record patterns.

Checked by: the pair `tests/format/punning`.

<a id="syntax.no-options"></a>
The formatter has no configuration options.

Checked by: the formatter's tests (`compiler/stilt-fmt/tests/formatting.rs`), which give it none.

<a id="syntax.formatter-tests"></a>
The formatter is not part of the conformance contract. Its rules are tested by the formatter's tests in `tests/format/`, each an input file paired with its expected output. Each expected output is derived from this chapter's rules by hand, never by running the formatter.

Checked by: `just formatter` (`compiler/stilt-fmt/tests/formatting.rs`).

## Tree form

<a id="syntax.tree-form"></a>
`parse --sexp` prints one line per source file, in order of path: `(file "PATH" MODULE)`. If any file has a syntax error, it prints nothing on stdout, writes the syntax errors that `check` reports to stderr, one line each, and exits with status 1.

Checked by: `just parse`, which compares the trees that the compiler's parser and the reference interpreter's print (`tools/runner/src/judge.rs`).

<a id="syntax.tree-form.conventions"></a>
A node is a list in parentheses, with its elements separated by single spaces, and its first element names the node, except where the tables below say otherwise. Identifiers are printed as written, and a path as its names joined by `.`. Number literals are printed as written, without `_`, and a negative integer pattern starts with `-`. Strings are quoted and escaped as a string nested inside another value is shown ([std.show-names-and-escapes](17-std.md#std.show-names-and-escapes)).

Checked by: `just parse`, as for [syntax.tree-form](#syntax.tree-form).

<a id="syntax.tree-form.normalizations"></a>
Parentheses that only group leave no trace. A punned field `f` is printed like `f: f`, as `(f f)`. A missing return type prints as `(tuple)`, and a missing row as `(row)`. A path in an expression is a name followed by fields, so `fs.read` is `(field fs read)`. A method call `e.m(a)` is a call of a field, `(call (field e m) a)`. Interpolated strings drop their empty text parts.

Checked by: `just parse`, as for [syntax.tree-form](#syntax.tree-form).

<a id="syntax.tree-form.declarations"></a>
Programs and declarations print as this table says.

| Syntax | Tree |
| --- | --- |
| A module | `(module HEADER? ITEM…)` |
| `module a.b` with limits | `(header a.b LIMITS…)`, where each `without` clause is `(without LIMIT…)`, such as `(without panic alloc)` |
| `use a.b` | `(use a.b)` |
| `meta use a.b` | `(meta-use a.b)` |
| `pub` before a declaration | `(pub DECL)` |
| `pub extern` before a function | `(pub (extern FN))` |
| A foreign function | `(extern FN)`, and `(pub (extern FN))` with `pub`, where `FN` has no `BODY` |
| Doc comments before a declaration | `(doc LINE… DECL)`, where a line is its text as a string, `(ex EXPR)` for an example, or `(prop EXPR)` for a property. `doc` wraps `pub` |
| A function | `(fn NAME (GENERIC…) (PARAM…) RETURN ROW LIMITS? BODY)`, where `RETURN` is the result type, or `(inout T)` for a projection, `LIMITS` is `(without LIMIT…)` when the function has a clause, and `BODY` is a block, `?` for `= ?`, or absent for a trait method without a body and a foreign function |
| A generic | `T`, `(T BOUND…)`, `(.. T)` or `(.. T BOUND…)` for a pack, a row variable `e`, or `(value n T)` for a value parameter, where a bound is its path, `(PATH T…)` with type arguments, or an anonymous record type for a record bound |
| A parameter | `(x T)`, `(inout x T)`, `(escaping x T)`, `self`, `(inout self)`, `(self T)` or `(inout self T)` |
| A record type | `(type NAME (TYPE_PARAM…) (record (FIELD T)…))`, where a type parameter is its name, `(.. NAME)` for a pack, or `(value n T)` for a value parameter |
| A variant type | `(type NAME (TYPE_PARAM…) (variants VARIANT…))`, where a variant is `Name` or `(Name PAYLOAD…)`, and a payload is `T` or `(name T)` |
| A trait | `(trait NAME MEMBER…)`, or `(trait NAME (params P…) MEMBER…)` with parameters, where a member is a function or `(const NAME T)`, `(const NAME T EXPR)` with a default |
| A constant | `(const NAME T EXPR)` |
| A test | `(test "name" BLOCK)` |
| An effect | `(effect NAME (P…)? OP…)`, where a type parameter list is `(params P…)` and an operation is `(op NAME (PARAM…) RETURN ROW)`, as a function's head |
| A macro | `(syntax NAME ARM…)`, where an arm is `(arm GROUP BLOCK? (template T…))`, its trailing block `(frag NAME KIND)`, a fragment `(frag NAME KIND)`, a repetition `(rep SEP OP M…)` with `SEP` `,`, `;` or `_` for none, a group `(paren M…)`, `(bracket M…)` or `(brace M…)`, and in a template `$x` is `(frag x)` |
| A procedural macro | `(macro-decl NAME (GENERIC…) (PARAM…) RETURN ROW LIMITS? BLOCK)`, as a function's |
| An inherent impl | `(impl (GENERIC…) T MEMBER…)` |
| A trait impl | `(impl-trait (GENERIC…) TRAIT T MEMBER…)`, where `TRAIT` is its path, or `(PATH T…)` with arguments |
| A `where` clause | `(where (PATH BOUND…)…)`, after the function's `ROW` and before its `LIMITS`, and after an impl's `T` |

Checked by: `just parse`, as for [syntax.tree-form](#syntax.tree-form).

<a id="syntax.tree-form.types"></a>
Types print as this table says.

| Syntax | Tree |
| --- | --- |
| A named type | Its path, such as `i64` or `m.T`, or `(PATH T…)` with type arguments, such as `(List Order)`, where a literal argument is its atom, as in `(Mod 7)`, `(Array T -1)` and `(Flag true)` |
| A tuple | `(tuple T…)`, and `(tuple)` for `()`, where an element is `T` or `(.. T)` for a spread |
| An anonymous record type | `(record-type (FIELD T)…)`, ending with `..` for an open one |
| A function type | `(fn (PARAM_TYPE…) RETURN ROW)`, where a parameter type is `T`, `(inout T)` or `(.. T)`, and `(fn (GENERIC…) (PARAM_TYPE…) RETURN ROW)` for a polymorphic one |
| A row | `(row ELEMENT…)`, where an element is `io`, `async`, `(raise T)`, an effect, as a named type is, or a row variable |
| A handler type | `(handler EFFECT RETURN? ROW)`, where `EFFECT` is as a handler literal's, and `RETURN` is `(-> T)` when one is written |
| A macro use | `(macro PATH GROUP)`, its tokens unexpanded |

Checked by: `just parse`, as for [syntax.tree-form](#syntax.tree-form).

<a id="syntax.tree-form.patterns"></a>
Patterns print as this table says.

| Syntax | Tree |
| --- | --- |
| `_`, a binding `x`, a literal | `_`, `x`, the literal |
| A constant or a variant without a payload | Its path |
| A variant with a payload | `(PATH P…)` |
| A record pattern | `(record PATH (FIELD P)…)`, ending with `..` when the pattern holds `..`, and `(record _ (FIELD P)…)` for an anonymous one |
| A tuple | `(tuple P…)` |
| A list | `(list P…)`, ending with `..` or `(.. rest)` when the pattern has a rest |
| Alternatives | `(or P…)` |
| A macro use | `(macro PATH GROUP)`, its tokens unexpanded |
| A pattern with a type, in `let`, `var` or a closure | `(: P T)` |

Checked by: `just parse`, as for [syntax.tree-form](#syntax.tree-form).

<a id="syntax.tree-form.expressions"></a>
Expressions and statements print as this table says.

| Syntax | Tree |
| --- | --- |
| A literal, a name, `self`, `Self`, a hole | The atom: `1000`, `2.5e-3`, `"a"`, `true`, `x`, `self`, `Self`, `?` |
| An interpolated string | `(interp PART…)`, where a part is a string, `(splice EXPR)` or `(splice EXPR "spec")` |
| The `.` that starts a key path | `.`, so `.name.len()` is `(call (field (field . name) len))` |
| A tuple, a list | `(tuple E…)`, `(list E…)` |
| A field, a call, an index | `(field E name)`, `(call E ARG…)`, `(index E E)`, where an argument is `E` or `(inout E)` |
| A struct literal | `(struct PATH (FIELD E)…)`, or `(struct PATH (.. E) (FIELD E)…)` for an update |
| An anonymous record literal | `(record-lit (FIELD E)…)`, or `(record-lit (.. E) (FIELD E)…)` for an update |
| A spread | `(.. E)` among a tuple's, a list's or a call's elements |
| A quote | `(quote BLOCK)`, `(quote-type T)`, `(quote-pattern P)` or `(quote-field (FIELD E))` |
| A splice or a spread in a quote | `($ x)` or `($ E)`, and `($.. x)` or `($.. E)`, standing where the form it fills does, as in `(field E ($ f))` and `(record-lit (($ n) E))` |
| `-e`, `!e` | `(neg E)`, `(not E)` |
| A binary operator | `(OP A B)`, with the operator as written, such as `(+ a b)` or `(\|\| a b)` |
| `a else b` | `(else A B)` |
| `try` | `(try E)`, or `(try E (catch ARM…))` |
| `raise`, `return`, `break`, `continue` | `(raise E)`, `(return)`, `(return E)`, `break`, `continue` |
| A closure | `(closure (PARAM…) E)`, where a parameter is a pattern, `(: P T)` with a type, `(inout x)`, or `(inout x T)` with a type |
| A block | `(block STMT…)` |
| `if` | `(if E BLOCK)` or `(if E BLOCK ELSE)`, where `E` is `(let P E)` for an `if let` and `(bound T BOUND…)` for a bound test |
| `match` | `(match E ARM…)` |
| An arm | `(arm P E)`, `(arm P (if GUARD) E)` or `(arm P (because "reason") E)` |
| Loops | `(loop BLOCK)`, `(while E BLOCK)`, `(for P ITERABLE BLOCK)`, where a range is `(.. A B)` or `(..= A B)` |
| A staging annotation | `(comptime FORM)`, where `FORM` is the tree of its `if`, `match` or `for` |
| `let`, `var` | `(let P E)`, `(var P E)` |
| `yield` | `(yield E)` |
| An assignment | `(= PLACE E)`, or `(OP= PLACE E)` such as `(+= PLACE E)` |
| `assert` | `(assert E)` |
| A handler literal | `(handler EFFECT RETURN? FN…)`, where `EFFECT` is its path, `(PATH T…)` with arguments, or `async`, and `RETURN` is `(-> T)` when one is written |
| `with` | `(with (H…) BLOCK)` |
| `when` | `(when (x…) BLOCK)` |
| `unsafe because` | `(unsafe "reason" BLOCK)` |
| `resume` | `(resume)` or `(resume E)` |
| A macro use | `(macro PATH GROUP…)`, its group and its trailing block, if any, unexpanded, where a group is `(paren T…)`, `(bracket T…)` or `(brace T…)`, and a token is printed as written, a literal or a piece of an interpolated string as a string of its text, and a separator as `;` |
| An expression statement | The expression's tree |

Checked by: `just parse`, as for [syntax.tree-form](#syntax.tree-form).

## Published grammars

<a id="syntax.published-grammars"></a>
Constrained decoders read this grammar in two forms:

- `grammar/stilt.gbnf`, the GBNF that llama.cpp reads;
- `grammar/stilt.lark`, the Lark-like format of llguidance.

`stilt-grammar` (in `tools/grammar/`) generates both from this chapter's productions and from [Lexical structure](02-lexical.md). A form never rejects a prefix of a program of the language. Where a rule isn't context-free, a form accepts more than the language does.

Checked by: `just grammar`, which checks that regenerating the forms changes nothing, and that each form, read by llguidance, keeps every prefix of the conformance tests that have no syntax error, of the guide's examples and of generated programs viable.

<a id="syntax.published-grammars.rewrites"></a>
The generator changes the productions in these ways, none of which changes the strings they accept:

- **Parameterized rules.** It expands `list`, `list1` and `arms` into rules of their own.
- **Heads.** It derives `head` from `expr`, as [syntax.heads](#syntax.heads) describes. It copies `expr`, `postfix`, `built`, `primary` and `catch_arm` without the forms a head can't hold. Outside parentheses and brackets, the copies refer to copies, never to the rules they copy.
- **Left recursion.** GBNF has no left recursion, so `a = a x | b` becomes `a = b { x }`, which `expr` and `built` need.
- **Separators.** A `SEP` is a run of `;` and newlines, and [lexical.separators](02-lexical.md#lexical.separators) lets one stand after every `{`, before every `}`, and at both ends of the file.

Checked by: `just grammar`, as for [syntax.published-grammars](#syntax.published-grammars).

<a id="syntax.published-grammars.loosening"></a>
The forms read characters, with the blanks and comments of [Lexical structure](02-lexical.md) after each token. They loosen the language in these places, each of which only adds strings:

- **Terminators** ([lexical.terminator-insertion](02-lexical.md#lexical.terminator-insertion), [lexical.inside-brackets](02-lexical.md#lexical.inside-brackets), [lexical.continuing-expression](02-lexical.md#lexical.continuing-expression)). A newline is a `SEP` where the line ends with an identifier, a literal or one of the other tokens that end an expression. After any other token, it ends nothing. A context-free grammar can't tell whether it is inside parentheses or brackets. So a newline may also precede `,`, `)`, `]`, `>` and every binary operator anywhere. It may also follow `>` and `>>` as binary operators, where the language inserts a terminator and so rejects the program.
- **Words** ([lexical.identifiers](02-lexical.md#lexical.identifiers) to [lexical.contextual-keywords](02-lexical.md#lexical.contextual-keywords)). A `lower` or an `Upper` may spell a keyword or a reserved word, and a function's parameter may be named `escaping`. Tokens need not be separated by blanks, so the GBNF reads `letx` as `let x`.
- **Numbers** ([lexical.integer-literals](02-lexical.md#lexical.integer-literals) to [lexical.digits-after-dot](02-lexical.md#lexical.digits-after-dot)). A number may be followed by a letter, a digit or `_`, as in `10u8`. A float with a fraction is an integer, a `.` and a fraction, so blanks may separate the three, and the integer may be hexadecimal, octal or binary.
- **Strings** ([lexical.string-literals](02-lexical.md#lexical.string-literals), [lexical.format-specs](02-lexical.md#lexical.format-specs)). An interpolation may span lines. The numbers of a format spec may have any number of digits and a leading zero.
- **Comments** ([program.doc-comments](04-programs.md#program.doc-comments)). A doc comment is a comment, so it may stand wherever a `//` comment may, and the examples and properties of doc comments aren't parsed.
- **Comparisons** ([expressions.precedence](08-expressions.md#expressions.precedence)). Comparisons chain: `a < b < c` is accepted.

Checked by: `just grammar`, as for [syntax.published-grammars](#syntax.published-grammars).
