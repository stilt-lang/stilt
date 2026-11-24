# 2. Lexical structure

The lexer turns a source file into tokens. This chapter gives the characters a file may hold, comments, identifiers and keywords, literals, operators and punctuation, and where a newline ends a statement. The lexer is fixed and has no reader macros: every tool reads every file into the same tokens. [Syntax](03-syntax.md) gives the grammar that reads the tokens.

## Source text

<a id="lexical.source-text"></a>
A source file must be UTF-8, with no byte-order mark. `\r\n` is read as `\n`, and a lone `\r` is an error. A file that breaks this rule is E0001, *invalid source text*, at the byte-order mark, the first byte that isn't UTF-8 or the lone `\r`. Such a file is not lexed at all, and this error is its only diagnostic.

Tests: [lexical/crlf_line_endings.lt](../conformance/lexical/crlf_line_endings.lt), [lexical/source_text/main.lt](../conformance/lexical/source_text/main.lt).

<a id="lexical.whitespace"></a>
**Whitespace** is space, tab and newline. Tabs are allowed, and `stilt fmt` replaces them ([syntax.format.indentation](03-syntax.md#syntax.format.indentation)). Outside string literals and comments, a character that is neither whitespace nor part of a token is E0002, *unexpected character*. Such characters include a form feed, a vertical tab, a no-break space, a letter outside ASCII, `~`, `\`, a backtick and `×`.

Tests: [lexical/tabs.lt](../conformance/lexical/tabs.lt), [lexical/unexpected_characters/main.lt](../conformance/lexical/unexpected_characters/main.lt).

## Comments

<a id="lexical.line-comments"></a>
`//` starts a comment that runs to the end of the line. A comment may follow code on its line, or stand alone on it.

Tests: [lexical/commented_out_code.lt](../conformance/lexical/commented_out_code.lt), [lexical/crlf_line_endings.lt](../conformance/lexical/crlf_line_endings.lt), [lexical/doc_comment_after_code.lt](../conformance/lexical/doc_comment_after_code.lt), [lexical/example_comments.lt](../conformance/lexical/example_comments.lt), [lexical/line_comments.lt](../conformance/lexical/line_comments.lt).

<a id="lexical.doc-comments"></a>
`///` starts a **doc comment**, which documents the declaration that follows it ([program.doc-comments](04-programs.md#program.doc-comments)). So `////` starts a doc comment whose text begins with `/`. A doc comment must stand alone on its line: one that follows code is a syntax error ([syntax.doc-comment-placement](03-syntax.md#syntax.doc-comment-placement)).

Tests: [lexical/commented_out_code.lt](../conformance/lexical/commented_out_code.lt), [lexical/doc_comment_after_code.lt](../conformance/lexical/doc_comment_after_code.lt), [lexical/doc_comments_hold_code.lt](../conformance/lexical/doc_comments_hold_code.lt), [lexical/four_slashes.lt](../conformance/lexical/four_slashes.lt).

<a id="lexical.annotations"></a>
`//~` starts a test annotation of the conformance suite ([conformance.annotations](01-conformance.md#conformance.annotations)). Every tool but the test runner reads it as an ordinary comment, to which [lexical.commented-out-code](#lexical.commented-out-code) doesn't apply.

Tests: [lexical/annotations_are_comments.lt](../conformance/lexical/annotations_are_comments.lt), [lexical/commented_out_code.lt](../conformance/lexical/commented_out_code.lt).

<a id="lexical.no-block-comments"></a>
There are no block comments. `/*` is the token `/` followed by the token `*`, so a block comment as C writes it is a syntax error (E0100).

Tests: [lexical/block_comment.lt](../conformance/lexical/block_comment.lt), [lexical/line_comments.lt](../conformance/lexical/line_comments.lt).

<a id="lexical.commented-out-code"></a>
A `//` comment whose text, after the `//`, parses as one or more complete statements or items gets the warning W0001, *commented-out code*, at the comment. Statements include expression statements ([expressions.statements](08-expressions.md#expressions.statements)). Doc comments and annotations are not `//` comments in this sense. So `// print("debug: {total}")`, `// pub fn f() {}`, `// var n = 0`, `// f(x)` and `// i.e. done` get the warning. `// see f(x)` and `// TODO(ana): tidy up` don't parse, and get none.

Tests: [checking/warning_outside_bodies.lt](../conformance/checking/warning_outside_bodies.lt), [lexical/annotations_are_comments.lt](../conformance/lexical/annotations_are_comments.lt), [lexical/commented_out_code.lt](../conformance/lexical/commented_out_code.lt), [lexical/commented_out_forms.lt](../conformance/lexical/commented_out_forms.lt), [lexical/commented_out_statements.lt](../conformance/lexical/commented_out_statements.lt), [lexical/crlf_line_endings.lt](../conformance/lexical/crlf_line_endings.lt), [lexical/doc_comments_hold_code.lt](../conformance/lexical/doc_comments_hold_code.lt), [lexical/four_slashes.lt](../conformance/lexical/four_slashes.lt), [protocol/comment_inside_failing_body.lt](../conformance/protocol/comment_inside_failing_body.lt), [protocol/comment_warnings_with_errors.lt](../conformance/protocol/comment_warnings_with_errors.lt), [protocol/syntax_errors_per_part/main.lt](../conformance/protocol/syntax_errors_per_part/main.lt).

<a id="lexical.commented-out-code.single-token"></a>
Text that is a single token is exempt from [lexical.commented-out-code](#lexical.commented-out-code). It stays exempt after a leading `-`, inside one pair of parentheses, or both, in either order. `()` is exempt too. A string literal counts as one token, even when it interpolates. A written `;` counts as a token. So `// fallthrough`, `// 42`, `// -1`, `// (unused)`, `// (-1)`, `// -(1)`, `// "done"`, `// ?` and `// ;` get no warning, while `// x;` and `// ;x` get one.

Tests: [lexical/commented_negative_in_parentheses.lt](../conformance/lexical/commented_negative_in_parentheses.lt), [lexical/separator_in_comment.lt](../conformance/lexical/separator_in_comment.lt), [lexical/single_token_comments.lt](../conformance/lexical/single_token_comments.lt).

## Identifiers and case

<a id="lexical.identifiers"></a>
An **identifier** matches `[A-Za-z_][A-Za-z0-9_]*`. Identifiers are ASCII: a letter outside ASCII, as in `café`, is an unexpected character ([lexical.whitespace](#lexical.whitespace)).

Tests: [lexical/identifiers.lt](../conformance/lexical/identifiers.lt), [lexical/unexpected_characters/main.lt](../conformance/lexical/unexpected_characters/main.lt), [lexical/words_left_free.lt](../conformance/lexical/words_left_free.lt).

<a id="lexical.case"></a>
Case is part of the grammar. An identifier's **case** is the case of its first letter, after any leading underscores. An identifier with no letter, such as `__` or `_1`, is E0003, *identifier without a letter*. An uppercase identifier names a type, a type parameter, a variant, a trait, a user-defined effect or a constant. A lowercase identifier names a value, a function, a module, a field, a method or an effect-row variable. The built-in effect labels are lowercase: `raise` is a keyword, and `io` a contextual keyword.

Tests: [lexical/identifiers.lt](../conformance/lexical/identifiers.lt), [lexical/no_letter/main.lt](../conformance/lexical/no_letter/main.lt), [lexical/underscored_names.lt](../conformance/lexical/underscored_names.lt), [lexical/uppercase_binding.lt](../conformance/lexical/uppercase_binding.lt).

<a id="lexical.case.wrong-case"></a>
Where the grammar expects one case, a name of the other case is a syntax error (E0100), whose fix corrects the case. So `fn Parse()`, `fn _Parse()`, `type point` and `const limit` are each one. So are a field `X`, a method `Get`, a parameter `Count`, a type parameter `t`, a variant `circle` and a trait `shape`. So are a module path `Std.io` and the struct literal `point { x: 0 }`. In a pattern, an uppercase name is a constant or a variant to compare against, never a binding ([patterns.pattern-forms](09-patterns.md#patterns.pattern-forms)). So `let Total = 1` names a constant, and is E0211, *unknown name*, if none exists.

Tests: [declarations/const_lowercase.lt](../conformance/declarations/const_lowercase.lt), [declarations/type_parameter_case.lt](../conformance/declarations/type_parameter_case.lt), [lexical/uppercase_binding.lt](../conformance/lexical/uppercase_binding.lt), [lexical/wrong_case/main.lt](../conformance/lexical/wrong_case/main.lt).

<a id="lexical.primitive-type-names"></a>
The **primitive type names** are lowercase and reserved: `bool`, `i8`, `i16`, `i32`, `i64`, `u8`, `u16`, `u32`, `u64`, `f32`, `f64` and `str`. They can't name anything else. They are identifiers to the lexer and the grammar. Name resolution rejects any declaration or binding that uses one as its name, which is E0210, *primitive type name used as a name*. This holds for a type, a field, a function, a method, a parameter, a generic and a binding of a pattern alike.

Tests: [lexical/primitive_names_as_types.lt](../conformance/lexical/primitive_names_as_types.lt), [lexical/primitive_type_names.lt](../conformance/lexical/primitive_type_names.lt), [names/primitive_binding_used.lt](../conformance/names/primitive_binding_used.lt), [names/primitive_names.lt](../conformance/names/primitive_names.lt), [protocol/several_entries_on_one_line.lt](../conformance/protocol/several_entries_on_one_line.lt).

<a id="lexical.wildcard"></a>
`_` alone is the wildcard. It is never an identifier, so `fn _()`, `type _ = …` and `let x = _` are syntax errors (E0100).

Tests: [lexical/identifiers.lt](../conformance/lexical/identifiers.lt), [lexical/no_letter/main.lt](../conformance/lexical/no_letter/main.lt), [lexical/wildcard_as_name/main.lt](../conformance/lexical/wildcard_as_name/main.lt).

## Keywords

<a id="lexical.keywords"></a>
These words are keywords:

- declarations: `const`, `fn`, `impl`, `module`, `pub`, `test`, `trait`, `type`, `use`;
- bindings and parameter modes: `inout`, `let`, `var`;
- control flow: `break`, `continue`, `else`, `for`, `if`, `in`, `loop`, `match`, `return`, `while`;
- failure: `assert`, `catch`, `raise`, `try`;
- values and types: `false`, `self`, `Self`, `true`.

A keyword used as a name is a syntax error (E0100).

Tests: [lexical/core_keywords_as_names/main.lt](../conformance/lexical/core_keywords_as_names/main.lt), [lexical/identifiers.lt](../conformance/lexical/identifiers.lt), [lexical/words_left_free.lt](../conformance/lexical/words_left_free.lt).

<a id="lexical.reserved-words"></a>
These words are keywords too: `async`, `await`, `comptime`, `effect`, `extern`, `handler`, `macro`, `quote`, `resume`, `syntax`, `unsafe`, `when`, `where`, `with` and `yield`. They are keywords in every module, whatever its tier. One used as a name is a syntax error (E0100). The forms they begin belong to the tiers that define them:

- `where`, `yield`, `syntax`, `effect`, `handler`, `with`, `resume`, `async`, `await` and `when` to the advanced tier;
- `comptime`, `macro` and `quote` to the meta tier;
- `unsafe`, and `extern` before a function without a body, to the systems tier;
- `extern` after `pub`, before a function with a body, to core ([c.exported-functions](20-builds.md#c.exported-functions)).

`await` names a method after `.`, as in `t.await()` ([tasks.std-task](14-tasks.md#tasks.std-task)). No other word is reserved: `as`, `dyn`, `move`, `mut`, `ref` and `static` are identifiers.

Tests: [lexical/identifiers.lt](../conformance/lexical/identifiers.lt), [lexical/later_tier_words_as_names/main.lt](../conformance/lexical/later_tier_words_as_names/main.lt), [lexical/words_left_free.lt](../conformance/lexical/words_left_free.lt).

<a id="lexical.contextual-keywords"></a>
A **contextual keyword** is an identifier that the parser reads as a keyword wherever the grammar accepts the keyword at that point, and as an identifier everywhere else. These are the contextual keywords, and where each is read as one:

| Word | A keyword |
| --- | --- |
| `because` | Between the pattern of a `catch` arm and its `=>` ([effects.catch-alls-need-reason](12-effects.md#effects.catch-alls-need-reason)), and after `unsafe` ([c.unsafe-because](20-builds.md#c.unsafe-because)) |
| `io` | As an element of an effect row ([effects.rows](12-effects.md#effects.rows)) |
| `escaping` | At the start of a parameter, before its name ([declarations.function-declarations](10-declarations.md#declarations.function-declarations)) |
| `without` | Where a limit clause can start: in a module header, after its path ([program.module-header](04-programs.md#program.module-header)), and after a function's signature, before its body ([declarations.function-declarations](10-declarations.md#declarations.function-declarations)) |
| `panic`, `overflow`, `alloc`, `div`, `copy`, `fs`, `net`, `clock`, `env`, `console`, `rand`, `spawn`, `exec`, `locks` | As the limits of a `without` clause ([facts.spelling](15-facts.md#facts.spelling), [facts.without](15-facts.md#facts.without), [shared.locks](14-tasks.md#shared.locks)) |
| `meta` | At the start of an item, before `use` ([macros.meta-use](16-meta.md#macros.meta-use)) |
| `pattern`, `field` | Directly after `quote` ([macros.quote](16-meta.md#macros.quote)) |

The limit `unsafe` is a reserved word ([lexical.reserved-words](#lexical.reserved-words)), and so a keyword everywhere.

Tests: [declarations/function_limits.lt](../conformance/declarations/function_limits.lt), [lexical/because_outside_catch.lt](../conformance/lexical/because_outside_catch.lt), [lexical/contextual_keywords.lt](../conformance/lexical/contextual_keywords.lt), [lexical/escaping_as_parameter.lt](../conformance/lexical/escaping_as_parameter.lt).

<a id="lexical.contextual-keywords.as-names"></a>
Outside those positions, a contextual keyword is a name. So `use std.io` binds the module name `io`, while `io` in an effect row is always the label. A local may be named `escaping`, but a parameter can't. A line that begins with `without` and a limit joins the line before it ([lexical.continuation-lines](#lexical.continuation-lines)). A name after `without` that isn't a limit, such as the name of a tier, is a syntax error (E0100).

Tests: [lexical/contextual_keywords.lt](../conformance/lexical/contextual_keywords.lt), [lexical/escaping_as_local.lt](../conformance/lexical/escaping_as_local.lt), [lexical/io_module_and_label.lt](../conformance/lexical/io_module_and_label.lt), [lexical/tier_after_without.lt](../conformance/lexical/tier_after_without.lt), [lexical/without_on_next_line.lt](../conformance/lexical/without_on_next_line.lt).

## Literals

<a id="lexical.integer-literals"></a>
A decimal integer literal is `0`, or a nonzero digit followed by digits. The prefixes `0x` (hexadecimal), `0o` (octal) and `0b` (binary) give the other bases. A prefix is lowercase, and must be followed by at least one digit of its base. Hexadecimal digits may be either case. `_` may appear only between two digits. A decimal literal with a leading zero, such as `007` or `00`, is malformed. So is a number literal directly followed by a letter, a digit or `_`, as in `10u8`, `1e`, `0b102` or `0o8`: there are no type suffixes. A malformed number literal, integer or float, is E0004, *malformed number literal*, at the first character at which it breaks its grammar.

Tests: [lexical/digits_after_dot_errors/main.lt](../conformance/lexical/digits_after_dot_errors/main.lt), [lexical/integer_literals.lt](../conformance/lexical/integer_literals.lt), [lexical/malformed_integers/main.lt](../conformance/lexical/malformed_integers/main.lt).

<a id="lexical.float-literals"></a>
A float literal takes one of three forms: `D.D`, `DeE` or `D.DeE`. `D` is a run of decimal digits, with the integers' rule for `_`. The part before the `.` or the exponent follows the leading-zero rule, so `0.5` is valid and `00.5` is malformed. `E` is a run of decimal digits after `e` or `E` and an optional sign. It may have leading zeros, as in `1e-05`, and holds no `_`, so `1e1_0` is malformed. `1.` and `.5` are not float literals, and there are no hexadecimal floats. The suffix rule of [lexical.integer-literals](#lexical.integer-literals) applies, so `2.5f` is malformed.

Tests: [lexical/float_literals.lt](../conformance/lexical/float_literals.lt), [lexical/float_separators.lt](../conformance/lexical/float_separators.lt), [lexical/leading_dot_key_path.lt](../conformance/lexical/leading_dot_key_path.lt), [lexical/leading_dot_not_a_float.lt](../conformance/lexical/leading_dot_not_a_float.lt), [lexical/malformed_floats/main.lt](../conformance/lexical/malformed_floats/main.lt).

<a id="lexical.digits-after-dot"></a>
A run of decimal digits that directly follows a `.` token is always lexed as a decimal integer, with no fraction or exponent. So `t.0.1` is lexed as `t . 0 . 1`, two tuple-field accesses. `0..n` is lexed as `0 .. n`, and `.5` as a key path to the tuple field `5` ([expressions.key-paths](08-expressions.md#expressions.key-paths)). After a `.`, `01` breaks the leading-zero rule, and `1e3` and `0x1` break the suffix rule. A `?` before the `.` is a hole, so `t?.0.1` is a syntax error at the `?` ([types.hole-before-dot](07-types.md#types.hole-before-dot)).

Tests: [lexical/digits_after_dot.lt](../conformance/lexical/digits_after_dot.lt), [lexical/digits_after_dot_errors/main.lt](../conformance/lexical/digits_after_dot_errors/main.lt), [lexical/leading_dot_key_path.lt](../conformance/lexical/leading_dot_key_path.lt).

<a id="lexical.string-literals"></a>
A **string literal** is written `"…"`. Every string literal interpolates: an unescaped `{` starts an interpolation ([lexical.interpolation](#lexical.interpolation)). A lone `}` is an ordinary character. Neither a string literal nor an interpolation inside it can hold a raw newline, so an interpolation closes on the line where its string opens. A string literal that its line leaves open is E0005, *unterminated string literal*, at its opening quote.

Tests: [lexical/interpolation_across_lines.lt](../conformance/lexical/interpolation_across_lines.lt), [lexical/single_token_comments.lt](../conformance/lexical/single_token_comments.lt), [lexical/unterminated_strings/main.lt](../conformance/lexical/unterminated_strings/main.lt).

<a id="lexical.escapes"></a>
The escapes are `\n`, `\t`, `\r`, `\0`, `\\`, `\"`, `\{` and `\u{X…}`. The 1 to 6 hexadecimal digits of `\u{X…}` must name a Unicode scalar value. Any other escape is E0006, *invalid escape*, at its backslash. So `\}`, `\'`, `\x41`, `\u0041`, `\u{}`, `\u{D800}` and `\u{110000}` are invalid. `{{` is an invalid escape too, at its first brace, and its fix is `\{`.

Tests: [lexical/brace_escape_instead_of_double.lt](../conformance/lexical/brace_escape_instead_of_double.lt), [lexical/double_braces.lt](../conformance/lexical/double_braces.lt), [lexical/invalid_escapes/main.lt](../conformance/lexical/invalid_escapes/main.lt), [lexical/string_escapes.lt](../conformance/lexical/string_escapes.lt).

<a id="lexical.interpolation"></a>
An **interpolation** is written `{expr}` or `{expr:spec}`. It must hold an expression, so `"{}"` is a syntax error (E0100). The spec starts at the first `:` of the interpolation that isn't inside a nested bracket or a nested string literal. So `{"a:b"}` has no spec, while the spec of `{|x: i64| x}` starts at its first `:`.

Tests: [lexical/empty_interpolation.lt](../conformance/lexical/empty_interpolation.lt), [lexical/interpolation.lt](../conformance/lexical/interpolation.lt).

<a id="lexical.nested-interpolation"></a>
An interpolation can hold string literals, braces and further interpolations, which the lexer reads with a stack of modes.

Tests: [lexical/interpolation.lt](../conformance/lexical/interpolation.lt), [lexical/interpolation_across_lines.lt](../conformance/lexical/interpolation_across_lines.lt), [lexical/string_escapes.lt](../conformance/lexical/string_escapes.lt).

<a id="lexical.format-specs"></a>
A **format spec** has the form `[[fill]align][width][.precision][kind]`. Each of its parts may be left out, so `{42:}` has an empty spec. The parts take these values:

| Part | Values |
| --- | --- |
| `align` | `<`, `^` or `>` |
| `fill` | Any one character other than `{` and `}` |
| `width` | A decimal number from 0 to 65535, with no leading zero |
| `precision` | A decimal number from 0 to 65535, with no leading zero |
| `kind` | `x`, `X`, `o`, `b` or `e` |

`{x:05}` is malformed, and isn't a width of 5. Zero padding is written with a fill, as in `{x:0>5}`. A spec that breaks this grammar is E0007, *malformed format spec*, at the `:` that starts it. So `{x:.2f}`, `{n:+5}`, `{n:#x}` and `{n:65536}` are malformed. [std.invalid-specs](17-std.md#std.invalid-specs) gives the specs that each type accepts.

Tests: [lexical/doc_example_malformed_spec.lt](../conformance/lexical/doc_example_malformed_spec.lt), [lexical/doc_property_malformed_spec.lt](../conformance/lexical/doc_property_malformed_spec.lt), [lexical/empty_format_spec.lt](../conformance/lexical/empty_format_spec.lt), [lexical/format_spec_grammar.lt](../conformance/lexical/format_spec_grammar.lt), [lexical/format_spec_limits.lt](../conformance/lexical/format_spec_limits.lt), [lexical/malformed_format_specs/main.lt](../conformance/lexical/malformed_format_specs/main.lt), [lexical/python_float_spec.lt](../conformance/lexical/python_float_spec.lt), [lexical/spec_precision_leading_zero.lt](../conformance/lexical/spec_precision_leading_zero.lt), [lexical/spec_width_leading_zero.lt](../conformance/lexical/spec_width_leading_zero.lt), [lexical/spec_zero_numbers.lt](../conformance/lexical/spec_zero_numbers.lt), [types/format_specs.lt](../conformance/types/format_specs.lt).

<a id="lexical.no-characters"></a>
There is no `char` type and no character literal. `'` is a reserved token ([lexical.reserved-tokens](#lexical.reserved-tokens)), so `'a'` is a syntax error (E0100). Text of one Unicode scalar value is a `str`.

Tests: [lexical/one_character_strings.lt](../conformance/lexical/one_character_strings.lt), [lexical/reserved_tokens/main.lt](../conformance/lexical/reserved_tokens/main.lt).

## Tokens

<a id="lexical.tokens"></a>
The operators and punctuation are these tokens:

| Group | Tokens |
| --- | --- |
| Arithmetic | `+` `-` `*` `/` `%` |
| Wrapping arithmetic | `+%` `-%` `*%` |
| Comparison | `==` `!=` `<` `<=` `>` `>=` |
| Logic | `&&` `\|\|` `!` |
| Bitwise | `&` `\|` `^` `<<` `>>` |
| Assignment | `=` `+=` `-=` `*=` `/=` `%=` `+%=` `-%=` `*%=` `&=` `\|=` `^=` `<<=` `>>=` |
| Arrows | `->` `=>` |
| Ranges and access | `.` `..` `..=` |
| Separators | `,` `:` `;` |
| Brackets | `(` `)` `[` `]` `{` `}` |
| Holes | `?` |
| Macros and quotes | `$` |
| Reserved | `@` `'` `#` |

Tokens are lexed by maximal munch, so `..=`, `+%=` and `>>=` are each one token. `?.` is not a token: a `?` followed by `.`, `..` or `..=` is a hole ([declarations.typed-holes](10-declarations.md#declarations.typed-holes)) followed by that token ([types.hole-before-dot](07-types.md#types.hole-before-dot)).

Tests: [lexical/hole_before_range.lt](../conformance/lexical/hole_before_range.lt), [lexical/operator_tokens.lt](../conformance/lexical/operator_tokens.lt), [lexical/separator_in_comment.lt](../conformance/lexical/separator_in_comment.lt), [lexical/unexpected_characters/main.lt](../conformance/lexical/unexpected_characters/main.lt).

<a id="lexical.reserved-tokens"></a>
The reserved tokens `@`, `'` and `#` stand in no form of the language. Each is a syntax error wherever it appears (E0100), as in the binding `kept @ Some(_)`. `$` stands only in a `syntax` declaration ([macros.templates](16-meta.md#macros.templates)) and in a quote ([macros.splices](16-meta.md#macros.splices)). Anywhere else, it is a syntax error.

Tests: [lexical/reserved_tokens/main.lt](../conformance/lexical/reserved_tokens/main.lt), [patterns/at_binding.lt](../conformance/patterns/at_binding.lt).

## Newlines and terminators

<a id="lexical.terminator-insertion"></a>
A newline becomes a statement **terminator** when all of these hold:

- the line ends with a token that can end an expression;
- the next line doesn't continue it ([lexical.continuation-lines](#lexical.continuation-lines));
- the line doesn't begin with `@`.

For this rule, these are the tokens that can end an expression:

- an identifier, a primitive type name among them, or a literal;
- `true`, `false`, `self`, `Self`, `return`, `break` and `continue`, and `unsafe`, which can end a `without` clause ([c.without-unsafe](20-builds.md#c.without-unsafe));
- `)`, `]`, `}`, `?`, `>` and `>>`.

So a signature without a body, as in a trait, needs no written terminator, even after `-> str` or `-> Option<i64>`. A `{` on the line after a signature is a syntax error (E0100).

Tests: [lexical/bodiless_signatures.lt](../conformance/lexical/bodiless_signatures.lt), [lexical/brace_on_next_line.lt](../conformance/lexical/brace_on_next_line.lt), [lexical/brackets_on_next_line.lt](../conformance/lexical/brackets_on_next_line.lt), [lexical/comparison_ends_line/main.lt](../conformance/lexical/comparison_ends_line/main.lt), [lexical/hole_ends_line.lt](../conformance/lexical/hole_ends_line.lt), [lexical/minus_starts_line.lt](../conformance/lexical/minus_starts_line.lt), [lexical/terminator_after_tokens.lt](../conformance/lexical/terminator_after_tokens.lt).

<a id="lexical.continuation-lines"></a>
A line continues the line before it when it begins with one of the tokens `.`, `else`, `catch` or `|`. It also continues it when it begins with the word `without`, followed on the same line by a limit of a `without` clause ([lexical.contextual-keywords](#lexical.contextual-keywords)). So a chain of calls, a fallback, a `catch`, an alternative, and a function's or a header's limit clause may each start a line of their own. Tokens are lexed by maximal munch, so a line that begins with `..` or `||` doesn't continue. Neither does a line that begins with `?`, `-`, `(` or `[`. The next line is the next one that holds a token: blank lines, and lines that hold only comments, are skipped.

Tests: [lexical/continuation_after_gaps.lt](../conformance/lexical/continuation_after_gaps.lt), [lexical/continuation_lines.lt](../conformance/lexical/continuation_lines.lt), [lexical/hole_dot_starts_line.lt](../conformance/lexical/hole_dot_starts_line.lt), [lexical/logical_or_starts_line.lt](../conformance/lexical/logical_or_starts_line.lt), [lexical/range_starts_line.lt](../conformance/lexical/range_starts_line.lt), [lexical/without_on_next_line.lt](../conformance/lexical/without_on_next_line.lt), [lexical/without_on_next_line_rejected.lt](../conformance/lexical/without_on_next_line_rejected.lt), [program/header_limits_on_path_line.lt](../conformance/program/header_limits_on_path_line.lt).

<a id="lexical.terminator-positions"></a>
An inserted terminator sits on the line of the token before it, so an error at it is reported on that line. The end of the file sits just after the file's last token.

Tests: [lexical/brace_on_next_line.lt](../conformance/lexical/brace_on_next_line.lt), [lexical/comparison_ends_line/main.lt](../conformance/lexical/comparison_ends_line/main.lt), [lexical/end_of_file_error.lt](../conformance/lexical/end_of_file_error.lt), [lexical/missing_commas/main.lt](../conformance/lexical/missing_commas/main.lt), [lexical/no_terminator_in_parentheses.lt](../conformance/lexical/no_terminator_in_parentheses.lt), [lexical/range_starts_line.lt](../conformance/lexical/range_starts_line.lt).

<a id="lexical.inside-brackets"></a>
No terminator is inserted while the innermost open bracket is `(` or `[`, so a call or a list may span lines. Inside a `{…}` nested within them, such as the block of a closure passed as an argument, [lexical.terminator-insertion](#lexical.terminator-insertion) applies again.

Tests: [lexical/brackets.lt](../conformance/lexical/brackets.lt), [lexical/no_terminator_in_parentheses.lt](../conformance/lexical/no_terminator_in_parentheses.lt).

<a id="lexical.terminators-never-replace-commas"></a>
Terminators never replace commas. The fields of a record type, of a record literal and of a record pattern are separated by commas, across lines too. A field that lacks its comma at the end of its line is a syntax error on that line (E0100).

Tests: [lexical/missing_commas/main.lt](../conformance/lexical/missing_commas/main.lt), [lexical/multiline_records.lt](../conformance/lexical/multiline_records.lt).

<a id="lexical.continuing-expression"></a>
A line that ends with a binary operator continues onto the next line. So does a line that ends with any other token that [lexical.terminator-insertion](#lexical.terminator-insertion) doesn't list, such as `=`, `,` or `=>`. `>` and `>>` are the exception: they can close a generic type, and they end the line. A comparison that spans lines is wrapped in parentheses: `a >` at the end of a line is a syntax error (E0100), while `a >=` continues.

Tests: [lexical/bodiless_signatures.lt](../conformance/lexical/bodiless_signatures.lt), [lexical/brackets.lt](../conformance/lexical/brackets.lt), [lexical/comparison_ends_line/main.lt](../conformance/lexical/comparison_ends_line/main.lt), [lexical/continuation_lines.lt](../conformance/lexical/continuation_lines.lt), [lexical/operator_ends_line.lt](../conformance/lexical/operator_ends_line.lt), [types/operator_mismatch_on_two_lines.lt](../conformance/types/operator_mismatch_on_two_lines.lt).

<a id="lexical.explicit-separators"></a>
`;` may separate statements or items explicitly, as in `use std.cli; use std.fs`, and may separate a module header's path from its `without` clause. `stilt fmt` never writes it ([syntax.format.separators](03-syntax.md#syntax.format.separators)).

Tests: [lexical/misplaced_separators/main.lt](../conformance/lexical/misplaced_separators/main.lt), [lexical/separators.lt](../conformance/lexical/separators.lt), [program/header_separators.lt](../conformance/program/header_separators.lt).

<a id="lexical.separators"></a>
The grammar sees `;` and an inserted terminator as the same separator, `SEP` ([syntax.token-classes](03-syntax.md#syntax.token-classes)). A separator is ignored when it comes directly after `{`, another separator or the start of the file. It is also ignored directly before `}` or the end of the file. So the last statement or arm of a block needs no separator. A separator where the grammar takes none is a syntax error (E0100). Such places include the gaps between the fields of a record type, the elements of a list and the arguments of a call.

Tests: [lexical/arm_separators.lt](../conformance/lexical/arm_separators.lt), [lexical/misplaced_separators/main.lt](../conformance/lexical/misplaced_separators/main.lt), [lexical/separator_in_comment.lt](../conformance/lexical/separator_in_comment.lt), [lexical/separators.lt](../conformance/lexical/separators.lt), [lexical/terminator_after_tokens.lt](../conformance/lexical/terminator_after_tokens.lt).

## Nesting

<a id="lexical.nesting"></a>
Brackets and interpolations nest at most 256 deep. Reading a file's tokens in order, each `(`, `[` and `{`, and the `{` that begins each interpolation ([lexical.interpolation](#lexical.interpolation)), opens one level, and each `)`, `]` and `}`, and the `}` that ends each interpolation, closes the innermost level open, if one is. A file in which a level opens with 256 already open is E0008, *nesting too deep*, at the bracket that opens it or, for an interpolation, at the `"` that begins its string literal. The levels are counted over the tokens before the file's first lexical error. Such a file is not parsed, so this error is its only diagnostic, and it declares nothing, as a file that breaks [lexical.source-text](#lexical.source-text) does. Code that needs deeper nesting names its parts with `let` bindings, functions or types.

Tests: [lexical/nesting_too_deep.lt](../conformance/lexical/nesting_too_deep.lt), [lexical/nesting_too_deep_interpolation.lt](../conformance/lexical/nesting_too_deep_interpolation.lt), [lexical/nesting_at_the_limit.lt](../conformance/lexical/nesting_at_the_limit.lt).
