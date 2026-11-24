# Rationale: Lexical structure

Stilt has no reader macros, so every tool can parse every file. That holds only if the lexer is fixed and fully specified, down to the questions that interact. `t.0.1` has to read as two tuple-field accesses and not as a float, `.1` is a key path, every string interpolates `{expr}`, and statements have no visible terminator. [Lexical structure](../02-lexical.md) answers each of these in a way that a second implementation can follow without reading the first.

## Source text

A file has one encoding, UTF-8 with no byte-order mark ([lexical.source-text](../02-lexical.md#lexical.source-text)). Two tools then never disagree about which characters a file holds. `\r\n` is read as `\n`, so a file saved on Windows has the same tokens as one saved elsewhere. A lone `\r` has no agreed meaning, so it is rejected instead of guessed at. A file whose encoding is broken can't be lexed meaningfully at all. It gets one diagnostic, and no cascade of errors about characters the file doesn't hold.

Tabs are allowed, because they change nothing that a reader or a parser sees, and the formatter replaces them ([lexical.whitespace](../02-lexical.md#lexical.whitespace)). Any other character outside strings and comments that belongs to no token gets a code of its own, E0002. A `×` or a no-break space pasted from a document is then named for what it is, and doesn't surface as a confusing syntax error further on.

## Comments

There are only line comments ([lexical.no-block-comments](../02-lexical.md#lexical.no-block-comments)). Block comments would make commented-out code harder to detect, and they raise the question of whether they nest. Zig shows that a language works without them.

A `//` comment that parses as code gets a warning ([lexical.commented-out-code](../02-lexical.md#lexical.commented-out-code)). Readers, and coding agents above all, take comments as true, and code kept in a comment is code that nobody checks. Defective commented-out code measurably raises the rate of defective generated code. Code that nothing uses is deleted, and version control keeps it. The cost is that prose which happens to parse, such as `// i.e. done` or `// f(x)`, gets the warning too.

The exemption for a single token ([lexical.commented-out-code.single-token](../02-lexical.md#lexical.commented-out-code.single-token)) keeps the warning off the short notes that people write: `// fallthrough`, `// 42`, `// -1`, `// (unused)`, `// "done"`. A single token, even negated or in parentheses, never states a program that anyone would want back. A written `;` counts as a token, so `// x;` reads as the statement it looks like.

Doc comments and test annotations are excluded from the warning, because they hold code on purpose. A doc comment's examples are code, and an annotation states what a test expects ([lexical.annotations](../02-lexical.md#lexical.annotations)).

## Identifiers and case

Case is part of the grammar ([lexical.case](../02-lexical.md#lexical.case)). The parser knows that only an uppercase name can start a struct literal. A pattern knows that `x` is a binding, while `X` is a variant or a constant to compare against. So whether a pattern can fail follows from its form and the names in it, never from the values it meets. The two meanings of `else`, let-else and the fallback, rely on this.

The cost is that naming conventions become rules: neither a constant nor a type can be lowercase. The wrong case is an error that offers the corrected name, so the rule costs one keystroke when it bites ([lexical.case.wrong-case](../02-lexical.md#lexical.case.wrong-case)). Visibility by case, as in Go, is ruled out for the same reason: case already has this meaning.

Identifiers are ASCII ([lexical.identifiers](../02-lexical.md#lexical.identifiers)). Unicode identifiers are left out because visually confusable characters weaken the rule that every name has exactly one home: two names that look alike could be two different names.

The primitive type names are reserved ([lexical.primitive-type-names](../02-lexical.md#lexical.primitive-type-names)), so `str` means the type wherever it appears. They are identifiers to the lexer and the grammar, though. So `i64.MAX` parses as a path, and `-> str` ends a line as a name does. The error for using one as a name is then a precise one from name resolution, E0210, and not a syntax error.

## Keywords

The words of every tier are reserved in every module ([lexical.reserved-words](../02-lexical.md#lexical.reserved-words)). A module's tier is inferred from the features it uses, and the lexer and the parser read a file before anything is known about its tier. One set of keywords for every module keeps one grammar for every file. A module that starts to use a feature of another tier then never has to rename a binding.

Words that other languages reserve and that no tier of Stilt uses, such as `dyn`, `move`, `mut`, `ref`, `static` and `as`, stay ordinary names. A reserved word costs a name that everyone could use. The diagnostics for habits carried over from other languages catch these words without reserving them.

Contextual keywords ([lexical.contextual-keywords](../02-lexical.md#lexical.contextual-keywords)) cover the words that are both useful names and part of a form: `io`, `panic`, `alloc`, `spawn`, `without`, `field`. Each is read as a keyword only where the grammar accepts the keyword and no identifier could stand. Reading it there changes the meaning of no program, and `use std.io` still binds a module named `io` ([lexical.contextual-keywords.as-names](../02-lexical.md#lexical.contextual-keywords.as-names)). `escaping` is the one that costs a name: it is read at the start of every parameter, so a parameter can't be called `escaping`, though a local can.

`without` shows the argument in full. No identifier can stand where a limit clause can start, so reading `without` as a keyword there takes no name away. No statement begins with two identifiers either, so joining a line that begins with `without` and a limit to the line before it ([lexical.continuation-lines](../02-lexical.md#lexical.continuation-lines)) takes no statement apart.

## Literals

A decimal literal can't have a leading zero ([lexical.integer-literals](../02-lexical.md#lexical.integer-literals)), because C and the languages that follow it read `007` as octal. Stilt writes octal as `0o7`, and rejects the form that means different things in different languages. Prefixes are lowercase, so each number has one spelling.

There are no type suffixes such as `10u8`. A literal takes its type from its context ([numbers.integer-literals](../06-numbers.md#numbers.integer-literals)), and a suffix would be a second way to write a type. A letter or a digit directly after a literal is an error, and doesn't start the next token. So `10u8` and `0b102` are reported where they are written, and never split silently.

`1.` and `.5` are not floats ([lexical.float-literals](../02-lexical.md#lexical.float-literals)), and digits directly after a `.` are always an integer ([lexical.digits-after-dot](../02-lexical.md#lexical.digits-after-dot)). With these two rules, `t.0.1` reads as two tuple-field accesses, `0..n` as a range, and `.5` as a key path to a tuple's sixth field. The lexer needs no lookahead and no exceptions for them.

Every string literal interpolates ([lexical.string-literals](../02-lexical.md#lexical.string-literals)), so there is one string form and no prefix to remember. A literal brace is written `\{` ([lexical.escapes](../02-lexical.md#lexical.escapes)), like every other escape, where Python and Rust write `{{`. Accepting `{{` as an interpolation of a block is the alternative, and it is rejected. Nobody writes a block as an interpolation on purpose, and `{{` is the most common mistake that programmers coming from Python and Rust make in Stilt strings. So it is an invalid escape whose fix is `\{`. Strings, interpolations included, close on the line where they open, so a missing quote is reported on the line that holds it.

A format spec's width and precision have no leading zero ([lexical.format-specs](../02-lexical.md#lexical.format-specs)). In Python and Rust, `{:05}` pads with zeros. Stilt's spec grammar has no zero flag, and reading `05` as a width of 5 would make the same spec mean something else in Stilt. It is rejected instead, and zero padding is written as a fill and an alignment, `{x:0>5}`. The cost is that a fill pads the shown text, sign included, so a negative number gets its zeros before its `-`.

There is no character type ([lexical.no-characters](../02-lexical.md#lexical.no-characters)). Text is always a `str`, and `chars()` splits one into strings of one Unicode scalar value each. No program converts between characters and strings, and `'` stays a reserved token.

## Tokens

Tokens are lexed by maximal munch ([lexical.tokens](../02-lexical.md#lexical.tokens)), the rule that every reader already assumes: `..=` is one token, never `..` and `=`. A field read through an `Option` needs no mark ([types.fields-through-option](../07-types.md#types.fields-through-option)). So `?.` is not a token, and `?` before a `.` is always a hole.

The tokens `@`, `'` and `#` are reserved ([lexical.reserved-tokens](../02-lexical.md#lexical.reserved-tokens)): they are lexed, and stand in no form. A program that writes a binding `x @ Some(_)`, a character `'a'` or an attribute `#[…]` out of habit gets a syntax error at the token, and not an unexpected character.

## Newlines and terminators

Statements have no visible terminator. The lexer decides where a newline ends one, as Go's does ([lexical.terminator-insertion](../02-lexical.md#lexical.terminator-insertion)). Letting the parser decide, as Swift and Kotlin do, is more flexible. But it scatters the newline rules across the grammar, and it makes it harder to check that the grammar has no conflicts, as the reference interpreter's parser generator, Menhir, does. The lexer's rules fit in a few paragraphs, and every tool applies them the same way.

A line continues when the next one begins with `.`, `else`, `catch` or `|` ([lexical.continuation-lines](../02-lexical.md#lexical.continuation-lines)). A chain of calls, a fallback and a `catch` can then each start a line. A line that begins with `without` continues only when a limit follows on that line. A function's limit clause can go on the line after a long signature, while a local named `without` still starts a statement of its own.

`>` and `>>` end a line ([lexical.continuing-expression](../02-lexical.md#lexical.continuing-expression)), because they can close a generic type. In return, a signature without a body, as in a trait, needs no written terminator even when it ends in `Option<i64>`. The cost is that a comparison that spans lines has to be wrapped in parentheses.

No terminator is inserted inside `(` or `[` ([lexical.inside-brackets](../02-lexical.md#lexical.inside-brackets)), so a call or a list spans lines freely. A closure's block passed as an argument still gets its statements separated. Terminators never replace commas ([lexical.terminators-never-replace-commas](../02-lexical.md#lexical.terminators-never-replace-commas)), so a record's fields have one form whether they share a line or not. An explicit `;` is accepted, so one line may hold two short statements ([lexical.explicit-separators](../02-lexical.md#lexical.explicit-separators)), but the formatter never writes one.
