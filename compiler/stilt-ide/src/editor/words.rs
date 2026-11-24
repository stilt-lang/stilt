//! What a hover shows over a word that names no declaration: a keyword, a built-in effect, a
//! limit or a primitive type. Each shows the form it is written in, then what it means as the
//! guide teaches it, then the record that defines it, so that every word of the language explains
//! itself where it is written (lexical.primitive-type-names, lexical.keywords and
//! lexical.reserved-words).

use stilt_db::{Database, SourceFile};
use stilt_syntax::SyntaxKind::*;
use stilt_syntax::TextSize;

/// A word's entry: the form it is written in, and what it means, in Markdown.
type Entry = (&'static str, &'static str, &'static str);

/// The keywords and reserved words, by their text (lexical.keywords and lexical.reserved-words),
/// with the contextual keywords of lexical.contextual-keywords that aren't effects.
const KEYWORDS: [Entry; 51] = [
    (
        "const",
        "const NAME: Type = value",
        "Declares a constant. Its name is uppercase, its type is required, and its value is a constant expression, built only from literals, unary `-`, other constants, and tuples, lists, records and variants of those (declarations.constant-declarations and declarations.constant-expressions).",
    ),
    (
        "fn",
        "fn name(param: Type) -> Result / row { body }",
        "Declares a function: its parameters with their types, its result type, its effect row after `/`, and its body. A function type is written `fn(i64) -> bool` (declarations.function-types and declarations.function-declarations).",
    ),
    (
        "impl",
        "impl Type { … }\nimpl Trait for Type { … }",
        "Declares methods of a type, or implements a trait for a type (traits.impl-blocks and traits.implementing-trait).",
    ),
    (
        "module",
        "module name\nwithout panic",
        "Names the file's module in its header, which may limit the module's code with `without` (program.module-header and program.header-limits).",
    ),
    (
        "pub",
        "pub fn name() { … }",
        "Makes a declaration visible to the modules that import its own (program.visibility).",
    ),
    (
        "test",
        "test \"name\" { body }",
        "Declares a test, which `stilt test` runs. It passes when its body finishes without raising, panicking or calling `exit`, and it may perform `io` and raise (declarations.tests; program.test-declarations).",
    ),
    (
        "trait",
        "trait Name { fn method(self) -> Type }",
        "Declares a trait: methods that each type implementing it gives, as `Show` gives `show` (traits.declaring-trait).",
    ),
    (
        "type",
        "type Name = { field: Type }\ntype Name = | Variant(Type) | Other",
        "Declares a record type, with named fields, or a variant type, whose values are one of its variants. A type is never another name for a type (declarations.records, declarations.variant-types and declarations.no-aliases).",
    ),
    (
        "use",
        "use std.fs",
        "Imports a module by its path, and binds its last segment, here `fs`, to it (program.what-use-binds).",
    ),
    (
        "inout",
        "fn f(inout xs: List<i64>)\nf(inout xs)",
        "Marks a parameter whose argument the function may change: the caller's place holds the result when the call ends. The argument is marked too, and must be a place (expressions.inout-arguments; modes.what-can-be-modified).",
    ),
    (
        "let",
        "let pattern = value\nlet Some(x) = value else { … }",
        "Binds the names of a pattern to a value that doesn't change. With `else`, a pattern that may fail to match binds when it matches, and the `else` branch runs when it doesn't (expressions.let-else; patterns.let-else).",
    ),
    (
        "var",
        "var name = value",
        "Binds a name to a value that assignment may change. A change never reaches a copy made before it (values.let-and-var and values.independent-copies; expressions.assignment).",
    ),
    (
        "if",
        "if condition { … } else { … }",
        "Runs its block when the condition, a `bool`, is true, and its `else` branch otherwise. `if let pattern = value` tests a pattern, and `if T: Bound` a type parameter's bounds (expressions.if-let; meta.bound-tests).",
    ),
    (
        "else",
        "if c { … } else { … }\nvalue else fallback",
        "The branch of an `if` when its condition is false; after `let`, the block that runs when its pattern doesn't match; and between two expressions, the fallback: `e₁ else e₂` unwraps the `Option` `e₁`, and evaluates `e₂` only when it is `None` (expressions.option-fallback, expressions.else-after-if and expressions.let-else).",
    ),
    (
        "match",
        "match value {\n  pattern => result\n}",
        "Tests a value against patterns in order, and gives the result of the first arm that matches. The arms must cover every value (expressions.match; patterns.match).",
    ),
    (
        "for",
        "for x in xs { … }",
        "Runs its block for each element of a list, each entry of a map, or each integer of a range (expressions.for-iterables).",
    ),
    (
        "in",
        "for x in xs { … }",
        "Separates a `for` loop's pattern from what it iterates over (expressions.for-iterables).",
    ),
    (
        "while",
        "while condition { … }",
        "Runs its block for as long as its condition, a `bool`, is true (expressions.loops).",
    ),
    (
        "loop",
        "loop { … }",
        "Runs its block until a `break`, a `return` or a raise leaves it (expressions.loops).",
    ),
    (
        "break",
        "break",
        "Leaves the innermost loop (expressions.break-and-continue).",
    ),
    (
        "continue",
        "continue",
        "Goes on to the next turn of the innermost loop (expressions.break-and-continue).",
    ),
    (
        "return",
        "return value",
        "Leaves the function with a value.",
    ),
    (
        "assert",
        "assert condition",
        "Panics with the kind `assert` when its condition is false. The compiler's report shows both sides of a comparison of values that implement `Show` (program.assert-expr).",
    ),
    (
        "try",
        "try call(…)\ntry call(…) catch e => …",
        "Marks every call in its operand that can raise, so each place where code can fail is visible. It doesn't handle the error, which goes on to the caller, unless a `catch` follows (effects.marking).",
    ),
    (
        "catch",
        "try e catch pattern => value",
        "Handles the errors that the operand of its `try` raises, with arms as a `match` writes them. A catch-all that drops the error says why with `because` (effects.catch-alls-need-reason).",
    ),
    (
        "raise",
        "raise error",
        "Fails with an error of any type. It performs `raise<E>`, and has type `Never`, so it fits wherever a value is expected. A raise unwinds nothing: it is a tagged return value (effects.raise).",
    ),
    (
        "because",
        "catch _ because \"reason\" => value",
        "Says why a catch-all may drop the error it catches (effects.catch-alls-need-reason).",
    ),
    ("true", "true", "The `bool` that is true."),
    ("false", "false", "The `bool` that is false."),
    (
        "self",
        "fn method(self) -> Type",
        "The value a method is called on (traits.methods).",
    ),
    (
        "Self",
        "fn new() -> Self",
        "The type of an `impl` or of a trait's implementor (traits.impl-blocks).",
    ),
    (
        "where",
        "fn f<C: Coll>(c: C) where C.Item: Show",
        "Bounds a member type, which has no place beside a type parameter (traits.where).",
    ),
    (
        "syntax",
        "syntax name {\n  ($x: expr) => template\n}",
        "Declares a pattern macro: arms, each a pattern of fragments and a template. A use writes the name with `!`, as `name!(…)` (macros.syntax-declarations).",
    ),
    (
        "effect",
        "effect Name { fn op() -> Type }",
        "Declares an effect and its operations. `Name.op(…)` performs one, a row names the effect, and a handler installed by `with` answers it (handlers.declaring-effect and handlers.performing-operation).",
    ),
    (
        "handler",
        "handler Name { fn op() -> Type { … } }\nhandler Name -> R { … }",
        "Implements every operation of an effect. One written `-> R` takes control: `resume(v)` goes on with `v` (handlers.handler-literals).",
    ),
    (
        "with",
        "with handler { … }",
        "Installs a handler while its block runs, so that it answers each performance of its effect there (handlers.with).",
    ),
    (
        "resume",
        "resume(value)",
        "In an operation of a handler written `-> R`, goes on where the operation was performed, with a value, at most once (handlers.resuming and handlers.resume-at-most-once).",
    ),
    (
        "async",
        "fn f() / async",
        "The effect of code that starts tasks or waits for them, as `std.task` does (tasks.async).",
    ),
    (
        "await",
        "task.await()",
        "Waits for a task's value, performing `async` (tasks.task-functions).",
    ),
    (
        "when",
        "when total { … }",
        "Waits until it holds every `Shared` value it names, runs its block with each name standing for its value, and lets them go. A function that runs one has the fact `locks` (shared.when and shared.locks).",
    ),
    (
        "yield",
        "fn at(inout self, i: i64) -> inout T { yield self.items[i] }",
        "In a projection, a function whose result is `inout T`, gives the caller a place, and resumes once the caller is done with it (projections.yield).",
    ),
    (
        "comptime",
        "comptime for x in xs { … }",
        "Asserts that what controls the `for`, `if` or `match` after it is known at compile time, so a release build may unroll the loop or keep one branch. It changes nothing else (meta.staging-annotations).",
    ),
    (
        "macro",
        "macro name(input: meta.Expr) -> meta.Expr { … }",
        "Declares a procedural macro: a function from syntax to syntax, which runs while the program is checked (macros.procedural-declarations).",
    ),
    (
        "quote",
        "quote { … }\nquote type { … }",
        "Builds code as a value of `std.meta`: an expression, or a type, a pattern or a field after its word. `$x` splices a value in, and `$..xs` a list of them (macros.quote).",
    ),
    (
        "extern",
        "extern fn strlen(s: c.Str) -> u64\npub extern fn name(x: i64) -> i64",
        "Without a body, declares a foreign function, which C gives under its name and only an `unsafe` block calls (c.foreign-functions). With one, after `pub`, exports a function to C, which calls it by its name, and `stilt build --lib` writes a library of the exported functions and a header (c.exported-functions and c.static-library).",
    ),
    (
        "unsafe",
        "unsafe because \"reason\" { … }\nwithout unsafe",
        "Runs the operations that can break the language's guarantees, calls of foreign functions and reads and writes through `std.c`'s pointers, and says why they are sound. A function that holds one has the fact `unsafe`, which `without unsafe` limits (c.unsafe-operations, c.unsafe-because and c.without-unsafe).",
    ),
    (
        "without",
        "without panic, alloc",
        "Turns implicit effects and capabilities into errors. A module's limit covers its functions' bodies, a function's covers its own body, and both cover the functions they name, in any module (facts.without; effects.without-panic).",
    ),
    (
        "escaping",
        "fn f(escaping g: fn() / io)",
        "Marks a function parameter that the function may keep. Its row is then exactly the one written, where a parameter that isn't escaping passes its argument's effects through (effects.escaping-parameters).",
    ),
    (
        "meta",
        "meta use std.meta",
        "Imports a module for the code of the program's macros (macros.meta-use).",
    ),
    (
        "pattern",
        "quote pattern { … }",
        "After `quote`, quotes a pattern (macros.quote).",
    ),
    (
        "field",
        "quote field { name: value }",
        "After `quote`, quotes one field of a record literal (macros.quote).",
    ),
];

/// The effects of a row, and the limits and capabilities of `without`, by their text.
const EFFECTS: [Entry; 17] = [
    (
        "io",
        "fn f() / io",
        "The function reaches the world. Below `io`, the capabilities it reaches are inferred, and `stilt show` prints them, as `io: fs, clock` (effects.effect-names; facts.io-and-capabilities).",
    ),
    (
        "raise",
        "fn f() -> T / raise<E>",
        "The function may raise an error of type `E`, and each call of it is marked with `try` (effects.raise and effects.marking).",
    ),
    (
        "async",
        "fn f() / async",
        "The function may start tasks or wait for them, as `std.task` does (tasks.async).",
    ),
    (
        "panic",
        "without panic",
        "Rules out every operation that may panic: indexing, division and the library's functions that check their input, unless verification proves the check can't fail (effects.panicking-operations and effects.without-panic).",
    ),
    (
        "overflow",
        "without overflow",
        "Rules out every operation that may overflow an integer, which panics at run time even under `without panic`: integer `+`, `-` and `*`, signed `/` and `%`, shifts, and the integer functions that may overflow, unless verification proves they can't (effects.overflow-effect and effects.without-overflow).",
    ),
    (
        "alloc",
        "without alloc",
        "Rules out every operation that may allocate: literals of lists and closures, interpolated strings, writes through an index, and the natives whose results hold a `str`, a `List` or a `Map` (facts.allocation and facts.without-alloc).",
    ),
    (
        "div",
        "without div",
        "Rules out possible non-termination: a `loop`, a `while` and recursion that verification doesn't prove to end, and calls of stored function values. `without panic, div` means total (facts.div, facts.descending-self-calls and facts.without-div).",
    ),
    (
        "copy",
        "without copy",
        "Rules out the writes that copy shared data (facts.copy and facts.without-copy).",
    ),
    (
        "locks",
        "without locks",
        "Rules out `when`, and the calls of functions that run one (shared.locks).",
    ),
    (
        "fs",
        "without fs",
        "Rules out reaching files, through `std.fs` (facts.without).",
    ),
    (
        "net",
        "without net",
        "Rules out reaching the network, through `std.net` and `std.http` (facts.without).",
    ),
    (
        "clock",
        "without clock",
        "Rules out reading the clock, through `std.clock` (facts.without).",
    ),
    (
        "env",
        "without env",
        "Rules out reading the environment, through `std.cli` (facts.without).",
    ),
    (
        "console",
        "without console",
        "Rules out the console: `print`, `eprint` and the console functions of `std.io` (facts.without).",
    ),
    (
        "rand",
        "without rand",
        "Rules out entropy, through `random.entropy` (facts.without).",
    ),
    (
        "spawn",
        "without spawn",
        "Rules out starting tasks, through `std.task`'s `spawn` (facts.without; tasks.implicit-effects-and-capabilities).",
    ),
    (
        "exec",
        "without exec",
        "Rules out running other programs, through `std.process` (facts.without).",
    ),
];

/// The primitive types (lexical.primitive-type-names), and `Never`.
const PRIMITIVES: [Entry; 13] = [
    ("bool", "bool", "`true` or `false`."),
    (
        "i8",
        "i8",
        "A signed integer of 8 bits, from `i8.MIN`, -128, to `i8.MAX`, 127.",
    ),
    (
        "i16",
        "i16",
        "A signed integer of 16 bits, from `i16.MIN` to `i16.MAX`.",
    ),
    (
        "i32",
        "i32",
        "A signed integer of 32 bits, from `i32.MIN` to `i32.MAX`.",
    ),
    (
        "i64",
        "i64",
        "A signed integer of 64 bits, from `i64.MIN` to `i64.MAX`, the type of an integer literal that nothing else types.",
    ),
    (
        "u8",
        "u8",
        "An unsigned integer of 8 bits, from 0 to `u8.MAX`, 255.",
    ),
    (
        "u16",
        "u16",
        "An unsigned integer of 16 bits, from 0 to `u16.MAX`.",
    ),
    (
        "u32",
        "u32",
        "An unsigned integer of 32 bits, from 0 to `u32.MAX`.",
    ),
    (
        "u64",
        "u64",
        "An unsigned integer of 64 bits, from 0 to `u64.MAX`.",
    ),
    ("f32", "f32", "An IEEE 754 float of 32 bits."),
    (
        "f64",
        "f64",
        "An IEEE 754 float of 64 bits, the type of a float literal that nothing else types.",
    ),
    (
        "str",
        "str",
        "Text, as UTF-8 bytes. Every string literal interpolates, as in `\"{name}\"` (lexical.string-literals).",
    ),
    (
        "Never",
        "Never",
        "The type without values: of `return`, `raise`, `break`, `continue` and calls such as `exit` and `panic`, so each fits wherever a value is expected.",
    ),
];

/// What a hover over the word at `offset` of `file` shows, when it is a keyword, a built-in
/// effect, a limit or a primitive type.
pub(crate) fn hover(db: &Database, file: SourceFile, offset: TextSize) -> Option<String> {
    let tree = stilt_db::parse(db, file).syntax();
    let token = super::syntax::token_at(&tree, offset)?;
    let kind = token.kind();
    let text = token.text();
    let in_row = matches!(kind, RAISE_KW | ASYNC_KW | IO_KW)
        && token
            .parent()
            .is_some_and(|p| matches!(p.kind(), ROW_RAISE | ROW_ASYNC | ROW_IO));
    let (table, what): (&[Entry], &str) = if in_row || (PANIC_KW..=LOCKS_KW).contains(&kind) {
        (&EFFECTS, if in_row { "effect" } else { "limit" })
    } else if super::syntax::is_keyword(kind) {
        (&KEYWORDS, "keyword")
    } else if matches!(kind, LOWER_IDENT | UPPER_IDENT) && stilt_syntax::is_primitive(text)
        || text == "Never"
    {
        (&PRIMITIVES, "type")
    } else {
        return None;
    };
    let (_, form, meaning) = table.iter().find(|(word, ..)| *word == text)?;
    Some(format!(
        "```stilt\n{form}\n```\n\n**`{text}`** · {what}\n\n{meaning}"
    ))
}

#[cfg(test)]
mod tests {
    use super::{EFFECTS, KEYWORDS, PRIMITIVES};

    #[test]
    fn every_keyword_and_primitive_type_is_explained_once() {
        let mut words: Vec<&str> = KEYWORDS.iter().map(|(w, ..)| *w).collect();
        words.sort_unstable();
        words.dedup();
        assert_eq!(words.len(), KEYWORDS.len());
        for word in stilt_syntax::PRIMITIVE_TYPES {
            assert!(PRIMITIVES.iter().any(|(w, ..)| *w == word), "{word}");
        }
        for word in ["io", "raise", "async"] {
            assert!(EFFECTS.iter().any(|(w, ..)| *w == word), "{word}");
        }
        // Every fact that a limit names explains itself, `unsafe` as a keyword
        // (facts.inferred-facts).
        for (word, ..) in crate::show::facts::FACTS
            .iter()
            .filter(|(w, ..)| *w != "foreign")
        {
            let explained = EFFECTS.iter().chain(&KEYWORDS).any(|(w, ..)| w == word);
            assert!(explained, "{word}");
        }
    }
}
