//! The table of names that other languages write where Stilt writes something else, with what
//! Stilt writes and why.

/// A name of another language, and what Stilt writes in its place.
pub(super) struct Entry {
    /// The names as other languages write them, a path's names joined by `.`.
    pub(super) names: &'static [&'static str],
    /// What Stilt writes instead, when it replaces the name alone.
    pub(super) stilt: Option<&'static str>,
    /// The message, with `$` standing for the name as written.
    pub(super) message: &'static str,
    pub(super) help: &'static str,
}

const PRIMITIVE: &str = "Stilt's primitive types are written in lower case, as `i64`, `f64`, \
                         `bool` and `str`.";
const COLLECTION: &str = "Stilt's collections are `List`, `Map` and `Set`, which every module \
                          sees without a `use`.";
const MISSING: &str = "A value that may be missing has the type `Option<T>`: it is \
                                  `None` when the value is missing and `Some(x)` when it is \
                                  there, and a `match` or an `else` reads it.";
const CONVERT: &str = "A number converts with a method, as `n.to_i64()` or `n.to_f64()`, and a \
                       string parses with the same methods, which give an `Option`, `None` when \
                       the text isn't a number.";

/// The types of other languages.
pub(super) const TYPES: &[Entry] = &[
    entry(
        &["String", "string", "Str"],
        "str",
        "Stilt's string type is `str`, not `$`",
        PRIMITIVE,
    ),
    entry(
        &[
            "int", "Int", "Integer", "integer", "long", "Long", "isize", "usize", "number",
        ],
        "i64",
        "Stilt's integer type is `i64`, not `$`",
        PRIMITIVE,
    ),
    entry(
        &["float", "Float", "double", "Double", "Number"],
        "f64",
        "Stilt's floating-point type is `f64`, not `$`",
        PRIMITIVE,
    ),
    entry(
        &["boolean", "Boolean", "Bool"],
        "bool",
        "Stilt's boolean type is `bool`, not `$`",
        PRIMITIVE,
    ),
    entry(
        &["char", "Char", "Character", "rune"],
        "str",
        "Stilt has no character type: a character is a `str`",
        PRIMITIVE,
    ),
    entry(
        &["Vec", "ArrayList", "Vector", "list"],
        "List",
        "Stilt's growable list is `List`, not `$`",
        COLLECTION,
    ),
    entry(
        &["HashMap", "BTreeMap", "Dictionary", "dict", "Dict", "map"],
        "Map",
        "Stilt's map is `Map`, not `$`",
        COLLECTION,
    ),
    entry(
        &["HashSet", "BTreeSet", "set"],
        "Set",
        "Stilt's set is `Set`, not `$`",
        COLLECTION,
    ),
    Entry {
        names: &["error", "Exception", "Throwable"],
        stilt: None,
        message: "Stilt has no `$` type: a function that can fail raises its own error type",
        help: "A function's row names the type of what it raises, as `/ raise<ParseError>`, and \
               `try f() catch e => …` handles it.",
    },
    entry(
        &["Optional", "Maybe", "Nullable"],
        "Option",
        "Stilt's optional value is `Option`, not `$`",
        MISSING,
    ),
    entry(
        &["void", "Void", "Unit"],
        "()",
        "Stilt has no `$`: a function that gives no value has the result type `()`",
        "A function whose result type isn't written gives `()`, the empty tuple.",
    ),
];

/// The values and functions of other languages.
pub(super) const VALUES: &[Entry] = &[
    Entry {
        names: NULLS,
        stilt: None,
        message: "Stilt has no `$`: a value that may be missing is an `Option`, as `None`",
        help: MISSING,
    },
    entry(
        &["True", "TRUE"],
        "true",
        "Stilt writes `true` in lower case",
        "Stilt's booleans are `true` and `false`.",
    ),
    entry(
        &["False", "FALSE"],
        "false",
        "Stilt writes `false` in lower case",
        "Stilt's booleans are `true` and `false`.",
    ),
    entry(
        &[
            "println",
            "printf",
            "puts",
            "echo",
            "console.log",
            "fmt.Println",
            "System.out.println",
            "Console.WriteLine",
        ],
        "print",
        "Stilt prints a line with `print`, not `$`",
        "`print` writes its string and a newline, and the function that calls it has `io` in \
         its row, as `fn main() / io`.",
    ),
    entry(
        &["eprintln", "console.error", "System.err.println"],
        "eprint",
        "Stilt prints a line to standard error with `eprint`, not `$`",
        "`eprint` writes its string and a newline to standard error, and the function that calls \
         it has `io` in its row.",
    ),
    Entry {
        names: &["len"],
        stilt: None,
        message: "Stilt has no `len` function: a length is a method, as `xs.len()`",
        help: "Lists, maps, sets and strings have a `len` method.",
    },
    Entry {
        names: &["err"],
        stilt: None,
        message: "Stilt has no `err` to test: a call that can fail raises its error",
        help: "A function names what it raises in its row, as `/ raise<E>`, and \
               `try f() catch e => …` handles the error where it is called.",
    },
    Entry {
        names: &["append"],
        stilt: None,
        message: "Stilt has no `append` function: a list grows with a method, as `xs.push(x)`",
        help: "`push` adds an element at the end of a list that a `var` holds, and changes it in \
               place.",
    },
    Entry {
        names: &["range"],
        stilt: None,
        message: "Stilt has no `range`: a `for` goes through a range, as `for i in 0..n`",
        help: "`0..n` counts from 0 up to `n`, leaving `n` out, and `0..=n` counts to `n` too. A \
               range is written only as what a `for` goes through.",
    },
    Entry {
        names: &["this"],
        stilt: Some("self"),
        message: "Stilt names the receiver `self`, not `this`",
        help: "A method takes its receiver as its first parameter, `self`, and reads its fields \
               as `self.x`.",
    },
    Entry {
        names: &["str", "String", "toString", "repr"],
        stilt: None,
        message: "Stilt has no `$` function: a value is written as text in a string, as `\"{x}\"`",
        help: "A string shows the value of an expression inside braces, as `\"{count}\"`, for any \
               type that implements `Show`.",
    },
    Entry {
        names: &[
            "ValueError",
            "TypeError",
            "KeyError",
            "IndexError",
            "RuntimeError",
            "Exception",
            "RangeError",
            "IllegalArgumentException",
            "IllegalStateException",
            "RuntimeException",
        ],
        stilt: None,
        message: "Stilt has no `$`: a function raises a value of an error type of its own",
        help: "Declare what can go wrong as a variant type, as `type ParseError = | Empty | \
               NotANumber(str)`, name it in the function's row, as `/ raise<ParseError>`, and \
               write `raise NotANumber(s)`.",
    },
    Entry {
        names: &["int", "float", "double", "parseInt", "parseFloat"],
        stilt: None,
        message: "Stilt has no `$` function: a value converts with a method, as `x.to_i64()`",
        help: CONVERT,
    },
];

/// The names that other languages give a missing value.
pub(super) const NULLS: &[&str] = &["null", "nil", "undefined", "NULL", "nullptr", "Nil"];

const fn entry(
    names: &'static [&'static str],
    stilt: &'static str,
    message: &'static str,
    help: &'static str,
) -> Entry {
    Entry {
        names,
        stilt: Some(stilt),
        message,
        help,
    }
}

/// The entry for `written` in `table`, if another language writes it.
pub(super) fn find<'t>(table: &'t [Entry], written: &str) -> Option<&'t Entry> {
    table.iter().find(|e| e.names.contains(&written))
}
