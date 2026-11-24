//! The natives of the standard library that a macro's run calls: every native that
//! performs nothing, found by its module, its owner and its name ([`native`]). Those that
//! perform `io` have no entry: a macro's body that reaches one is E0502, so no run calls them
//! (macros.procedural-bodies). `into`, `part` and `split` of `std.view` take a place, and the
//! evaluation of calls runs them ([`crate::eval::windows`]). The natives that reach C, and foreign
//! functions, stop the run ([`reaches_c`]).

mod collections;
mod iters;
mod numbers;
mod shapes;
mod strs;
mod tasks;
mod views;

use std::sync::LazyLock;

use stilt_hir::hir::{Item, Name};
use stilt_types::ty::Ty;

use crate::eval::{Machine, R, panic};
use crate::value::{IntKind, Value};

pub(crate) use iters::Cursor;

/// A call of a native: its owner, if it is a member, its name, and its type arguments, its
/// impl's first.
pub(crate) struct Native<'c> {
    pub(crate) owner: Option<&'c str>,
    pub(crate) name: &'c str,
    pub(crate) targs: &'c [Ty],
}

/// What runs a native, on the values of its arguments, leaving its `inout` parameters' final
/// values there.
pub(crate) type Run = for<'a> fn(&mut Machine<'a>, &Native<'_>, &mut [Value<'a>]) -> R<'a>;

const INTEGER: &[&str] = &[
    "abs",
    "min",
    "max",
    "to_i8",
    "to_i16",
    "to_i32",
    "to_i64",
    "to_u8",
    "to_u16",
    "to_u32",
    "to_u64",
    "to_f32",
    "to_f64",
    "wrap_to_i8",
    "wrap_to_i16",
    "wrap_to_i32",
    "wrap_to_i64",
    "wrap_to_u8",
    "wrap_to_u16",
    "wrap_to_u32",
    "wrap_to_u64",
    "checked_add",
    "checked_sub",
    "checked_mul",
    "saturating_add",
    "saturating_sub",
    "pow",
    "div_euclid",
    "rem_euclid",
    "count_ones",
    "leading_zeros",
    "trailing_zeros",
    "gcd",
    "lcm",
];
const FLOAT: &[&str] = &[
    "sqrt", "floor", "ceil", "trunc", "round", "abs", "min", "max", "is_nan", "to_i8", "to_i16",
    "to_i32", "to_i64", "to_u8", "to_u16", "to_u32", "to_u64", "to_f32", "to_f64",
];
const MATH: &[&str] = &[
    "pow", "exp", "log", "log2", "log10", "sin", "cos", "tan", "asin", "acos", "atan", "atan2",
    "sinh", "cosh", "tanh", "cbrt", "hypot",
];
const LIST: &[&str] = &[
    "new",
    "len",
    "is_empty",
    "get",
    "push",
    "pop",
    "insert",
    "remove",
    "slice",
    "sorted_by",
    "sorted_desc_by",
];
const MAP: &[&str] = &[
    "new",
    "with_default",
    "len",
    "is_empty",
    "contains",
    "get",
    "insert",
    "remove",
];
const ITER: &[&str] = &[
    "of",
    "of_view",
    "map",
    "filter",
    "take",
    "skip",
    "take_while",
    "skip_while",
    "enumerate",
    "zip",
    "chain",
    "collect",
    "fold",
    "count",
    "any",
    "all",
    "find",
    "first",
    "last",
    "nth",
    "max",
    "min",
];

/// The names of the members of `std.meta`'s type `owner` that are native, and what runs them.
fn meta_member(owner: &str) -> Option<(&'static [&'static str], Run)> {
    let accessors: &'static [&'static str] = match owner {
        "Integer" => &["text", "parse"],
        "Convert" => &["get", "make"],
        "Sized" => &["get", "make", "len"],
        "Fields" => &["len", "build"],
        "Field" => &["name", "index", "get"],
        "Cases" => &["len"],
        "Case" => &["name", "index", "get", "make"],
        _ => {
            let names: &'static [&'static str] = match owner {
                "Span" => &["to"],
                "Token" => &["kind", "span", "name"],
                "Text" => &["value", "span", "lex"],
                "Name" => &["text", "span"],
                "Expr" | "Pattern" | "Type" | "FieldInit" => &["span"],
                "Error" => &["note"],
                _ => return None,
            };
            return Some((names, |m, n, values| {
                crate::meta::natives::member(m, n.owner.unwrap_or(""), n.name, values)
            }));
        }
    };
    Some((accessors, shapes::shapes))
}

/// The native that runs `owner.name` of the module `home`, or its function `name` when it has
/// no owner, if it performs nothing.
pub(crate) fn native(home: &str, owner: Option<&str>, name: &str) -> Option<Run> {
    let lends = matches!(
        (owner, name),
        (Some("List"), "with_ptr" | "with_mut_ptr") | (Some("str"), "with_c_str")
    );
    if home == "std.c" || (home == "std.prelude" && lends) {
        Some(reaches_c)
    } else {
        computing(home, owner, name)
    }
}

/// The native that runs `owner.name` of the module `home`, or its function `name`, among those
/// that compute a value.
fn computing(home: &str, owner: Option<&str>, name: &str) -> Option<Run> {
    let (names, run): (&[&str], Run) = match (home, owner) {
        ("std.prelude", Some(o)) if IntKind::named(o).is_some() => (INTEGER, |_, n, values| {
            let k = IntKind::named(n.owner.unwrap_or("")).unwrap_or(IntKind::I64);
            numbers::integer(k, n.name, values)
        }),
        ("std.prelude", Some("f32" | "f64")) => (FLOAT, |_, n, values| {
            numbers::float(n.owner == Some("f32"), n.name, values)
        }),
        ("std.prelude", Some("str")) => (strs::NAMES, |_, n, values| strs::call(n.name, values)),
        ("std.prelude", Some("List")) => {
            (LIST, |m, n, values| collections::list(m, n.name, values))
        }
        ("std.prelude", Some("Map")) => (MAP, |m, n, values| collections::map(m, n.name, values)),
        ("std.prelude", None) => (
            &["panic", "unreachable", "unwrap_failed", "expect_failed"],
            prelude_panic,
        ),
        ("std.math", None) => (MATH, |_, n, values| {
            let f = |i: usize| match values.get(i) {
                Some(Value::Float(x, _)) => *x,
                _ => 0.0,
            };
            Ok(numbers::math(n.name, f(0), f(1)))
        }),
        ("std.meta", Some(o)) => meta_member(o)?,
        ("std.meta", None) => (
            &[
                "fresh",
                "error",
                "parse_expr",
                "parse_pattern",
                "parse_type",
            ],
            |m, n, values| crate::meta::natives::function(m, n.name, values),
        ),
        ("std.view", None) => (
            &["get", "chars", "bytes", "range", "of_map"],
            views::function,
        ),
        ("std.view", Some("View")) => (
            &["of", "all", "len", "is_empty", "view", "copy"],
            views::view,
        ),
        ("std.view", Some("Iter")) => (ITER, iters::iter),
        ("std.lazy", Some("Lazy")) => (&["new", "get"], tasks::lazy),
        ("std.sync", Some("Shared")) => (&["new"], |_, _, values| {
            Ok(crate::eval::shared(values[0].clone()))
        }),
        ("std.task", None) => (&["spawn", "threads", "sequential"], tasks::task),
        ("std.task", Some("Task")) => (&["await"], tasks::task),
        ("std.task", Some("Scope")) => (&["spawn"], tasks::task),
        ("std.par", None) => (&["map", "each", "both", "fold"], tasks::par),
        ("std.array", None) => (&["fill", "from_list"], tasks::array),
        ("std.array", Some("Array")) => (&["map"], tasks::array),
        _ => return None,
    };
    names.contains(&name).then_some(run)
}

/// Stops a macro's run, which performs nothing, where it would reach C: at a foreign function,
/// a native of `std.c` or a method that lends C a list or a string (c.calls).
pub(crate) fn reaches_c<'a>(_: &mut Machine<'a>, n: &Native<'_>, _: &mut [Value<'a>]) -> R<'a> {
    Err(crate::eval::Flow::Stop(crate::eval::Stop::C(
        n.name.to_owned(),
    )))
}

/// The panics of the prelude's functions: `panic` and `expect` quote their message as their
/// detail, and `unwrap` gives its own (program.panic-detail; effects.panic-kinds).
fn prelude_panic<'a>(_: &mut Machine<'a>, n: &Native<'_>, values: &mut [Value<'a>]) -> R<'a> {
    let msg = values.first().map_or("", Value::as_str);
    match n.name {
        "panic" => panic("explicit", stilt_runtime::quoted(msg)),
        "unwrap_failed" => panic("unwrap", msg.to_owned()),
        "expect_failed" => panic("unwrap", stilt_runtime::quoted(msg)),
        _ => panic("unreachable", "reached unreachable()"),
    }
}

/// Calls the native `item`, a member of `owner` when it has one, with the type arguments
/// `targs`, which `run` runs, found when the run's image was made.
pub(crate) fn call<'a>(
    m: &mut Machine<'a>,
    run: Option<Run>,
    (owner, item, targs): (Option<&Item>, &Item, &[Ty]),
    values: &mut [Value<'a>],
) -> R<'a> {
    static VIEW: LazyLock<Name> = LazyLock::new(|| Name::from("std.view"));
    let owner = owner.map(|o| &*o.name);
    let Some(run) = run else {
        unreachable!(
            "`{}.{}` performs `io`, which E0502 rejects in a macro's body before any run \
             (macros.procedural-bodies)",
            item.home, item.name
        )
    };
    // A native of `std.view` reads a writable view as the part it views
    // (projections.places-through-views).
    if item.home == *VIEW {
        for v in values.iter_mut() {
            *v = m.thaw(std::mem::replace(v, Value::unit()))?;
        }
    }
    let native = Native {
        owner,
        name: &item.name,
        targs,
    };
    run(m, &native, values)
}

/// Whether `owner.name` is a native constant whose value [`constant`] gives.
pub(crate) fn has_constant(owner: &str, name: &str) -> bool {
    matches!(owner, "f32" | "f64") && matches!(name, "NAN" | "INFINITY")
}

/// The value of a native constant: `NAN` and `INFINITY` of `f32` and `f64`, the only ones of
/// the standard library.
pub(crate) fn constant<'a>(owner: &Item, name: &str) -> Value<'a> {
    assert!(
        has_constant(&owner.name, name),
        "the native constants are `NAN` and `INFINITY` of the float types"
    );
    let x = if name == "NAN" {
        f64::NAN
    } else {
        f64::INFINITY
    };
    crate::eval::ops_float(x, &*owner.name == "f32")
}

#[cfg(test)]
mod tests;
