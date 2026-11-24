//! The natives of `std.view` (views.making-view, views.functions-of-views, views.making-iterator
//! and views.adapters) but `into`, `part` and `split`, which take a place
//! (projections.writable-views). A view's value is the part of its source that it views: nothing
//! can change the source while the view lives (views.change-while-viewed), so a copy of the part
//! can't be told from a window into it (reference/rationale/13-modes.md, Views); a window reaches these natives as the part
//! it views (projections.places-through-views).

use std::sync::Arc;

use super::Native;
use crate::eval::{Machine, R, panic};
use crate::value::{IntKind, IterValue, Value};

/// The part of a string or a list from `start` up to `stop`, counted as `slice` counts (rules
/// 3 and 5).
fn slice<'a>(v: &Value<'a>, start: i128, stop: i128) -> R<'a> {
    let (length, what) = match v {
        Value::Str(s) => (
            s.get().len(),
            format!("a string of {} bytes", s.get().len()),
        ),
        _ => (
            v.as_list().len(),
            format!("a list of length {}", v.as_list().len()),
        ),
    };
    let fits = 0 <= start && start <= stop && usize::try_from(stop).is_ok_and(|s| s <= length);
    if !fits {
        return panic(
            "bounds",
            format!("the range {start}..{stop} is out of bounds for {what}"),
        );
    }
    let (a, b) = (
        usize::try_from(start).unwrap_or(0),
        usize::try_from(stop).unwrap_or(0),
    );
    match v {
        Value::Str(s) => {
            let s = s.get();
            if !(s.is_char_boundary(a) && s.is_char_boundary(b)) {
                return panic(
                    "utf8-boundary",
                    format!("the range {a}..{b} splits a UTF-8 sequence"),
                );
            }
            Ok(Value::str(&s[a..b]))
        }
        _ => Ok(Value::list(v.as_list()[a..b].to_vec())),
    }
}

fn length(v: &Value<'_>) -> usize {
    match v {
        Value::Str(s) => s.get().len(),
        _ => v.as_list().len(),
    }
}

/// `impl<T> View<T>` (views.making-view and views.functions-of-views).
pub(super) fn view<'a>(_: &mut Machine<'a>, n: &Native<'_>, values: &mut [Value<'a>]) -> R<'a> {
    let int = |i: usize| values.get(i).map_or(0, Value::as_int);
    match n.name {
        "of" | "view" => slice(&values[0], int(1), int(2)),
        "all" | "copy" => Ok(values[0].clone()),
        "len" => Ok(Value::i64(i128::try_from(length(&values[0])).unwrap_or(0))),
        "is_empty" => Ok(Value::Bool(length(&values[0]) == 0)),
        _ => unreachable!("the table names every native of `View`: {}", n.name),
    }
}

/// The functions of the module: `get`, `chars` and `bytes` (views.functions-of-views), and the
/// iterators `range` and `of_map` (views.making-iterator).
pub(super) fn function<'a>(_: &mut Machine<'a>, n: &Native<'_>, values: &mut [Value<'a>]) -> R<'a> {
    let elements = |xs: Vec<Value<'a>>| Ok(Value::Iter(Arc::new(IterValue::Elements(xs))));
    match n.name {
        "get" => {
            let i = values[1].as_int();
            let xs = values[0].as_list();
            Ok(Value::option(
                usize::try_from(i).ok().and_then(|i| xs.get(i)).cloned(),
            ))
        }
        "chars" => elements(
            values[0]
                .as_str()
                .chars()
                .map(|c| Value::str(c.to_string()))
                .collect(),
        ),
        "bytes" => elements(
            values[0]
                .as_str()
                .bytes()
                .map(|b| Value::Int(i128::from(b), IntKind::U8))
                .collect(),
        ),
        "range" => Ok(Value::Iter(Arc::new(IterValue::Range(
            values[0].as_int(),
            values[1].as_int(),
        )))),
        "of_map" => {
            let Value::Map(map) = &values[0] else {
                unreachable!("`of_map` takes a map")
            };
            let pairs = map.entries.get().iter();
            elements(
                pairs
                    .map(|(k, v)| Value::tuple(vec![k.clone(), v.clone()]))
                    .collect(),
            )
        }
        _ => unreachable!("the table names every function of `std.view`: {}", n.name),
    }
}
