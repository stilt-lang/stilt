//! The natives of `List` and `Map` (std.lists and std.maps), on the values of a run: a map keeps
//! its entries in the order their keys were first inserted, and finds a key by the key type's `Eq`.

use std::cmp::Ordering;
use std::sync::Arc;

use crate::eval::{Machine, R, panic, reserve};
use crate::value::{Counted, MapValue, Value};

fn index_of(values: &[Value<'_>], i: usize) -> i128 {
    values.get(i).map_or(0, Value::as_int)
}

/// The native `name` of `List`, which may change its first argument, an `inout` receiver.
pub(super) fn list<'a>(m: &mut Machine<'a>, name: &str, values: &mut [Value<'a>]) -> R<'a> {
    let size = std::mem::size_of::<Value<'a>>();
    let len = values.first().map_or(0, |v| v.as_list().len());
    let bounds = |i: i128, len: usize| {
        panic::<Value<'a>>(
            "bounds",
            format!("index {i} is out of bounds for a list of length {len}"),
        )
    };
    match name {
        "new" => Ok(Value::list(Vec::new())),
        "len" => Ok(Value::i64(len as i128)),
        "is_empty" => Ok(Value::Bool(len == 0)),
        "get" => {
            let i = index_of(values, 1);
            let x = usize::try_from(i)
                .ok()
                .and_then(|i| values[0].as_list().get(i).cloned());
            Ok(Value::option(x))
        }
        "push" => {
            reserve(size)?;
            let x = values[1].clone();
            edit(&mut values[0], |xs| xs.push(x));
            Ok(Value::unit())
        }
        "pop" => Ok(Value::option(edit(&mut values[0], Vec::pop))),
        "insert" => {
            let i = index_of(values, 1);
            let Some(at) = usize::try_from(i).ok().filter(|&at| at <= len) else {
                return bounds(i, len);
            };
            reserve(size)?;
            let x = values[2].clone();
            edit(&mut values[0], |xs| xs.insert(at, x));
            Ok(Value::unit())
        }
        "remove" => {
            let i = index_of(values, 1);
            let Some(at) = usize::try_from(i).ok().filter(|&at| at < len) else {
                return bounds(i, len);
            };
            Ok(edit(&mut values[0], |xs| xs.remove(at)))
        }
        "slice" => slice(values, len, size),
        "sorted_by" | "sorted_desc_by" => sorted(m, name == "sorted_desc_by", values),
        _ => unreachable!("the table names every native of `List`: {name}"),
    }
}

/// The elements of a list from `start` to `end`, weighed before they are copied.
fn slice<'a>(values: &[Value<'a>], len: usize, size: usize) -> R<'a> {
    let (start, end) = (index_of(values, 1), index_of(values, 2));
    if start < 0 || start > end || end > len as i128 {
        return panic(
            "bounds",
            format!("the range {start}..{end} is out of bounds for a list of length {len}"),
        );
    }
    let (from, to) = (
        usize::try_from(start).unwrap_or(0),
        usize::try_from(end).unwrap_or(0),
    );
    reserve((to - from) * size)?;
    Ok(Value::list(values[0].as_list()[from..to].to_vec()))
}

/// Changes the list a value holds.
fn edit<'a, T>(v: &mut Value<'a>, f: impl FnOnce(&mut Vec<Value<'a>>) -> T) -> T {
    if let Value::List(xs) = v {
        Arc::make_mut(xs).update(f)
    } else {
        let mut empty = Vec::new();
        f(&mut empty)
    }
}

/// A stable sort by keys that the closure gives, each called once, in order.
fn sorted<'a>(m: &mut Machine<'a>, descending: bool, values: &mut [Value<'a>]) -> R<'a> {
    let xs = values[0].as_list().to_vec();
    let key = values[1].clone();
    let mut keyed = Vec::with_capacity(xs.len());
    for x in xs {
        let mut args = vec![x.clone()];
        let k = m.apply_value(&key, &mut args)?;
        keyed.push((k, x));
    }
    let mut error = None;
    let mut order = |a: &Value<'a>, b: &Value<'a>| -> Ordering {
        if error.is_some() {
            return Ordering::Equal;
        }
        match m.order(a, b) {
            Ok(o) => o,
            Err(e) => {
                error = Some(e);
                Ordering::Equal
            }
        }
    };
    keyed.sort_by(|(a, _), (b, _)| {
        let o = order(a, b);
        if descending { o.reverse() } else { o }
    });
    if let Some(e) = error {
        return Err(e);
    }
    Ok(Value::list(keyed.into_iter().map(|(_, x)| x).collect()))
}

/// The native `name` of `Map`, which may change its first argument, an `inout` receiver.
pub(super) fn map<'a>(m: &mut Machine<'a>, name: &str, values: &mut [Value<'a>]) -> R<'a> {
    let empty = |default| {
        Value::Map(Arc::new(MapValue {
            entries: Counted::new(Vec::new()),
            default,
        }))
    };
    match name {
        "new" => return Ok(empty(None)),
        "with_default" => return Ok(empty(values.first().cloned())),
        _ => {}
    }
    let Value::Map(map) = &values[0] else {
        return Ok(Value::unit());
    };
    let entries = map.entries.get().clone();
    let found = match values.get(1) {
        Some(k) => m.find_key(&entries, k)?,
        None => None,
    };
    match name {
        "len" => Ok(Value::i64(entries.len() as i128)),
        "is_empty" => Ok(Value::Bool(entries.is_empty())),
        "contains" => Ok(Value::Bool(found.is_some())),
        "get" => Ok(Value::option(found.map(|i| entries[i].1.clone()))),
        "insert" => {
            reserve(2 * std::mem::size_of::<Value<'a>>())?;
            let (k, v) = (values[1].clone(), values[2].clone());
            edit_map(&mut values[0], |e| match found {
                Some(i) => e[i].1 = v,
                None => e.push((k, v)),
            });
            Ok(Value::unit())
        }
        "remove" => {
            let removed = found.map(|i| edit_map(&mut values[0], |e| e.remove(i).1));
            Ok(Value::option(removed))
        }
        _ => unreachable!("the table names every native of `Map`: {name}"),
    }
}

fn edit_map<'a, T>(v: &mut Value<'a>, f: impl FnOnce(&mut Vec<(Value<'a>, Value<'a>)>) -> T) -> T {
    match v {
        Value::Map(map) => Arc::make_mut(map).entries.update(f),
        _ => f(&mut Vec::new()),
    }
}
