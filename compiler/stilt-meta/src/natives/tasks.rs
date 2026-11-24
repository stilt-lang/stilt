//! The natives of `std.lazy` (polymorphism.lazy-values), `std.task` (tasks.std-task;
//! tasks.scopes), `std.par` (par.std-par) and `std.array` (generics.arrays). A program means its
//! sequential run (tasks.sequential-run; parallel-like-sequential), which is what each runs here: a
//! task runs to its end where it starts, and a parallel function calls its closures from the first
//! element to the last.

use std::sync::{Arc, Mutex, PoisonError};

use stilt_hir::hir::{self, Item, Name};
use stilt_types::ty::Ty;

use super::Native;
use crate::eval::{Machine, R, panic, reserve};
use crate::value::{Deferred, HandlerValue, Value, prelude};

fn task_item(name: &str) -> Item {
    Item {
        home: Name::from("std.task"),
        name: Name::from(name),
    }
}

fn arg<'a>(values: &[Value<'a>], i: usize) -> Value<'a> {
    values.get(i).cloned().unwrap_or_else(Value::unit)
}

/// `Lazy.new` keeps its function, and `get` runs it the first time any copy of the value asks,
/// and keeps what it returns.
pub(super) fn lazy<'a>(m: &mut Machine<'a>, n: &Native<'_>, values: &mut [Value<'a>]) -> R<'a> {
    match (n.name, arg(values, 0)) {
        ("new", compute) => Ok(Value::Deferred(Arc::new(Deferred {
            compute,
            result: Mutex::new(None),
        }))),
        ("get", Value::Deferred(d)) => {
            let kept = d
                .result
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .clone();
            if let Some(v) = kept {
                return Ok(v);
            }
            let v = m.apply_value(&d.compute, &mut Vec::new())?;
            *d.result.lock().unwrap_or_else(PoisonError::into_inner) = Some(v.clone());
            Ok(v)
        }
        _ => unreachable!("the table names every native of `Lazy`: {}", n.name),
    }
}

/// The tasks of tasks.std-task and tasks.sequential-run, and those of a scope (tasks.scopes and
/// tasks.scope-failure): a task runs to its end where it starts, under either handler, and its
/// handle holds its value, so a task that raises raises where it is spawned. `scope` performs `io`,
/// which no macro's run reaches (macros.procedural-bodies), so no run has a scope to spawn in; its
/// `spawn` runs as `spawn` does all the same.
pub(super) fn task<'a>(m: &mut Machine<'a>, n: &Native<'_>, values: &mut [Value<'a>]) -> R<'a> {
    match (n.owner, n.name) {
        (None, "threads" | "sequential") => Ok(Value::Handler(Arc::new(HandlerValue {
            effect: prelude("async"),
            control: false,
            ops: Vec::new(),
        }))),
        (None | Some("Scope"), "spawn") => {
            let f = arg(values, values.len().saturating_sub(1));
            let v = m.apply_value(&f, &mut Vec::new())?;
            Ok(Value::variant(task_item("Task"), vec![v]))
        }
        (Some("Task"), "await") => match arg(values, 0) {
            Value::Variant(x) => Ok(x.1.first().cloned().unwrap_or_else(Value::unit)),
            _ => unreachable!("a task's handle holds its value"),
        },
        _ => unreachable!("the table names every native of `std.task`: {}", n.name),
    }
}

/// par.fold-tree: a list of `n` elements combines its first `n / 2` elements folded with the
/// rest folded, so that the tree depends on `n` alone; one element is itself.
fn tree<'a>(m: &mut Machine<'a>, f: &Value<'a>, xs: &[Value<'a>]) -> R<'a> {
    match xs {
        [] => unreachable!("a fold's tree has an element"),
        [x] => Ok(x.clone()),
        _ => {
            let (left, right) = xs.split_at(xs.len() / 2);
            let a = tree(m, f, left)?;
            let b = tree(m, f, right)?;
            m.apply_value(f, &mut vec![a, b])
        }
    }
}

/// par.sequential-meaning, par.panics and par.writes-in-place: `map` and `each` call `f` on the
/// elements from the first to the last, `each` writing each element in place, and `both` calls `f`,
/// then `g`.
pub(super) fn par<'a>(m: &mut Machine<'a>, n: &Native<'_>, values: &mut [Value<'a>]) -> R<'a> {
    match n.name {
        "map" => {
            let f = arg(values, 1);
            let mut out = Vec::with_capacity(values[0].as_list().len());
            for x in values[0].as_list().to_vec() {
                out.push(m.apply_value(&f, &mut vec![x])?);
            }
            Ok(Value::list(out))
        }
        "each" => {
            let f = arg(values, 1);
            let mut out = Vec::with_capacity(values[0].as_list().len());
            for x in values[0].as_list().to_vec() {
                let mut cell = vec![x];
                m.apply_value(&f, &mut cell)?;
                out.push(cell.pop().unwrap_or_else(Value::unit));
            }
            values[0] = Value::list(out);
            Ok(Value::unit())
        }
        "both" => {
            let (first, second) = (arg(values, 0), arg(values, 1));
            let left = m.apply_value(&first, &mut Vec::new())?;
            let right = m.apply_value(&second, &mut Vec::new())?;
            Ok(Value::tuple(vec![left, right]))
        }
        "fold" => {
            let xs = values[0].as_list().to_vec();
            if xs.is_empty() {
                return Ok(arg(values, 1));
            }
            tree(m, &arg(values, 2), &xs)
        }
        _ => unreachable!("the table names every function of `std.par`: {}", n.name),
    }
}

/// The size that an array type's arguments give, the second of `targs`: the impl's for a
/// method, and the function's own for `fill` and `from_list`.
fn size(targs: &[Ty]) -> i128 {
    match targs.get(1) {
        Some(Ty::Value(hir::Value::Int(n))) => *n,
        other => unreachable!("an array's size is a value when its code runs: {other:?}"),
    }
}

/// `std.array`: an array is held as a list of exactly its size, whose value semantics are an
/// array's (generics.array-elements).
pub(super) fn array<'a>(m: &mut Machine<'a>, n: &Native<'_>, values: &mut [Value<'a>]) -> R<'a> {
    match n.name {
        "fill" => {
            let n = size(n.targs);
            let Ok(count) = usize::try_from(n) else {
                return panic(
                    "bounds",
                    format!("an array's size is never negative, and this one is {n}"),
                );
            };
            reserve(count.saturating_mul(8))?;
            Ok(Value::list(vec![arg(values, 0); count]))
        }
        "from_list" => {
            let fits = i128::try_from(values[0].as_list().len()).is_ok_and(|l| l == size(n.targs));
            Ok(Value::option(fits.then(|| arg(values, 0))))
        }
        "map" => {
            let f = arg(values, 1);
            let mut out = Vec::with_capacity(values[0].as_list().len());
            for x in values[0].as_list().to_vec() {
                out.push(m.apply_value(&f, &mut vec![x])?);
            }
            Ok(Value::list(out))
        }
        _ => unreachable!("the table names every native of `std.array`: {}", n.name),
    }
}
