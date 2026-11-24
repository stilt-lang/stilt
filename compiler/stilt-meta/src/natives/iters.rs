//! Iterators (views.making-iterator, views.adapters, views.laziness and views.consumers): an
//! iterator is a description of its source and its adapters, which a consumer turns into a cursor
//! each time it reads it, so that nothing runs before a consumer asks and every consumer starts
//! from the first element (views.laziness).

use std::cmp::Ordering;
use std::sync::Arc;

use super::Native;
use crate::eval::{Flow, Machine, R, panic};
use crate::value::{IterValue, Value};

/// A reading of an iterator, which asks for one element at a time, calling the closures of its
/// adapters on each element as it reaches them (views.laziness).
#[derive(Debug)]
pub(crate) enum Cursor<'a> {
    Elements(std::vec::IntoIter<Value<'a>>),
    Range(i128, i128),
    Mapped(Box<Cursor<'a>>, Value<'a>),
    Filtered(Box<Cursor<'a>>, Value<'a>),
    /// How many elements it may still give.
    Taken(Box<Cursor<'a>>, i128),
    /// How many it drops when it is first asked.
    Skipped(Box<Cursor<'a>>, Option<i128>),
    /// Whether an element was rejected.
    TakenWhile(Box<Cursor<'a>>, Value<'a>, bool),
    /// Whether it still drops.
    SkippedWhile(Box<Cursor<'a>>, Value<'a>, bool),
    Enumerated(Box<Cursor<'a>>, i128),
    Zipped(Box<Cursor<'a>>, Box<Cursor<'a>>),
    /// Whether the first has ended.
    Chained(Box<Cursor<'a>>, Box<Cursor<'a>>, bool),
}

/// Whether a function value accepts `x`.
fn holds<'a>(m: &mut Machine<'a>, f: &Value<'a>, x: &Value<'a>) -> Result<bool, Flow<'a>> {
    Ok(m.apply_value(f, &mut vec![x.clone()])?.as_bool())
}

impl<'a> Cursor<'a> {
    /// A cursor at the first element of `it`.
    pub(crate) fn new(it: &IterValue<'a>) -> Self {
        let inner = |it: &Arc<IterValue<'a>>| Box::new(Cursor::new(it));
        match it {
            IterValue::Elements(xs) => Cursor::Elements(xs.clone().into_iter()),
            IterValue::Range(a, b) => Cursor::Range(*a, *b),
            IterValue::Mapped(it, f) => Cursor::Mapped(inner(it), f.clone()),
            IterValue::Filtered(it, f) => Cursor::Filtered(inner(it), f.clone()),
            IterValue::Taken(it, n) => Cursor::Taken(inner(it), *n),
            IterValue::Skipped(it, n) => Cursor::Skipped(inner(it), Some(*n)),
            IterValue::TakenWhile(it, f) => Cursor::TakenWhile(inner(it), f.clone(), false),
            IterValue::SkippedWhile(it, f) => Cursor::SkippedWhile(inner(it), f.clone(), true),
            IterValue::Enumerated(it, start) => Cursor::Enumerated(inner(it), *start),
            IterValue::Zipped(a, b) => Cursor::Zipped(inner(a), inner(b)),
            IterValue::Chained(a, b) => Cursor::Chained(inner(a), inner(b), false),
        }
    }

    /// The next element, if there is one.
    pub(crate) fn next(&mut self, m: &mut Machine<'a>) -> Result<Option<Value<'a>>, Flow<'a>> {
        Ok(match self {
            Cursor::Elements(xs) => xs.next(),
            Cursor::Range(i, last) => (*i < *last).then(|| {
                *i += 1;
                Value::i64(*i - 1)
            }),
            Cursor::Mapped(inner, f) => match inner.next(m)? {
                Some(x) => Some(m.apply_value(f, &mut vec![x])?),
                None => None,
            },
            Cursor::Filtered(inner, keep) => loop {
                match inner.next(m)? {
                    Some(x) if !holds(m, keep, &x)? => {}
                    found => break found,
                }
            },
            Cursor::Taken(inner, left) => {
                if *left <= 0 {
                    return Ok(None);
                }
                let found = inner.next(m)?;
                *left = if found.is_some() { *left - 1 } else { 0 };
                found
            }
            Cursor::Skipped(inner, pending) => {
                for _ in 0..pending.take().unwrap_or(0).max(0) {
                    if inner.next(m)?.is_none() {
                        return Ok(None);
                    }
                }
                inner.next(m)?
            }
            Cursor::TakenWhile(inner, keep, over) => {
                if *over {
                    return Ok(None);
                }
                match inner.next(m)? {
                    Some(x) if holds(m, keep, &x)? => Some(x),
                    _ => {
                        *over = true;
                        None
                    }
                }
            }
            Cursor::SkippedWhile(inner, drop, skipping) => loop {
                match inner.next(m)? {
                    Some(x) if *skipping && holds(m, drop, &x)? => {}
                    found => {
                        *skipping = false;
                        break found;
                    }
                }
            },
            _ => return self.next_pair(m),
        })
    }

    /// The next element of the adapters that pair: `enumerate`, `zip` and `chain`.
    fn next_pair(&mut self, m: &mut Machine<'a>) -> Result<Option<Value<'a>>, Flow<'a>> {
        let pair = |a, b| Value::tuple(vec![a, b]);
        Ok(match self {
            Cursor::Enumerated(inner, i) => match inner.next(m)? {
                Some(x) => {
                    let index = *i;
                    // An index past `i64`'s range overflows, as `List.enumerate`'s does.
                    if index >= i128::from(i64::MAX) {
                        return panic("overflow", "the result doesn't fit in `i64`");
                    }
                    *i += 1;
                    Some(pair(Value::i64(index), x))
                }
                None => None,
            },
            // `zip` asks `self` and then `other` for each pair, and ends with the first that
            // ends; `chain` asks `other` once `self` ends (views.laziness).
            Cursor::Zipped(a, b) => match a.next(m)? {
                Some(x) => b.next(m)?.map(|y| pair(x, y)),
                None => None,
            },
            Cursor::Chained(a, b, second) => {
                if !*second {
                    if let Some(x) = a.next(m)? {
                        return Ok(Some(x));
                    }
                    *second = true;
                }
                b.next(m)?
            }
            _ => unreachable!("every other cursor is read by `next`"),
        })
    }
}

/// The natives of `impl<T> Iter<T>`: the makers of views.making-iterator that take a list, the
/// adapters of views.adapters, which run nothing, and the consumers of views.consumers.
pub(super) fn iter<'a>(m: &mut Machine<'a>, n: &Native<'_>, values: &mut [Value<'a>]) -> R<'a> {
    let it = |values: &[Value<'a>]| match values.first() {
        Some(Value::Iter(it)) => Arc::clone(it),
        _ => unreachable!("an adapter's receiver is an iterator"),
    };
    let arg = |i: usize| values.get(i).cloned().unwrap_or_else(Value::unit);
    let adapted = match n.name {
        "of" | "of_view" => IterValue::Elements(values[0].as_list().to_vec()),
        "map" => IterValue::Mapped(it(values), arg(1)),
        "filter" => IterValue::Filtered(it(values), arg(1)),
        "take" => IterValue::Taken(it(values), arg(1).as_int()),
        "skip" => IterValue::Skipped(it(values), arg(1).as_int()),
        "take_while" => IterValue::TakenWhile(it(values), arg(1)),
        "skip_while" => IterValue::SkippedWhile(it(values), arg(1)),
        "enumerate" => IterValue::Enumerated(it(values), arg(1).as_int()),
        "zip" | "chain" => {
            let Value::Iter(other) = arg(1) else {
                unreachable!("`zip` and `chain` take an iterator")
            };
            if n.name == "zip" {
                IterValue::Zipped(it(values), other)
            } else {
                IterValue::Chained(it(values), other)
            }
        }
        _ => return consume(m, n.name, &it(values), values),
    };
    Ok(Value::Iter(Arc::new(adapted)))
}

/// Every element, in order.
fn until_end<'a>(m: &mut Machine<'a>, cursor: &mut Cursor<'a>) -> Result<Vec<Value<'a>>, Flow<'a>> {
    let mut seen = Vec::new();
    while let Some(x) = cursor.next(m)? {
        crate::eval::reserve((seen.len() + 1) * std::mem::size_of::<Value<'_>>())?;
        seen.push(x);
    }
    Ok(seen)
}

/// `any`, `all` and `find`, which read elements until one decides.
fn tested<'a>(m: &mut Machine<'a>, name: &str, cursor: &mut Cursor<'a>, f: &Value<'a>) -> R<'a> {
    while let Some(x) = cursor.next(m)? {
        let accepted = holds(m, f, &x)?;
        match name {
            "any" if accepted => return Ok(Value::Bool(true)),
            "all" if !accepted => return Ok(Value::Bool(false)),
            "find" if accepted => return Ok(Value::option(Some(x))),
            _ => {}
        }
    }
    Ok(match name {
        "any" => Value::Bool(false),
        "all" => Value::Bool(true),
        _ => Value::option(None),
    })
}

/// The consumers of views.consumers, each of which reads the elements it needs, in order, and calls
/// its callback as it reads them.
fn consume<'a>(m: &mut Machine<'a>, name: &str, it: &IterValue<'a>, values: &[Value<'a>]) -> R<'a> {
    let mut cursor = Cursor::new(it);
    let f = values.get(1).cloned().unwrap_or_else(Value::unit);
    match name {
        "collect" => Ok(Value::list(until_end(m, &mut cursor)?)),
        "count" => Ok(Value::i64(
            i128::try_from(until_end(m, &mut cursor)?.len()).unwrap_or(0),
        )),
        "last" => Ok(Value::option(until_end(m, &mut cursor)?.pop())),
        "first" => Ok(Value::option(cursor.next(m)?)),
        "fold" => {
            let mut acc = f;
            let g = values.get(2).cloned().unwrap_or_else(Value::unit);
            while let Some(x) = cursor.next(m)? {
                acc = m.apply_value(&g, &mut vec![acc, x])?;
            }
            Ok(acc)
        }
        "any" | "all" | "find" => tested(m, name, &mut cursor, &f),
        "nth" => {
            let n = f.as_int();
            if n < 0 {
                return Ok(Value::option(None));
            }
            let mut i = 0;
            while let Some(x) = cursor.next(m)? {
                if i == n {
                    return Ok(Value::option(Some(x)));
                }
                i += 1;
            }
            Ok(Value::option(None))
        }
        "max" | "min" => {
            // The greatest or the least, the first of equal ones.
            let better = if name == "max" {
                Ordering::Greater
            } else {
                Ordering::Less
            };
            let mut best: Option<Value<'a>> = None;
            while let Some(x) = cursor.next(m)? {
                let replaces = match &best {
                    Some(b) => m.order(&x, b)? == better,
                    None => true,
                };
                if replaces {
                    best = Some(x);
                }
            }
            Ok(Value::option(best))
        }
        _ => unreachable!("the table names every native of `Iter`: {name}"),
    }
}
