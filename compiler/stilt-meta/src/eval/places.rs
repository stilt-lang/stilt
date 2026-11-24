//! Places (expressions.places and expressions.mutable-places; values.inout-arguments): a variable,
//! a field of a place, an element of a list or a map's entry, read, written by an assignment, and
//! lent to an `inout` parameter, which takes the place's value and writes it back.

use std::sync::Arc;

use stilt_hir::hir::BinaryOp;
use stilt_types::tast::{Expr, ExprKind};

use super::{Flow, Frame, Machine, R, ops, panic};
use crate::value::Value;

/// What is done to a place's value.
pub(crate) type Visit<'v, 'a> =
    dyn FnMut(&mut Machine<'a>, &mut Value<'a>) -> Result<(), Flow<'a>> + 'v;

impl<'a> Machine<'a> {
    /// Applies `visit` to the value at the place `place`: a place rooted in a local, in a
    /// projection's call, or a value of its own.
    pub(crate) fn with_place(
        &mut self,
        fr: &mut Frame<'a>,
        place: &'a Expr,
        visit: &mut Visit<'_, 'a>,
    ) -> Result<(), Flow<'a>> {
        if super::args::projected(place) {
            let mut prepared = self.prepare(fr, place, Vec::new())?;
            let result = self.open_prepared(&mut prepared, visit);
            self.written_back(prepared.into_args())?;
            return result;
        }
        if let Some(at) = self.resolve(fr, place)? {
            return self.at_place(&at, visit);
        }
        let mut value = self.expr(fr, place)?;
        visit(self, &mut value)
    }

    /// Applies `f` to element `key` of a list, or to a map's entry for `key`, which it adds
    /// with the map's default when the map has none.
    pub(crate) fn element(
        &mut self,
        b: &mut Value<'a>,
        key: &Value<'a>,
        f: &mut Visit<'_, 'a>,
    ) -> Result<(), Flow<'a>> {
        match b {
            Value::List(xs) => {
                let i = key.as_int();
                let len = xs.get().len();
                let Some(i) = usize::try_from(i).ok().filter(|&i| i < len) else {
                    return panic(
                        "bounds",
                        format!("index {i} is out of bounds for a list of length {len}"),
                    );
                };
                let mut slot = xs.get()[i].clone();
                let r = f(self, &mut slot);
                Arc::make_mut(xs).update(|v| v[i] = slot);
                r
            }
            Value::Map(map) => {
                let found = self.find_key(map.entries.get(), key)?;
                let map = Arc::make_mut(map);
                let mut slot = match (found, &map.default) {
                    (Some(i), _) => map.entries.get()[i].1.clone(),
                    (None, Some(d)) => d.clone(),
                    (None, None) => {
                        return panic(
                            "missing-key",
                            "the key isn't in the map, which has no default",
                        );
                    }
                };
                let r = f(self, &mut slot);
                map.entries.update(|entries| match found {
                    Some(i) => entries[i].1 = slot,
                    None => entries.push((key.clone(), slot)),
                });
                r
            }
            Value::Window(w) => {
                let w = Arc::clone(w);
                self.window_at(&w, key, f)
            }
            _ => unreachable!("an index reaches into a list, a map or a view, as checking found"),
        }
    }

    /// The index of the entry whose key equals `key`.
    pub(crate) fn find_key(
        &mut self,
        entries: &[(Value<'a>, Value<'a>)],
        key: &Value<'a>,
    ) -> Result<Option<usize>, Flow<'a>> {
        for (i, (k, _)) in entries.iter().enumerate() {
            if self.equal(k, key)? {
                return Ok(Some(i));
            }
        }
        Ok(None)
    }

    /// `place = value`, and `place op= value`.
    pub(super) fn assign(
        &mut self,
        fr: &mut Frame<'a>,
        op: Option<BinaryOp>,
        place: &'a Expr,
        value: &'a Expr,
    ) -> Result<(), Flow<'a>> {
        let x = self.expr(fr, value)?;
        if op.is_none()
            && let ExprKind::Index(map, key) = &place.kind
            && map.ty.is_prelude("Map")
        {
            return self.store(fr, map, key, x);
        }
        let mut x = Some(x);
        self.with_place(fr, place, &mut |_, v| {
            let Some(x) = x.take() else { return Ok(()) };
            *v = match op {
                Some(op) => ops::arithmetic(op, v, &x)?,
                None => x,
            };
            Ok(())
        })
    }

    /// `m[k] = x`, which gives the map's entry for `k` the value `x`, adding it when the map has
    /// none, and reads no entry (std.maps).
    fn store(
        &mut self,
        fr: &mut Frame<'a>,
        map: &'a Expr,
        key: &'a Expr,
        x: Value<'a>,
    ) -> Result<(), Flow<'a>> {
        let key = self.expr(fr, key)?;
        let mut entry = Some((key, x));
        self.with_place(fr, map, &mut |m, v| {
            let (Value::Map(map), Some((key, x))) = (v, entry.take()) else {
                unreachable!("a store into a map's entry reaches a map, as checking found")
            };
            let found = m.find_key(map.entries.get(), &key)?;
            Arc::make_mut(map).entries.update(|entries| match found {
                Some(i) => entries[i].1 = x,
                None => entries.push((key, x)),
            });
            Ok(())
        })
    }

    /// `xs[i]` and `m[k]`.
    pub(super) fn index(&mut self, fr: &mut Frame<'a>, base: &'a Expr, i: &'a Expr) -> R<'a> {
        let b = self.expr(fr, base)?;
        let key = self.expr(fr, i)?;
        match &b {
            Value::List(xs) => {
                let i = key.as_int();
                let len = xs.get().len();
                match usize::try_from(i).ok().and_then(|i| xs.get().get(i)) {
                    Some(v) => Ok(v.clone()),
                    None => panic(
                        "bounds",
                        format!("index {i} is out of bounds for a list of length {len}"),
                    ),
                }
            }
            Value::Map(m) => match self.find_key(m.entries.get(), &key)? {
                Some(i) => Ok(m.entries.get()[i].1.clone()),
                None => match &m.default {
                    Some(d) => Ok(d.clone()),
                    None => panic(
                        "missing-key",
                        "the key isn't in the map, which has no default",
                    ),
                },
            },
            Value::Window(w) => self.window_read(w, &key),
            _ => unreachable!("an index reads a list, a map or a view, as its checking found"),
        }
    }
}
