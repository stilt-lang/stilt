//! Spreads of packs (variadics.spread-expressions): `..e` among a tuple's or a list's elements or a
//! call's arguments stands for the values of its body, evaluated once for each element of its pack,
//! with each pack tuple it maps standing for that element, and the pack's element type for its
//! type.

use stilt_types::tast::{Arg, Expr, ExprKind, SpreadExpr};
use stilt_types::ty::Ty;

use super::{Flow, Frame, Machine, substituted};
use crate::value::Value;

impl<'a> Machine<'a> {
    /// The values of elements, each spread's in its place.
    pub(crate) fn elements(
        &mut self,
        fr: &mut Frame<'a>,
        es: &'a [Expr],
    ) -> Result<Vec<Value<'a>>, Flow<'a>> {
        let mut values = Vec::with_capacity(es.len());
        for e in es {
            match &e.kind {
                ExprKind::Spread(s) => values.extend(self.spread_pack(fr, s)?),
                _ => values.push(self.expr(fr, e)?),
            }
        }
        Ok(values)
    }

    /// The values of arguments that are passed by value, each spread's in its place.
    pub(crate) fn values_of(
        &mut self,
        fr: &mut Frame<'a>,
        args: &'a [Arg],
    ) -> Result<Vec<Value<'a>>, Flow<'a>> {
        let mut values = Vec::with_capacity(args.len());
        for a in args {
            match &a.value.kind {
                ExprKind::Spread(s) => values.extend(self.spread_pack(fr, s)?),
                _ => values.push(self.expr(fr, &a.value)?),
            }
        }
        Ok(values)
    }

    /// The values of a spread: its body's, once for each element of its pack, with the pack
    /// tuples it maps holding their elements and the pack its element's type meanwhile.
    fn spread_pack(
        &mut self,
        fr: &mut Frame<'a>,
        s: &'a SpreadExpr,
    ) -> Result<Vec<Value<'a>>, Flow<'a>> {
        let Ty::Tuple(element_types) = substituted(&fr.info.tenv, &s.pack) else {
            unreachable!("a spread's pack is a tuple of types when the body runs")
        };
        let wholes: Vec<Value<'a>> = s
            .mapped
            .iter()
            .map(|id| fr.get(*id).unwrap_or_else(Value::unit))
            .collect();
        let info = std::sync::Arc::clone(&fr.info);
        let mut values = Vec::with_capacity(element_types.len());
        let mut result = Ok(());
        for (i, ty) in element_types.into_iter().enumerate() {
            for (id, whole) in s.mapped.iter().zip(&wholes) {
                let Value::Tuple(xs) = whole else {
                    unreachable!("a spread maps pack tuples")
                };
                fr.set(*id, xs.get().get(i).cloned().unwrap_or_else(Value::unit));
            }
            fr.info = std::sync::Arc::clone(&info);
            fr.bind_types(vec![(s.of.clone(), ty)]);
            match self.expr(fr, &s.body) {
                Ok(v) => values.push(v),
                Err(flow) => {
                    result = Err(flow);
                    break;
                }
            }
        }
        fr.info = info;
        for (id, whole) in s.mapped.iter().zip(wholes) {
            fr.set(*id, whole);
        }
        result.map(|()| values)
    }
}
