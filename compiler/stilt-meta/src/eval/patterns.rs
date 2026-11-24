//! Patterns (patterns.pattern-forms): whether a value matches, binding the pattern's variables when
//! it does.

use stilt_hir::hir::ListRest;
use stilt_types::tast::{Pat, PatKind};

use super::{Flow, Frame, Machine};
use crate::value::Value;

impl<'a> Machine<'a> {
    /// Whether `v` matches `p`, binding its variables in the frame.
    pub(crate) fn bind_pattern(
        &mut self,
        fr: &mut Frame<'a>,
        p: &'a Pat,
        v: Value<'a>,
    ) -> Result<bool, Flow<'a>> {
        Ok(match &p.kind {
            PatKind::Wild | PatKind::Error => true,
            PatKind::Bind(id) => {
                fr.set(*id, v);
                true
            }
            PatKind::Int(text) => match v {
                Value::Int(x, _) => parse_int(text) == Some(x),
                _ => false,
            },
            PatKind::Str(s) => v.as_str() == s,
            PatKind::Bool(b) => matches!(v, Value::Bool(x) if x == *b),
            PatKind::Tuple(ps) => match &v {
                Value::Tuple(xs) => self.all(fr, ps, xs)?,
                _ => false,
            },
            PatKind::Const(e) => {
                let c = self.expr(fr, e)?;
                self.equal(&v, &c)?
            }
            PatKind::Variant(item, ps) => match &v {
                Value::Variant(x) if x.0 == *item => {
                    // meta.fresh-types: a case of a shape binds its payload's fresh types.
                    if let [payload] = &ps[..]
                        && stilt_types::ty::is_shape_case(item)
                    {
                        self.bind_case(fr, &p.ty, &item.name, &payload.ty);
                    }
                    self.all(fr, ps, &x.1)?
                }
                _ => false,
            },
            PatKind::Record(fields) => {
                for (name, fp) in fields {
                    let Some(x) = v.field_named(*name).cloned() else {
                        return Ok(false);
                    };
                    if !self.bind_pattern(fr, fp, x)? {
                        return Ok(false);
                    }
                }
                true
            }
            PatKind::List(ps, rest) => self.list_pattern(fr, ps, *rest, &v)?,
            PatKind::Or(ps) => {
                for alt in ps {
                    if self.bind_pattern(fr, alt, v.clone())? {
                        return Ok(true);
                    }
                }
                false
            }
        })
    }

    fn all(
        &mut self,
        fr: &mut Frame<'a>,
        ps: &'a [Pat],
        xs: &[Value<'a>],
    ) -> Result<bool, Flow<'a>> {
        if ps.len() != xs.len() {
            return Ok(false);
        }
        for (p, x) in ps.iter().zip(xs) {
            if !self.bind_pattern(fr, p, x.clone())? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// `[p, q]`, `[p, ..]` and `[p, ..rest]`: the elements first, then the rest.
    fn list_pattern(
        &mut self,
        fr: &mut Frame<'a>,
        ps: &'a [Pat],
        rest: ListRest,
        v: &Value<'a>,
    ) -> Result<bool, Flow<'a>> {
        let xs = v.as_list();
        let fits = match rest {
            ListRest::Exact => xs.len() == ps.len(),
            ListRest::Rest | ListRest::Bind(_) => xs.len() >= ps.len(),
        };
        if !fits {
            return Ok(false);
        }
        let xs = xs.to_vec();
        for (p, x) in ps.iter().zip(&xs) {
            if !self.bind_pattern(fr, p, x.clone())? {
                return Ok(false);
            }
        }
        if let ListRest::Bind(id) = rest {
            fr.set(id, Value::list(xs[ps.len()..].to_vec()));
        }
        Ok(true)
    }
}

/// The value of an integer pattern's literal.
fn parse_int(text: &str) -> Option<i128> {
    let digits: String = text.chars().filter(|c| *c != '_').collect();
    let (negative, digits) = match digits.strip_prefix('-') {
        Some(d) => (true, d.trim().to_owned()),
        None => (false, digits),
    };
    let x = if let Some(h) = digits.strip_prefix("0x") {
        i128::from_str_radix(h, 16).ok()?
    } else if let Some(o) = digits.strip_prefix("0o") {
        i128::from_str_radix(o, 8).ok()?
    } else if let Some(b) = digits.strip_prefix("0b") {
        i128::from_str_radix(b, 2).ok()?
    } else {
        digits.parse().ok()?
    };
    Some(if negative { -x } else { x })
}
