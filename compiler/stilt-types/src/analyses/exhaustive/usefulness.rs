//! Maranget's usefulness over vectors of patterns, with the witness it finds (patterns.algorithm).

use std::borrow::Cow;

use stilt_hir::decls::Lookup;

use super::ctors::{all_ctors, arity, field_types, is_error, is_list};
use super::{Ctor, Pat, wilds};
use crate::ty::Ty;

/// A row of the matrix: one pattern per column.
type Row = Vec<Pat>;

/// `head` followed by `rest`.
fn cons<T: Clone>(head: T, rest: &[T]) -> Vec<T> {
    let mut v = Vec::with_capacity(rest.len() + 1);
    v.push(head);
    v.extend_from_slice(rest);
    v
}

/// Rows whose first pattern is an or-pattern, split into one row per alternative. Rows without
/// one, as most are, are borrowed: a `match` of many arms checks each against those before it,
/// which copying them would make slow (goal bounded-checking).
fn expand(rows: &[Row]) -> Cow<'_, [Row]> {
    if !rows
        .iter()
        .any(|row| matches!(row.first(), Some(Pat::Or(_))))
    {
        return Cow::Borrowed(rows);
    }
    let split = rows.iter().flat_map(|row| match row.split_first() {
        Some((Pat::Or(alts), rest)) => {
            let split: Vec<Row> = alts.iter().map(|p| cons(p.clone(), rest)).collect();
            expand(&split).into_owned()
        }
        _ => vec![row.clone()],
    });
    Cow::Owned(split.collect())
}

/// The rows that a value built with `ctor`, of arity `n`, can match, with the constructor's
/// fields in place of the first column.
fn specialize(ctor: &Ctor, n: usize, rows: &[Row]) -> Vec<Row> {
    rows.iter()
        .filter_map(|row| match row.split_first() {
            Some((Pat::Ctor(c, ps), rest)) => (c == ctor).then(|| [ps.as_slice(), rest].concat()),
            Some((Pat::Prefix(ps), rest)) => {
                (n >= ps.len()).then(|| [ps.as_slice(), &wilds(n - ps.len()), rest].concat())
            }
            Some((Pat::Wild, rest)) => Some([wilds(n).as_slice(), rest].concat()),
            Some((Pat::Or(_), _)) | None => {
                unreachable!("the rows are expanded, and as wide as their types")
            }
        })
        .collect()
}

/// The rows whose first pattern matches any value, without it.
fn default(rows: &[Row]) -> Vec<Row> {
    rows.iter()
        .filter_map(|row| match row.split_first() {
            Some((Pat::Wild, rest)) => Some(rest.to_vec()),
            _ => None,
        })
        .collect()
}

/// The constructors at the heads of the rows.
fn heads(rows: &[Row]) -> Vec<&Ctor> {
    rows.iter()
        .filter_map(|row| match row.first() {
            Some(Pat::Ctor(c, _)) => Some(c),
            _ => None,
        })
        .collect()
}

/// The list lengths that tell the patterns of a column apart: each length below `n` on its
/// own, then every length from `n` on together.
fn list_cases(rows: &[Row], q: &Pat) -> Vec<Ctor> {
    let longest = std::iter::once(q)
        .chain(rows.iter().filter_map(|row| row.first()))
        .fold(0, |m, p| match p {
            Pat::Ctor(Ctor::Len(k), _) => m.max(k + 1),
            Pat::Prefix(ps) => m.max(ps.len()),
            _ => m,
        });
    (0..longest)
        .map(Ctor::Len)
        .chain([Ctor::AtLeast(longest)])
        .collect()
}

/// Whether `head`, the pattern of a list column, covers `case`, one of [`list_cases`].
fn covers(head: &Pat, case: &Ctor) -> bool {
    match case {
        Ctor::Len(k) => match head {
            Pat::Ctor(Ctor::Len(n), _) => n == k,
            Pat::Prefix(ps) => *k >= ps.len(),
            _ => true,
        },
        Ctor::AtLeast(_) => !matches!(head, Pat::Ctor(Ctor::Len(_), _)),
        _ => false,
    }
}

/// The pattern for the values of `ty` that the constructors `seen` at the heads of the rows
/// miss: a missing constructor, if `ty` has constructors and the rows name some.
fn missing(decls: &dyn Lookup, ty: &Ty, ctors: Option<&[Ctor]>, seen: &[&Ctor]) -> Pat {
    match ctors {
        Some(ctors) if !seen.is_empty() => ctors
            .iter()
            .find(|c| !seen.contains(c))
            .map_or(Pat::Wild, |c| {
                Pat::Ctor(c.clone(), wilds(arity(decls, ty, c)))
            }),
        _ => Pat::Wild,
    }
}

/// Whether `q` is useful with respect to `rows`, all of types `tys`. If it is, the result is a
/// value vector, as patterns, that `q` matches and no row does. A column of the error type
/// matches anything, and tells nothing apart (errors.error-type).
pub(super) fn useful(decls: &dyn Lookup, tys: &[Ty], rows: &[Row], q: &[Pat]) -> Option<Vec<Pat>> {
    let rows = expand(rows);
    if rows.iter().any(|row| row.iter().all(|p| *p == Pat::Wild)) {
        return None;
    }
    let n = wild_columns(decls, tys, &rows, q);
    if n > 0 {
        let rows: Vec<Row> = rows.iter().map(|row| row[n..].to_vec()).collect();
        return useful(decls, &tys[n..], &rows, &q[n..]).map(|w| [wilds(n), w].concat());
    }
    match (tys.split_first(), q.split_first()) {
        (None, None) => Some(Vec::new()),
        (Some((ty, tys)), Some((_, rest))) if is_error(ty) => {
            let rows: Vec<Row> = rows.iter().map(|row| row[1..].to_vec()).collect();
            useful(decls, tys, &rows, rest).map(|w| cons(Pat::Wild, &w))
        }
        (Some((ty, tys)), Some((head, rest))) => Column {
            decls,
            ty,
            tys,
            rows: &rows,
            head,
            rest,
        }
        .useful(),
        _ => unreachable!("a vector is as wide as its types"),
    }
}

/// The number of leading columns where `q` and every row hold `_`, each of a type that has
/// values and isn't a list, whose witness names a length. [`useful`] would drop each with `_`
/// in its witness, as a column of the error type, or as a wildcard against rows that name no
/// constructor; it drops them at once, since one call for each would nest as deep as an array
/// is long (generics.array-patterns).
fn wild_columns(decls: &dyn Lookup, tys: &[Ty], rows: &[Row], q: &[Pat]) -> usize {
    tys.iter()
        .zip(q)
        .enumerate()
        .take_while(|(i, (ty, p))| {
            **p == Pat::Wild
                && rows.iter().all(|row| row[*i] == Pat::Wild)
                && (is_error(ty)
                    || !is_list(ty) && all_ctors(decls, ty).is_none_or(|ctors| !ctors.is_empty()))
        })
        .count()
}

/// A step of [`useful`] on the first column: its type and the other columns' types, the
/// expanded rows, and the vector's first pattern and the others.
struct Column<'a> {
    decls: &'a dyn Lookup,
    ty: &'a Ty,
    tys: &'a [Ty],
    rows: &'a [Row],
    head: &'a Pat,
    rest: &'a [Pat],
}

impl Column<'_> {
    /// [`useful`], split on the first column's pattern.
    fn useful(&self) -> Option<Vec<Pat>> {
        match self.head {
            Pat::Or(alts) => {
                let tys = cons(self.ty.clone(), self.tys);
                alts.iter().find_map(|alt| {
                    useful(self.decls, &tys, self.rows, &cons(alt.clone(), self.rest))
                })
            }
            _ if is_list(self.ty) => list_cases(self.rows, self.head)
                .iter()
                .filter(|case| covers(self.head, case))
                .find_map(|case| self.with_ctor(case)),
            Pat::Ctor(ctor, _) => self.with_ctor(ctor),
            Pat::Prefix(_) => None,
            Pat::Wild => self.useful_wild(),
        }
    }

    /// [`useful`] for a wildcard: on each constructor of the type when the rows name every one,
    /// else on the rows that match any value, with a constructor they miss in the witness.
    fn useful_wild(&self) -> Option<Vec<Pat>> {
        let seen = heads(self.rows);
        match all_ctors(self.decls, self.ty) {
            Some(ctors) if ctors.iter().all(|c| seen.contains(&c)) => {
                ctors.iter().find_map(|c| self.with_ctor(c))
            }
            ctors => {
                let w = useful(self.decls, self.tys, &default(self.rows), self.rest)?;
                Some(cons(
                    missing(self.decls, self.ty, ctors.as_deref(), &seen),
                    &w,
                ))
            }
        }
    }

    /// [`useful`] for the values built with `ctor`, with the witness built back up.
    fn with_ctor(&self, ctor: &Ctor) -> Option<Vec<Pat>> {
        let fields = field_types(self.decls, self.ty, ctor);
        let n = fields.len();
        let q = match self.head {
            Pat::Ctor(_, ps) => [ps.as_slice(), self.rest].concat(),
            // `covers` keeps only the lengths that the prefix fits in.
            Pat::Prefix(ps) => [ps.as_slice(), &wilds(n - ps.len()), self.rest].concat(),
            Pat::Wild | Pat::Or(_) => [wilds(n).as_slice(), self.rest].concat(),
        };
        let tys = [fields.as_slice(), self.tys].concat();
        let mut w = useful(self.decls, &tys, &specialize(ctor, n, self.rows), &q)?;
        let rest = w.split_off(n.min(w.len()));
        Some(cons(Pat::Ctor(ctor.clone(), w), &rest))
    }
}
