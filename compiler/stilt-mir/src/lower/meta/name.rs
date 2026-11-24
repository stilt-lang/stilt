//! The name of a described type, as a diagnostic writes it (meta.shape-and-name): text, and the
//! names of the type parameters it holds, which their descriptors give where it is made.

use stilt_hir::hir::{GenericId, Name};
use stilt_types::ty::{Table, Ty};

use super::{DESC_LEN, NAME, number};
use crate::described::{Piece, number_of};
use crate::lower::Lower;
use crate::mir::{Const, Operand, Repr, Runtime, Rvalue};

/// What marks a type parameter's number in a name's text.
const MARK: char = '\u{1}';

/// The type parameters a type holds, in the order its name shows them.
fn params_in(ty: &Ty, out: &mut Vec<Ty>) {
    match ty {
        Ty::Param(_) => {
            if !out.contains(ty) {
                out.push(ty.clone());
            }
        }
        Ty::Con(_, ts) | Ty::Tuple(ts) => {
            for t in ts {
                params_in(t, out);
            }
        }
        Ty::App(head, ts) => {
            for t in std::iter::once(&**head).chain(ts) {
                params_in(t, out);
            }
        }
        Ty::Fn(f) => {
            let params = f.params.iter().map(|(_, t)| t);
            let row = f.row.raise.as_deref().into_iter();
            let effects = f.row.effects.iter().flat_map(|(_, ts)| ts);
            for t in params.chain([&f.ret]).chain(row).chain(effects) {
                params_in(t, out);
            }
        }
        Ty::Spread(s) => params_in(&s.elem, out),
        Ty::Handler(h) => {
            for t in h.args.iter().chain(&h.answer) {
                params_in(t, out);
            }
        }
        Ty::SelfTy | Ty::Value(_) | Ty::Var(_) | Ty::Error => {}
    }
}

/// The pieces of a name written with each numbered type parameter marked.
fn split(text: &str) -> Box<[Piece]> {
    text.split(MARK)
        .enumerate()
        .filter(|(_, s)| !s.is_empty())
        .map(|(i, s)| match s.parse::<u32>() {
            Ok(n) if i % 2 == 1 => Piece::Param(n),
            _ => Piece::Text(s.into()),
        })
        .collect()
}

fn marked(i: u32) -> Name {
    Name::from(format!("{MARK}{i}{MARK}").as_str())
}

impl Lower<'_> {
    /// The pieces of the name of a type of the code being lowered, its type parameters in scope
    /// numbered among `params`. A rigid type of a polymorphic function type it holds is named
    /// by the letter of its place, as it has no descriptor.
    pub(crate) fn pieces(&self, ty: &Ty, params: &mut Vec<Ty>) -> Box<[Piece]> {
        let mut found = Vec::new();
        params_in(ty, &mut found);
        let numbers: Vec<(GenericId, u32)> = found
            .iter()
            .filter(|t| self.generic(t).is_some())
            .filter_map(|t| match t {
                Ty::Param(g) => Some((g.clone(), number(params, t))),
                _ => None,
            })
            .collect();
        let names = |g: &GenericId| match numbers.iter().find(|(h, _)| h == g) {
            Some((_, i)) => marked(*i),
            None => Name::from(g.fresh_letter().unwrap_or('T').to_string().as_str()),
        };
        split(&Table::default().show(ty, &names))
    }

    /// The pieces of the name of the type that the code of a descriptor describes, whose type
    /// parameters are numbered.
    pub(crate) fn numbered_pieces(ty: &Ty) -> Box<[Piece]> {
        let names = |g: &GenericId| match number_of(g) {
            Some(i) => marked(i),
            None => Name::from("T"),
        };
        split(&Table::default().show(ty, &names))
    }

    /// A name from its pieces: a constant, or the text of each piece joined, the name of a
    /// type parameter read from its descriptor.
    pub(crate) fn type_name(&mut self, pieces: &[Piece]) -> Operand {
        self.joined(pieces, None, NAME)
    }

    /// Text from its pieces: a constant, or each piece joined, a type parameter's read from
    /// field `field` of its descriptor: the type that `params` holds at its number, or else
    /// the numbered type parameter of a descriptor's code.
    pub(crate) fn joined(
        &mut self,
        pieces: &[Piece],
        params: Option<&[Ty]>,
        field: u32,
    ) -> Operand {
        if pieces.iter().all(|p| matches!(p, Piece::Text(_))) {
            let text: String = pieces
                .iter()
                .map(|p| match p {
                    Piece::Text(t) => &**t,
                    Piece::Param(_) => "",
                })
                .collect();
            return Operand::Const(Const::Str(text.as_str().into()));
        }
        let parts: Vec<Vec<Operand>> = pieces
            .iter()
            .map(|p| match p {
                Piece::Text(t) => vec![Operand::Const(Const::Str(t.as_ref().into()))],
                Piece::Param(i) => {
                    let ty = params
                        .and_then(|ps| ps.get(*i as usize).cloned())
                        .unwrap_or_else(|| Self::numbered_ty(*i));
                    let d = self.descriptor(&ty);
                    vec![self.read(d, DESC_LEN, field, Repr::Heap)]
                }
            })
            .collect();
        let list = self.list_literal(parts, &Ty::list(Ty::str()));
        self.b
            .define_op(Repr::Heap, Rvalue::Runtime(Runtime::Concat, vec![list]))
    }

    /// The pieces of the identities of types of the code being lowered, joined by `;`, their
    /// type parameters in scope numbered among `params`.
    pub(crate) fn ident_pieces(&self, tys: &[Ty], params: &mut Vec<Ty>) -> Box<[Piece]> {
        let mut text = String::new();
        for (k, ty) in tys.iter().enumerate() {
            if k > 0 {
                text.push(';');
            }
            let mut mark = |t: &Ty| (self.generic(t).is_some()).then(|| number(params, t));
            ident_text(ty, &mut mark, &mut text);
        }
        split(&text)
    }

    /// The pieces of the identities of types of a descriptor's code, joined by `;`, whose type
    /// parameters are numbered.
    pub(crate) fn numbered_ident(tys: &[Ty]) -> Box<[Piece]> {
        let mut text = String::new();
        for (k, ty) in tys.iter().enumerate() {
            if k > 0 {
                text.push(';');
            }
            let mut mark = |t: &Ty| match t {
                Ty::Param(g) => number_of(g),
                _ => None,
            };
            ident_text(ty, &mut mark, &mut text);
        }
        split(&text)
    }

    /// Field `index` of a data object of `len` fields, a copy of its own, which borrow
    /// inference may make a borrow (`stilt-rc`).
    pub(crate) fn read(&mut self, base: Operand, len: u32, index: u32, repr: Repr) -> Operand {
        self.b.define_op(
            repr,
            Rvalue::Field {
                base,
                len,
                index,
                variant: None,
            },
        )
    }
}

/// A type's identity: as a diagnostic writes it, but each type constructor with its module, and
/// each type parameter that `mark` numbers marked with its number.
fn ident_text(ty: &Ty, mark: &mut dyn FnMut(&Ty) -> Option<u32>, out: &mut String) {
    let list = |ts: &[Ty], mark: &mut dyn FnMut(&Ty) -> Option<u32>, out: &mut String| {
        for (k, t) in ts.iter().enumerate() {
            if k > 0 {
                out.push(',');
            }
            ident_text(t, mark, out);
        }
    };
    match ty {
        Ty::Con(item, args) => {
            out.push_str(&item.home);
            out.push('.');
            out.push_str(&item.name);
            if !args.is_empty() {
                out.push('<');
                list(args, mark, out);
                out.push('>');
            }
        }
        Ty::Tuple(ts) => {
            out.push('(');
            list(ts, mark, out);
            out.push(')');
        }
        Ty::Param(_) | Ty::SelfTy if let Some(i) = mark(ty) => out.push_str(&marked(i)),
        other => {
            let names =
                |g: &GenericId| Name::from(g.fresh_letter().unwrap_or('T').to_string().as_str());
            out.push_str(&Table::default().show(other, &names));
        }
    }
}
