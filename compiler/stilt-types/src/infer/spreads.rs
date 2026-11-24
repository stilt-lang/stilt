//! Pack tuples and spread expressions (variadics.pack-tuples and variadics.spread-expressions).
//!
//! A pack tuple's arity isn't known in the body, so no pattern, index or loop takes it apart
//! (E0342). A spread `..e` maps over the pack tuples that `e` names: each stands for its element
//! while `e` is checked, all of them spread one pack (E0343), and none is named inside a closure
//! or another spread in `e` (E0343). Among a tuple's elements or a call's arguments it gives one
//! element for each of the pack's, of `e`'s type; among a list's, values of one type, which
//! names no pack (E0311).

use stilt_diag::codes;
use stilt_hir::hir::walk::{Visitor, walk_expr};
use stilt_hir::hir::{self, Arg, ExprKind, LocalId, Mode};
use stilt_syntax::TextRange;

use super::{Cx, State, error_node, node};
use crate::tast::{self, SpreadExpr};
use crate::ty::{Spread, Ty, is_prelude, replace};

/// The locals that an expression names, each where, and whether inside a closure or a spread
/// it holds, and whether it names a name with an error.
#[derive(Default)]
struct Named {
    found: Vec<(LocalId, TextRange, bool)>,
    depth: u32,
    /// Whether it names a name with an error, whose uses have the error type.
    broken: bool,
}

impl Visitor for Named {
    fn expr(&mut self, e: &hir::Expr) {
        match &e.kind {
            ExprKind::Local(v) => self.found.push((*v, e.at, self.depth > 0)),
            ExprKind::Error => self.broken = true,
            ExprKind::Closure(..) | ExprKind::Spread(_) => {
                self.depth += 1;
                walk_expr(self, e);
                self.depth -= 1;
            }
            _ => walk_expr(self, e),
        }
    }
}

/// Why a spread maps nothing: it names no pack tuple, or names one where it can't.
enum Unmapped {
    NoPack,
    Misused,
}

impl State<'_> {
    /// Whether `ty` is a pack tuple, whose type spreads a pack (variadics.pack-tuples).
    pub(super) fn pack_tuple(&self, ty: &Ty) -> bool {
        match self.resolved(ty) {
            Ty::Tuple(ts) => self
                .table
                .elements(&ts)
                .iter()
                .any(|t| t.as_spread().is_some()),
            _ => false,
        }
    }

    /// E0342 at `at`: an operation that would need a pack tuple's arity.
    pub(super) fn unknown_arity(&mut self, at: TextRange, what: &str) {
        let message = format!(
            "this tuple's type spreads a pack, so its arity isn't known and {what}; map it with \
             a spread instead"
        );
        self.error(codes::E0342, at, message);
    }

    /// E0343 at `at`.
    fn bad_spread(&mut self, at: TextRange, message: &str) -> tast::Expr {
        self.error(codes::E0343, at, message.to_owned());
        error_node(at)
    }

    /// The pack tuples that `e` names, each with its spread, or the error that it names none,
    /// names one where it can't, or names two of different packs.
    fn mapped(&mut self, e: &hir::Expr, at: TextRange) -> Result<Vec<(LocalId, Spread)>, Unmapped> {
        let mut named = Named::default();
        named.expr(e);
        let mut mapped: Vec<(LocalId, Spread)> = Vec::new();
        let mut broken = named.broken;
        for (v, used, nested) in named.found {
            let ty = self.locals.get(&v).map(|t| self.resolved(t));
            broken |= ty.as_ref().is_some_and(|t| self.table.mentions_error(t));
            let Some(ty @ Ty::Tuple(_)) = ty.filter(|t| self.pack_tuple(t)) else {
                continue;
            };
            if nested {
                self.bad_spread(
                    used,
                    "a tuple that a spread maps can't be named in a closure or a spread inside it",
                );
                return Err(Unmapped::Misused);
            }
            let Ty::Tuple(ts) = ty else { continue };
            let Some(s) = self
                .table
                .elements(&ts)
                .first()
                .and_then(Ty::as_spread)
                .cloned()
            else {
                continue;
            };
            if self.table.elements(&ts).len() != 1 {
                self.bad_spread(
                    used,
                    "a tuple that a spread maps spreads one pack and holds nothing else",
                );
                return Err(Unmapped::Misused);
            }
            if let Some((_, first)) = mapped.first()
                && self.resolved(&first.pack) != self.resolved(&s.pack)
            {
                self.bad_spread(
                    used,
                    "the tuples that a spread maps spread one pack, so that they have one length",
                );
                return Err(Unmapped::Misused);
            }
            if mapped.iter().all(|(w, _)| *w != v) {
                mapped.push((v, s));
            }
        }
        // A tuple or a name whose type is an error was reported where it was written
        // (errors.error-type).
        if mapped.is_empty() && broken {
            return Err(Unmapped::NoPack);
        }
        if mapped.is_empty() {
            self.bad_spread(
                at,
                "a spread maps a tuple whose type spreads a pack, and this one names none",
            );
            return Err(Unmapped::NoPack);
        }
        Ok(mapped)
    }

    /// The spread `..e` at `at`, `e` checked with each pack tuple it names standing for its
    /// element (variadics.spread-expressions).
    pub(super) fn spread(&mut self, cx: &mut Cx, e: &hir::Expr, at: TextRange) -> tast::Expr {
        let mapped = match self.mapped(e, at) {
            Ok(mapped) => mapped,
            // A spread's `e` has no expected type, so one that names no pack tuple is inferred
            // as any other `e` is, its own errors reported (variadics.spread-expressions).
            Err(Unmapped::NoPack) => {
                self.infer(cx, None, e);
                return error_node(at);
            }
            Err(Unmapped::Misused) => {
                self.abandon(cx, e);
                return error_node(at);
            }
        };
        let (pack, of) = (mapped[0].1.pack.clone(), mapped[0].1.of.clone());
        let saved: Vec<(LocalId, Option<Ty>)> = mapped
            .iter()
            .map(|(v, s)| {
                let elem = replace(&s.elem, &s.of, &Ty::Param(of.clone()));
                (*v, self.locals.insert(*v, elem))
            })
            .collect();
        let body = self.infer(cx, None, e);
        for (v, old) in saved {
            if let Some(old) = old {
                self.locals.insert(v, old);
            }
        }
        let ty = Ty::spread(pack.clone(), of.clone(), body.ty.clone());
        let spread = SpreadExpr {
            body,
            mapped: mapped.into_iter().map(|(v, _)| v).collect(),
            pack,
            of,
        };
        node(tast::ExprKind::Spread(Box::new(spread)), ty, at)
    }

    /// An element of a tuple, a list or a call: a spread, or any other expression, inferred.
    fn element(&mut self, cx: &mut Cx, e: &hir::Expr) -> tast::Expr {
        match &e.kind {
            ExprKind::Spread(inner) => self.spread(cx, inner, e.at),
            _ => self.infer(cx, None, e),
        }
    }

    /// A tuple with spreads among its elements, whose type spreads each one's pack.
    pub(super) fn spread_tuple(
        &mut self,
        cx: &mut Cx,
        at: TextRange,
        es: &[hir::Expr],
    ) -> tast::Expr {
        let items: Vec<tast::Expr> = es.iter().map(|e| self.element(cx, e)).collect();
        // A spread with an error stands for a number of values that nothing gives, so the
        // tuple's type is the error type (errors.error-type).
        let broken = (es.iter().zip(&items))
            .any(|(e, i)| matches!(e.kind, ExprKind::Spread(_)) && matches!(i.ty, Ty::Error));
        let ty = if broken {
            Ty::Error
        } else {
            Ty::Tuple(items.iter().map(|i| i.ty.clone()).collect())
        };
        node(tast::ExprKind::Tuple(items), ty, at)
    }

    /// A list with spreads among its elements: each spread's values have one type, which names
    /// no pack, so that every element has it (variadics.spread-checks; E0311).
    pub(super) fn spread_list(
        &mut self,
        cx: &mut Cx,
        expected: Option<&Ty>,
        at: TextRange,
        es: &[hir::Expr],
    ) -> tast::Expr {
        let elem = match expected.map(|t| self.resolved(t)) {
            Some(Ty::Con(item, args)) if is_prelude(&item, "List") && args.len() == 1 => {
                args[0].clone()
            }
            _ => self.fresh(at),
        };
        let mut items = Vec::new();
        for e in es {
            let item = self.element(cx, e);
            let ty = match &item.ty {
                Ty::Spread(s) => {
                    let frozen = self.table.freeze(&s.elem);
                    if replace(&frozen, &s.of, &Ty::Error) == frozen {
                        s.elem.clone()
                    } else {
                        let message = format!(
                            "each element of this spread has a type of its own, `{}`, so a \
                             list can't hold them; spread it in a tuple instead",
                            self.show(&s.elem)
                        );
                        self.error(codes::E0311, e.at, message);
                        Ty::Error
                    }
                }
                t => t.clone(),
            };
            self.expect(e.at, &elem, &ty);
            items.push(item);
        }
        node(tast::ExprKind::List(items), Ty::list(elem), at)
    }

    /// The arguments of a call whose parameters or arguments spread packs: the arguments'
    /// types, each spread's for each element, are the parameters' (variadics.spread-checks).
    pub(super) fn spread_arguments(
        &mut self,
        cx: &mut Cx,
        at: TextRange,
        params: &[(Mode, Ty)],
        args: &[Arg],
    ) -> Vec<tast::Arg> {
        self.spread_args(cx, at, (params, false), args)
    }

    /// The arguments, with a spread among them, of a call of a value whose type was unknown, and
    /// is now a function type with a new variable for each argument: each variable is that
    /// argument's type, a spread's among them, so that the callee takes the spread's pack as a
    /// hole takes the type its context expects (declarations.typed-holes and
    /// variadics.spread-expressions).
    pub(super) fn open_spread_arguments(
        &mut self,
        cx: &mut Cx,
        at: TextRange,
        params: &[(Mode, Ty)],
        args: &[Arg],
    ) -> Vec<tast::Arg> {
        self.spread_args(cx, at, (params, true), args)
    }

    /// The arguments of a call whose parameters or arguments spread packs, which are the
    /// parameters' elements, or, when `open`, each parameter's type one for one. A spread with an
    /// error stands for a number of values that nothing gives, so the arguments are no mismatch
    /// (errors.error-type).
    fn spread_args(
        &mut self,
        cx: &mut Cx,
        at: TextRange,
        (params, open): (&[(Mode, Ty)], bool),
        args: &[Arg],
    ) -> Vec<tast::Arg> {
        let values: Vec<tast::Expr> = args.iter().map(|a| self.element(cx, &a.value)).collect();
        let types: Vec<Ty> = values.iter().map(|v| v.ty.clone()).collect();
        let wanted: Vec<Ty> = params.iter().map(|(_, t)| t.clone()).collect();
        let broken = (args.iter().zip(&types))
            .any(|(a, t)| matches!(a.value.kind, ExprKind::Spread(_)) && matches!(t, Ty::Error));
        // The parameters meet the error type, which taints what they leave open, as a hole's
        // (errors.error-type).
        if broken {
            for w in &wanted {
                self.table.taint(w);
            }
        }
        let fits = broken
            || if open {
                wanted.len() == types.len()
                    && wanted
                        .iter()
                        .zip(&types)
                        .all(|(w, t)| self.table.unify(w, t))
            } else {
                self.table.unify_elems(&wanted, &types)
            };
        if !fits {
            let message = format!(
                "these arguments are `{}`, but the parameters are `{}`",
                self.show(&Ty::Tuple(types)),
                self.show(&Ty::Tuple(wanted)),
            );
            self.error(codes::E0311, at, message);
        }
        values
            .into_iter()
            .map(|value| tast::Arg {
                mode: Mode::Let,
                value,
                passes: false,
                kept: false,
            })
            .collect()
    }
}
