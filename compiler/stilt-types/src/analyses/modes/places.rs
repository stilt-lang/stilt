//! Places (modes.places), and the variables that code binds and may modify. Rule numbers in
//! comments refer to the Reference's modes chapter, unless they name another record.

use std::collections::HashMap;

use stilt_hir::hir::{ListRest, LocalId, Mode, Name};
use stilt_syntax::TextSize;

use crate::tast::walk::{self, Part};
use crate::tast::{Arg, Block, Expr, ExprKind, Pat, PatKind, StmtKind};

/// A step from a place to a part of it. An index is kept only as a position.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Step {
    /// A field, or a tuple's element by its number written out.
    Field(Name),
    Index,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Place {
    pub(crate) root: LocalId,
    pub(crate) path: Vec<Step>,
}

impl Place {
    /// The name of the variable the place is part of.
    pub(crate) fn name<'n>(&self, locals: &'n [Name]) -> &'n str {
        &locals[self.root.0 as usize]
    }

    /// The fields on the place's path, without its indexes.
    pub(crate) fn fields(&self) -> Vec<&Name> {
        self.path
            .iter()
            .filter_map(|s| match s {
                Step::Field(f) => Some(f),
                Step::Index => None,
            })
            .collect()
    }
}

/// The place an expression names, if it names one.
pub(crate) fn place(e: &Expr) -> Option<Place> {
    let mut path = Vec::new();
    let mut e = e;
    loop {
        match &e.kind {
            ExprKind::Local(v) => {
                path.reverse();
                return Some(Place { root: *v, path });
            }
            ExprKind::Field(base, name) => {
                path.push(Step::Field(*name));
                e = base;
            }
            ExprKind::TupleField(base, i) => {
                path.push(Step::Field(i.to_string().into()));
                e = base;
            }
            ExprKind::Index(base, _) => {
                path.push(Step::Index);
                e = base;
            }
            _ => return None,
        }
    }
}

/// Whether `a` starts `b`.
pub(super) fn is_prefix<T: PartialEq>(a: &[T], b: &[T]) -> bool {
    b.starts_with(a)
}

/// shared.names-that-may-be-one-place: each name of a `when` in a body, by its variable, with the
/// first name of its `when` whose value has the same type, which stands for both, since their
/// handles may reach one value.
#[derive(Debug, Default)]
pub(crate) struct Aliases(HashMap<LocalId, LocalId>);

impl Aliases {
    /// The names of every `when` in `block`, closures included.
    pub(crate) fn of(block: &Block) -> Self {
        let mut aliases = HashMap::new();
        walk::exprs_of_block(block, &mut |e| {
            if let ExprKind::When(held, _) = &e.kind {
                for (i, (handle, name)) in held.iter().enumerate() {
                    let first = held[..i].iter().find(|(h, _)| h.ty == handle.ty);
                    if let Some((_, first)) = first {
                        aliases.insert(*name, *first);
                    }
                }
            }
        });
        Self(aliases)
    }

    /// The variable that stands for `v` in the law of exclusivity.
    fn root(&self, v: LocalId) -> LocalId {
        self.0.get(&v).copied().unwrap_or(v)
    }
}

/// Whether two places can share a part (modes.overlap), the names of a `when` whose values have the
/// same type counting as one (shared.names-that-may-be-one-place).
pub(crate) fn overlap(a: &Place, b: &Place, aliases: &Aliases) -> bool {
    aliases.root(a.root) == aliases.root(b.root) && {
        let (fa, fb) = (a.fields(), b.fields());
        is_prefix(&fa, &fb) || is_prefix(&fb, &fa)
    }
}

/// The arguments of the projection whose call a place is rooted in (projections.call-is-place).
pub(super) fn projection_root(e: &Expr) -> Option<&[Arg]> {
    let mut e = e;
    loop {
        match &e.kind {
            ExprKind::Project(_, _, args, _) => return Some(args),
            ExprKind::Field(base, _) | ExprKind::TupleField(base, _) | ExprKind::Index(base, _) => {
                e = base;
            }
            _ => return None,
        }
    }
}

/// The expressions that a place evaluates to find its target, which are its indexes, in order.
/// Of an expression that isn't a place, the base that isn't one comes first. A projection's
/// arguments are its call's to weigh (projections.when-projection-runs).
pub(super) fn place_parts(e: &Expr) -> Vec<&Expr> {
    let mut parts = Vec::new();
    let mut e = e;
    loop {
        match &e.kind {
            ExprKind::Local(_) | ExprKind::Project(..) => break,
            ExprKind::Field(base, _) | ExprKind::TupleField(base, _) => e = base,
            ExprKind::Index(base, i) => {
                parts.push(&**i);
                e = base;
            }
            _ => {
                parts.push(e);
                break;
            }
        }
    }
    parts.reverse();
    parts
}

fn collect_pattern(p: &Pat, vars: &mut Vec<LocalId>) {
    match &p.kind {
        PatKind::Bind(v) => vars.push(*v),
        PatKind::List(ps, rest) => {
            if let ListRest::Bind(v) = rest {
                vars.push(*v);
            }
            for p in ps {
                collect_pattern(p, vars);
            }
        }
        PatKind::Tuple(ps) | PatKind::Variant(_, ps) | PatKind::Or(ps) => {
            for p in ps {
                collect_pattern(p, vars);
            }
        }
        PatKind::Record(fields) => {
            for (_, p) in fields {
                collect_pattern(p, vars);
            }
        }
        PatKind::Wild
        | PatKind::Int(_)
        | PatKind::Str(_)
        | PatKind::Bool(_)
        | PatKind::Const(_)
        | PatKind::Error => {}
    }
}

/// The variables a body declares with `var`, outside the closures in it, and the
/// names of its `when`s (shared.when).
pub(super) fn var_bindings(block: &Block) -> Vec<LocalId> {
    let mut found = Vec::new();
    collect_block(block, true, &mut found);
    found.into_iter().map(|(v, _)| v).collect()
}

/// [`var_bindings`] of the blocks inside an expression.
pub(super) fn expr_var_bindings(e: &Expr) -> Vec<LocalId> {
    let mut found = Vec::new();
    collect_expr(e, true, &mut found);
    found.into_iter().map(|(v, _)| v).collect()
}

/// The variables a body declares with `let`, outside the closures in it, each with the start of its
/// statement: the `let` that a `var` would make them modifiable with
/// (patterns.irrefutable-positions and patterns.let-else).
pub(super) fn let_bindings(block: &Block) -> Vec<(LocalId, TextSize)> {
    let mut found = Vec::new();
    collect_block(block, false, &mut found);
    found
}

/// [`let_bindings`] of the blocks inside an expression.
pub(super) fn expr_let_bindings(e: &Expr) -> Vec<(LocalId, TextSize)> {
    let mut found = Vec::new();
    collect_expr(e, false, &mut found);
    found
}

/// The variables that the statements declare with `var` if `var`, and with `let` otherwise.
fn collect_block(block: &Block, var: bool, found: &mut Vec<(LocalId, TextSize)>) {
    for s in block {
        let binding = match &s.kind {
            StmtKind::Var(b) if var => Some(b),
            StmtKind::Let(b) if !var => Some(b),
            _ => None,
        };
        if let Some(b) = binding {
            let mut vars = Vec::new();
            collect_pattern(&b.pattern, &mut vars);
            found.extend(vars.into_iter().map(|v| (v, s.at.start())));
        }
        for e in walk::stmt_exprs(s) {
            collect_expr(e, var, found);
        }
    }
}

fn collect_expr(e: &Expr, var: bool, found: &mut Vec<(LocalId, TextSize)>) {
    match &e.kind {
        ExprKind::Closure(..) => return,
        // shared.when: a `when`'s names are writable as a `var` is.
        ExprKind::When(held, _) if var => {
            found.extend(held.iter().map(|(_, place)| (*place, e.at.start())));
        }
        _ => {}
    }
    for part in walk::parts(e) {
        match part {
            Part::Expr(e) => collect_expr(e, var, found),
            Part::Block(b) => collect_block(b, var, found),
        }
    }
}

/// The `inout` parameters among a body's parameters.
pub(super) fn inout_params(params: &[(Mode, LocalId)]) -> impl Iterator<Item = LocalId> + '_ {
    params
        .iter()
        .filter(|(mode, _)| *mode == Mode::Inout)
        .map(|(_, v)| *v)
}

#[cfg(test)]
mod tests {
    use stilt_syntax::TextRange;

    use super::*;
    use crate::ty::Ty;

    fn field(f: &str) -> Step {
        Step::Field(f.into())
    }

    fn at(root: u32, path: Vec<Step>) -> Place {
        Place {
            root: LocalId(root),
            path,
        }
    }

    #[test]
    fn prefixes_start_lists() {
        assert!(is_prefix::<u8>(&[], &[]));
        assert!(is_prefix(&[], &[1]));
        assert!(is_prefix(&[1], &[1, 2]));
        assert!(is_prefix(&[1, 2], &[1, 2]));
        assert!(!is_prefix(&[1, 2], &[1]));
        assert!(!is_prefix(&[2], &[1, 2]));
    }

    #[test]
    fn places_overlap_along_their_fields() {
        let none = Aliases::default();
        let a = at(0, vec![field("a")]);
        assert!(overlap(&a, &at(0, vec![]), &none));
        assert!(overlap(&at(0, vec![]), &a, &none));
        assert!(overlap(&a, &at(0, vec![field("a"), field("b")]), &none));
        assert!(!overlap(&a, &at(0, vec![field("b")]), &none));
        assert!(!overlap(&a, &at(1, vec![field("a")]), &none));
    }

    #[test]
    fn indexes_are_ignored_by_overlap() {
        let none = Aliases::default();
        let first = at(0, vec![Step::Index, field("a")]);
        assert!(overlap(
            &first,
            &at(0, vec![field("a"), Step::Index]),
            &none
        ));
        assert!(overlap(&first, &at(0, vec![Step::Index]), &none));
        assert!(!overlap(
            &first,
            &at(0, vec![Step::Index, field("b")]),
            &none
        ));
    }

    /// shared.names-that-may-be-one-place: `when a, b, c`, where `a` and `c` hold values of one
    /// type and `b` of another, makes `c` stand for `a`, and leaves `b` alone.
    #[test]
    fn names_of_one_type_in_a_when_are_one() {
        let handle = |v: u32, ty: Ty| (typed(ExprKind::Local(LocalId(v)), ty), LocalId(v + 10));
        let held = vec![
            handle(0, Ty::bool()),
            handle(1, Ty::unit()),
            handle(2, Ty::bool()),
        ];
        let when = expr(ExprKind::When(held, Vec::new()));
        let block = vec![crate::tast::Stmt {
            kind: StmtKind::Expr(when),
            at: TextRange::default(),
        }];
        let aliases = Aliases::of(&block);
        let place = |v: u32| at(v + 10, vec![field("balance")]);
        assert!(overlap(&place(0), &place(2), &aliases));
        assert!(overlap(&place(2), &place(0), &aliases));
        assert!(!overlap(&place(0), &place(1), &aliases));
        assert!(!overlap(&place(0), &at(12, vec![field("fee")]), &aliases));
    }

    fn typed(kind: ExprKind, ty: Ty) -> Expr {
        Expr {
            kind,
            ty,
            at: TextRange::default(),
        }
    }

    fn expr(kind: ExprKind) -> Expr {
        typed(kind, Ty::Error)
    }

    fn index(base: Expr, i: &str) -> Expr {
        expr(ExprKind::Index(
            Box::new(base),
            Box::new(expr(ExprKind::Int(i.into()))),
        ))
    }

    #[test]
    fn places_run_from_their_root() {
        let base = expr(ExprKind::TupleField(
            Box::new(expr(ExprKind::Local(LocalId(3)))),
            0,
        ));
        let e = expr(ExprKind::Field(Box::new(index(base, "1")), "x".into()));
        assert_eq!(
            place(&e),
            Some(at(3, vec![field("0"), Step::Index, field("x")]))
        );
        assert_eq!(place(&index(expr(ExprKind::Hole), "1")), None);
    }

    #[test]
    fn place_parts_come_in_order() {
        let e = index(index(expr(ExprKind::Local(LocalId(0))), "1"), "2");
        let ints = |parts: Vec<&Expr>| -> Vec<String> {
            parts
                .into_iter()
                .map(|p| match &p.kind {
                    ExprKind::Int(i) => i.clone(),
                    _ => "base".to_owned(),
                })
                .collect()
        };
        assert_eq!(ints(place_parts(&e)), ["1", "2"]);
        let e = index(index(expr(ExprKind::Hole), "1"), "2");
        assert_eq!(ints(place_parts(&e)), ["base", "1", "2"]);
    }
}
