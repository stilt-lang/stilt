//! The operations of a body that have an effect themselves, and those that name the items whose
//! implicit effects they inherit (facts.inference and facts.allocation; effects.panic-kinds and
//! effects.panicking-operations; facts.writes-in-place, facts.copy-at-call and facts.div), and
//! those that can overflow (effects.overflow-effect).

mod overflow;
mod promised;

use std::cell::RefCell;

use stilt_hir::decls::Lookup;
use stilt_hir::hir::{BinaryOp, Item, Mode, UnaryOp};
use stilt_syntax::TextRange;

use super::alloc::is_recursive;
use super::descent::{Descent, Parts};
use super::names::{bound_names, callee_names, method_names};
use super::remedies::{Contexts, Remedy};
use super::storage::Storage;
use super::{Fact, Key, Scope, Site, walk_code};
use crate::literal::int_canonical;
use crate::tast::{Arg, Callee, Code, Expr, ExprKind, Segment, Stmt, StmtKind};
use crate::ty::Ty;
use crate::verify::Check;

/// Whether a type is an integer type.
fn is_integer(ty: &Ty) -> bool {
    ty.integer_name().is_some()
}

/// Whether a type is the prelude's `Map`.
fn is_map(ty: &Ty) -> bool {
    ty.is_prelude("Map")
}

/// effects.panicking-operations: a divisor written as an integer literal other than zero can't make
/// a division panic.
fn nonzero_literal(e: &Expr) -> bool {
    let nonzero = |text: &str| !int_canonical(text).is_empty();
    match &e.kind {
        ExprKind::Int(text) => nonzero(text),
        ExprKind::Unary(UnaryOp::Neg, operand) => {
            matches!(&operand.kind, ExprKind::Int(text) if nonzero(text))
        }
        _ => false,
    }
}

/// Whether dividing `a` by `b` can panic: an integer division whose divisor may be zero.
pub(crate) fn divides(a: &Expr, b: &Expr) -> bool {
    is_integer(&a.ty) && !nonzero_literal(b)
}

/// std.integers: a call of `div_euclid` or `rem_euclid` whose divisor is written as an
/// integer literal other than zero can't panic, as `/` and `%` can't, so its site doesn't name
/// the native.
fn euclidean_by_literal(c: &Callee, args: &[Arg]) -> bool {
    match (c, args) {
        (Callee::Member(owner, name), [_, divisor]) => {
            matches!(&**name, "div_euclid" | "rem_euclid")
                && crate::ty::is_numeric(owner)
                && !crate::ty::is_float(owner)
                && nonzero_literal(&divisor.value)
        }
        _ => false,
    }
}

/// The prelude's item `name`.
fn prelude(name: &str) -> Item {
    stilt_hir::decls::prelude_item(name)
}

/// std.maps and std.finding-keys: a map's keys are compared and hashed through their impls of `Eq`
/// and `Hash`.
fn key_names(decls: &dyn Lookup, ty: &Ty) -> Vec<Key> {
    match ty {
        Ty::Con(_, args) => match args.as_slice() {
            [key, _] => {
                let mut names = bound_names(decls, &[], &prelude("Eq"), key);
                names.extend(bound_names(decls, &[], &prelude("Hash"), key));
                names
            }
            _ => Vec::new(),
        },
        _ => Vec::new(),
    }
}

/// facts.allocation: a place that goes through an index, whose list or map a write may copy. An
/// index into a view goes through storage that a writable binding holds unique, so it copies
/// nothing (projections.places-through-views).
pub(super) fn through_index(place: &Expr) -> bool {
    match &place.kind {
        // An array's elements are stored inline, so writing one copies nothing but where the
        // array itself is held (generics.array-effects).
        ExprKind::Index(base, _) if base.ty.arrayed().is_some() => through_index(base),
        ExprKind::Index(base, _) => !base.ty.is_view() || through_index(base),
        ExprKind::Field(base, _) | ExprKind::TupleField(base, _) => through_index(base),
        _ => false,
    }
}

/// A write through an index, which may copy a shared list or map (facts.allocation).
fn write() -> Fact {
    Fact::noun("write through an index")
}

/// What [`find`] has found so far in a body, as it walks it.
struct Finder<'a> {
    decls: &'a dyn Lookup,
    scope: &'a Scope<'a>,
    storage: Storage<'a>,
    parts: Parts,
    descent: RefCell<Descent>,
    found: RefCell<Vec<Site>>,
    /// The places that store into a map, which insert their key and can't panic.
    stores: RefCell<Vec<&'a Expr>>,
    contexts: Contexts<'a>,
}

impl<'a> Finder<'a> {
    /// Records an operation that calls what it names, on `args` when they are known.
    fn add(&self, at: TextRange, names: Vec<Key>, args: Option<&[&Expr]>) {
        self.descend(&names, args);
        self.push(Site {
            called: true,
            ..Site::new(at, names)
        });
    }

    /// Records, for facts.descending-self-calls, a call that names the function itself.
    fn descend(&self, names: &[Key], args: Option<&[&Expr]>) {
        if self.scope.key.is_some_and(|k| names.contains(k)) {
            let strict = args.map_or_else(|| self.parts.none(), |a| self.parts.strict(a));
            self.descent.borrow_mut().call(&strict);
        }
    }

    /// Records an operation that can panic, the operation that `what` names, which names
    /// `names`, and which `remedy` keeps from panicking where it can.
    fn panics(&self, at: TextRange, what: &str, names: Vec<Key>, remedy: Option<Remedy>) {
        self.descend(&names, None);
        let site = Site {
            panic: Some(Fact::noun(what)),
            remedy,
            called: true,
            ..Site::new(at, names)
        };
        self.push(site);
    }

    /// Records an operation that can fail by `check` unless a rule of acceptance proves it can't
    /// (facts.range-loops, facts.guards, facts.divisors and facts.keys): then it adds no `panic`,
    /// and otherwise its error names what the closest rule needs (facts.closest-rule).
    fn checked(
        &self,
        at: TextRange,
        what: &str,
        names: Vec<Key>,
        remedy: Option<Remedy>,
        check: Check,
    ) {
        let accepted = self.scope.accepted;
        self.descend(&names, None);
        if let Some(rule) = accepted.proves(at, check) {
            return self.push(Site {
                called: true,
                proved: Some((check, rule)),
                ..Site::new(at, names)
            });
        }
        self.push(Site {
            panic: Some(Fact::noun(what)),
            remedy,
            called: true,
            need: (accepted.lacks(at, check)).map(|n| (super::Effect::Panic, n.clone())),
            ..Site::new(at, names)
        });
    }

    /// Records an operation that allocates, as `fact` says.
    fn allocates(&self, at: TextRange, fact: Fact) {
        let site = Site {
            alloc: Some(fact),
            ..Site::new(at, Vec::new())
        };
        self.push(site);
    }

    fn push(&self, site: Site) {
        self.found.borrow_mut().push(site);
    }

    /// The type a variant belongs to, when that type is recursive.
    fn recursive_variant(&self, variant: &Item) -> Option<Item> {
        let ty = &self.decls.variant(variant)?.ty;
        is_recursive(self.decls, ty).then(|| ty.clone())
    }

    /// The sites of a statement itself, before those of its expressions.
    fn stmt(&self, s: &'a Stmt) {
        self.contexts.stmt(s);
        self.overflow_stmt(s);
        match &s.kind {
            StmtKind::Assert(c) => {
                let remedy = self.contexts.assert(s, c);
                self.panics(s.at, "`assert`", Vec::new(), remedy);
            }
            StmtKind::Assign(Some(op @ (BinaryOp::Div | BinaryOp::Rem)), p, v) if divides(p, v) => {
                self.checked(s.at, division(*op), Vec::new(), None, Check::DivideByZero);
            }
            // A store into a map inserts its key, so it can't panic, and names the key's
            // impls of `Eq` and `Hash`.
            StmtKind::Assign(
                None,
                p @ Expr {
                    kind: ExprKind::Index(m, _),
                    ..
                },
                _,
            ) if is_map(&m.ty) => {
                self.stores.borrow_mut().push(p);
                self.descend(&key_names(self.decls, &m.ty), None);
                let site = Site {
                    alloc: Some(write()),
                    called: true,
                    ..Site::new(p.at, key_names(self.decls, &m.ty))
                };
                self.push(site);
                return;
            }
            _ => {}
        }
        match &s.kind {
            StmtKind::Assign(_, p, _) if self.in_place(s, p) => {}
            StmtKind::Assign(_, p, _) if through_index(p) => self.allocates(p.at, write()),
            // projections.yield: a yield whose place goes through an index allocates, as an
            // `inout` argument's does.
            StmtKind::Yield(p) if through_index(p) => {
                self.allocates(p.at, Fact::noun("`yield` through an index"));
            }
            _ => {}
        }
    }

    /// `m[k]` read: `bounds` on a list or an array, `missing-key` on a map, which names the
    /// key's impls of `Eq` and `Hash`.
    fn index(&self, e: &'a Expr, m: &'a Expr, k: &'a Expr) {
        let map = is_map(&m.ty);
        let names = if map {
            key_names(self.decls, &m.ty)
        } else {
            Vec::new()
        };
        // An array has no `get` to read an element without panicking (generics.array-elements).
        let remedy = if m.ty.arrayed().is_some() {
            None
        } else {
            self.contexts.index(e, m, k, map)
        };
        let check = if map {
            Check::MissingKey
        } else {
            Check::Bounds
        };
        self.checked(e.at, "index", names, remedy, check);
    }

    /// The site of an expression, if it is one, apart from those inside it.
    fn expr(&self, e: &'a Expr) {
        let decls = self.decls;
        self.contexts.expr(e);
        self.overflow_expr(e);
        match &e.kind {
            ExprKind::Index(m, k) if !self.stores.borrow().iter().any(|p| std::ptr::eq(*p, e)) => {
                self.index(e, m, k);
            }
            ExprKind::Binary(op @ (BinaryOp::Div | BinaryOp::Rem), a, b) if divides(a, b) => {
                self.checked(e.at, division(*op), Vec::new(), None, Check::DivideByZero);
            }
            ExprKind::Hole => self.panics(e.at, "hole", Vec::new(), None),
            ExprKind::Call(c, _, args, _) if euclidean_by_literal(c, args) => {
                self.inout_args(args);
            }
            // handlers.implicit-effects-and-capabilities: a performance calls its handler's
            // operation, a stored function value, which may not end and adds nothing else of its
            // own.
            ExprKind::Call(crate::tast::Callee::Operation(effect, op), _, args, _) => {
                self.performs(e, effect, op);
                self.inout_args(args);
            }
            ExprKind::Call(c, targs, args, _) | ExprKind::Project(c, targs, args, _) => {
                self.call(e, c, targs, args);
            }
            ExprKind::CallValue(f, args) => {
                self.stored_call(e, f);
                self.inout_args(args);
            }
            ExprKind::Callee(c, targs) => self.push(Site::new(e.at, callee_names(decls, c, targs))),
            ExprKind::Binary(BinaryOp::Eq | BinaryOp::Ne, a, b) => {
                let names = method_names(decls, &[], &prelude("Eq"), "eq", &a.ty);
                self.add(e.at, names, Some(&[&**a, &**b]));
            }
            ExprKind::Binary(BinaryOp::Lt | BinaryOp::Le | BinaryOp::Gt | BinaryOp::Ge, a, b) => {
                let names = method_names(decls, &[], &prelude("Ord"), "compare", &a.ty);
                self.add(e.at, names, Some(&[&**a, &**b]));
            }
            ExprKind::Interpolated(segments) => {
                self.allocates(e.at, Fact::noun("interpolated string"));
                for s in segments {
                    if let Segment::Splice(s, _) = s {
                        let names = method_names(decls, &[], &prelude("Show"), "show", &s.ty);
                        self.add(s.at, names, Some(&[&**s]));
                    }
                }
            }
            // facts.counting-loops: a counting loop adds no `div`.
            ExprKind::While(..) if self.scope.accepted.ends(e.at) => {}
            ExprKind::While(..) | ExprKind::Loop(_) => self.diverges(e),
            // shared.locks: a `when` holds shared values.
            ExprKind::When(..) => self.push(Site {
                locks: Some(Fact::noun("`when`")),
                ..Site::new(e.at, Vec::new())
            }),
            _ => self.allocating(e),
        }
    }

    /// A call by name: what it names, its `inout` arguments through an index, and its copies
    /// for in-place parameters (facts.copy-at-call).
    fn call(&self, e: &'a Expr, c: &Callee, targs: &[Ty], args: &'a [Arg]) {
        let names = callee_names(self.decls, c, targs);
        let values: Vec<&Expr> = args.iter().map(|a| &a.value).collect();
        if self.window(e, c, args) {
            self.descend(&names, Some(&values));
            self.push(Site {
                called: true,
                in_place: true,
                ..Site::new(e.at, names)
            });
        } else {
            self.add(e.at, names, Some(&values));
        }
        self.inout_args(args);
        self.copies(e, c, args);
    }

    /// facts.allocation: the expressions that allocate, apart from calls and interpolations.
    fn allocating(&self, e: &'a Expr) {
        let fact = match &e.kind {
            // An array's elements are stored inline (generics.array-effects).
            ExprKind::List(_) if e.ty.arrayed().is_some() => return,
            ExprKind::List(_) => Fact::noun("list"),
            ExprKind::Closure(..) => Fact::noun("closure"),
            ExprKind::Record(item, ..) if is_recursive(self.decls, item) => {
                Fact::noun(&format!("record of the recursive type `{}`", item.name))
            }
            ExprKind::Construct(variant, _, args) if !args.is_empty() => {
                let Some(ty) = self.recursive_variant(variant) else {
                    return;
                };
                Fact::noun(&format!(
                    "`{}` of the recursive type `{}`",
                    variant.name, ty.name
                ))
            }
            ExprKind::Constructor(variant, _) => {
                let Some(ty) = self.recursive_variant(variant) else {
                    return;
                };
                Fact::definite(format!(
                    "the constructor `{}` of the recursive type `{}`",
                    variant.name, ty.name
                ))
            }
            // A `with` allocates the handler it installs, and a `for` over an `Iter` the state it
            // pulls elements through, each at its keyword.
            ExprKind::With(..) => return self.allocates(keyword(e, 4), Fact::noun("`with`")),
            ExprKind::For(_, iterable, _) if over_iterator(iterable) => {
                let fact = Fact::noun("`for` over an iterator");
                return self.allocates(keyword(e, 3), fact);
            }
            _ => return,
        };
        self.allocates(e.at, fact);
    }

    /// facts.allocation: the `inout` arguments whose places go through an index.
    fn inout_args(&self, args: &[Arg]) {
        for a in args {
            if a.mode == Mode::Inout && through_index(&a.value) {
                let fact = Fact::noun("`inout` argument through an index");
                self.allocates(a.value.at, fact);
            }
        }
    }
}

/// The span of the keyword that starts `e`, `len` bytes long.
fn keyword(e: &Expr, len: u32) -> TextRange {
    TextRange::at(e.at.start(), stilt_syntax::TextSize::from(len))
}

/// Whether a `for` iterates an `Iter` (views.for-over-view).
fn over_iterator(iterable: &crate::tast::Iterable) -> bool {
    matches!(iterable, crate::tast::Iterable::Iter(source)
        if matches!(&source.ty, Ty::Con(item, _) if crate::ty::is_view_type(item, "Iter")))
}

/// The operation that a division or a remainder is, for messages.
fn division(op: BinaryOp) -> &'static str {
    if op == BinaryOp::Div {
        "division"
    } else {
        "remainder"
    }
}

/// What [`find`] gives: the sites of a body's code, and whether its calls of itself descend
/// (facts.descending-self-calls).
pub(super) struct Found {
    pub(super) sites: Vec<Site>,
    pub(super) descends: bool,
}

/// The sites of the code of the body that `scope` describes.
pub(super) fn find<'a>(decls: &'a dyn Lookup, scope: &'a Scope<'a>, code: &'a Code) -> Found {
    let finder = Finder {
        decls,
        scope,
        storage: Storage::of(scope.body, code, scope.limits.alloc),
        parts: Parts::of(scope.body, code),
        descent: RefCell::new(Descent::new(scope.body.params.len())),
        found: RefCell::new(Vec::new()),
        stores: RefCell::new(Vec::new()),
        contexts: Contexts::default(),
    };
    walk_code(code, &mut |s| finder.stmt(s), &mut |e| finder.expr(e));
    let descends = finder.descent.borrow().descends();
    let mut sites = finder.found.into_inner();
    // facts.closest-rule: each self-call of a function whose self-calls neither descend nor
    // shrink names what shrinking recursion needs.
    if let (false, Some(need), Some(key)) = (descends, scope.accepted.recursion_need(), scope.key) {
        for s in sites
            .iter_mut()
            .filter(|s| s.called && s.names.contains(key))
        {
            s.need = Some((super::Effect::Div, need.clone()));
        }
    }
    Found { sites, descends }
}
