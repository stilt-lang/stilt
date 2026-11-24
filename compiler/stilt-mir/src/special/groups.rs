//! The functions that keep their dictionaries in a release build (builds.what-stays-generic): every
//! function of a recursive group in which a call passes type arguments other than the group's
//! own (polymorphism.recursion), whose instantiations could grow without end.
//!
//! The groups are the strongly connected components of the call graph of `super::super::lower::keys`:
//! a body reaches what it calls, and a trait, which stands for every method of its impls, so a
//! call through a dictionary may reach any of them. A call grows its group when it passes a type
//! argument that is built from the caller's type parameters without being one of them, as
//! `depth(inner)` passes `Nested<List<T>>` for `T`: a type that holds no type parameter, as
//! `i64`, gives a group one instantiation more, never one without end. A trait's method called
//! on such a type reaches the impl of the type's constructor, or, where the trait's impl for it
//! is structural, as a list's `==` is, the impls of the types it holds, so `self.kids ==
//! o.kids` in the `Eq` of a tree whose kids are a list of trees passes the tree's own type.

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use stilt_db::{Db, Program};
use stilt_hir::decls::{Lookup, prelude_item};
use stilt_hir::hir::{BinaryOp, Item};
use stilt_syntax::TextRange;
use stilt_types::tast::{Callee, Code, Definition, Expr, ExprKind, Segment, walk};
use stilt_types::ty::Ty;

use crate::FnRef;
use crate::items::{Code as Where, code_of};
use crate::lower::Cx;
use crate::lower::keys::{Node, edges, node_of};
use crate::mir::Function;

/// The groups of a program whose functions keep their dictionaries.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Groups {
    /// The functions with bodies that keep their dictionaries.
    pub kept: HashSet<FnRef>,
    /// Each call that grows its group: its caller, and where the call is in the caller's body.
    pub growing: Vec<(FnRef, TextRange)>,
}

/// The groups of the functions that `functions`, a build's, are code of.
#[must_use]
pub fn groups(db: &dyn Db, program: Program, functions: &[Arc<Function>]) -> Groups {
    let cx = Cx { db, program };
    let graph = Graph::explore(&cx, functions.iter().filter_map(|f| node_of(&f.name)));
    let mut out = Groups::default();
    for component in graph.components() {
        let members: HashSet<&Node> = component.iter().map(|&i| &graph.nodes[i]).collect();
        let cyclic = members.len() > 1 || component.iter().any(|&i| graph.succ[i].contains(&i));
        if !cyclic {
            continue;
        }
        let mut growing = Vec::new();
        for node in &members {
            if let Node::Fn(f) = node {
                growing.extend(
                    grows(&cx, f, &members)
                        .into_iter()
                        .map(|at| (f.clone(), at)),
                );
            }
        }
        if growing.is_empty() {
            continue;
        }
        for node in members {
            if let Node::Fn(f) = node {
                out.kept.insert(f.clone());
            }
        }
        out.growing.extend(growing);
    }
    out.growing.sort_by_key(|(f, at)| (f.symbol(), at.start()));
    out
}

/// The part of the call graph that a build's functions reach.
struct Graph {
    nodes: Vec<Node>,
    succ: Vec<Vec<usize>>,
}

impl Graph {
    fn explore(cx: &Cx<'_>, starts: impl Iterator<Item = Node>) -> Self {
        let mut index: HashMap<Node, usize> = HashMap::new();
        let mut g = Graph {
            nodes: Vec::new(),
            succ: Vec::new(),
        };
        let mut next = Vec::new();
        for n in starts {
            if !index.contains_key(&n) {
                index.insert(n.clone(), g.nodes.len());
                next.push(g.nodes.len());
                g.nodes.push(n);
                g.succ.push(Vec::new());
            }
        }
        while let Some(i) = next.pop() {
            let out: Vec<usize> = edges(cx, &g.nodes[i])
                .into_iter()
                .map(|m| {
                    *index.entry(m.clone()).or_insert_with(|| {
                        next.push(g.nodes.len());
                        g.nodes.push(m);
                        g.succ.push(Vec::new());
                        g.nodes.len() - 1
                    })
                })
                .collect();
            g.succ[i] = out;
        }
        g
    }

    /// The strongly connected components, by Tarjan's algorithm, without recursion.
    fn components(&self) -> Vec<Vec<usize>> {
        let n = self.nodes.len();
        let (mut low, mut num) = (vec![0usize; n], vec![usize::MAX; n]);
        let (mut on, mut stack, mut out) = (vec![false; n], Vec::new(), Vec::new());
        let mut counter = 0;
        for root in 0..n {
            if num[root] != usize::MAX {
                continue;
            }
            let mut frames = vec![(root, 0usize)];
            num[root] = counter;
            low[root] = counter;
            counter += 1;
            stack.push(root);
            on[root] = true;
            while let Some(&mut (v, ref mut k)) = frames.last_mut() {
                if let Some(&w) = self.succ[v].get(*k) {
                    *k += 1;
                    if num[w] == usize::MAX {
                        (num[w], low[w]) = (counter, counter);
                        counter += 1;
                        stack.push(w);
                        on[w] = true;
                        frames.push((w, 0));
                    } else if on[w] {
                        low[v] = low[v].min(num[w]);
                    }
                    continue;
                }
                frames.pop();
                if let Some(&(parent, _)) = frames.last() {
                    low[parent] = low[parent].min(low[v]);
                }
                if low[v] == num[v] {
                    let mut component = Vec::new();
                    while let Some(w) = stack.pop() {
                        on[w] = false;
                        component.push(w);
                        if w == v {
                            break;
                        }
                    }
                    out.push(component);
                }
            }
        }
        out
    }
}

/// Where the body of `f` calls into its group with a type argument that grows the group.
fn grows(cx: &Cx<'_>, f: &FnRef, members: &HashSet<&Node>) -> Vec<TextRange> {
    let Some(Where::Body(file, index)) = code_of(cx.db, cx.program, f.clone()) else {
        return Vec::new();
    };
    let typed = &stilt_types::infer_body(cx.db, cx.program, file, index).body;
    let Definition::Code(code) = &typed.code else {
        return Vec::new();
    };
    let decls = cx.decls();
    let own = own_self(&decls, f);
    let check = Check {
        decls: &decls,
        own: own.as_ref(),
        members,
    };
    let mut out = Vec::new();
    let mut visit = |e: &Expr| {
        if check.expr(e) {
            out.push(e.at);
        }
    };
    match code {
        Code::Block(b) => walk::exprs_of_block(b, &mut visit),
        Code::Expr(e) => walk::iter(e, &mut |_| {}, &mut visit),
    }
    out
}

/// The type an impl's method is a method of, which its calls on `self` pass as its own.
fn own_self(decls: &dyn Lookup, f: &FnRef) -> Option<Ty> {
    match f {
        FnRef::ImplMethod(t, owner, _) => decls
            .trait_impl(t, owner)
            .map(|info| Ty::from_hir(&info.self_ty, None)),
        FnRef::DefaultMethod(..) => Some(Ty::SelfTy),
        _ => None,
    }
}

/// What decides whether a call of a body grows its group.
struct Check<'a> {
    decls: &'a dyn Lookup,
    own: Option<&'a Ty>,
    members: &'a HashSet<&'a Node>,
}

impl Check<'_> {
    fn member(&self, n: &Node) -> bool {
        self.members.contains(n)
    }

    fn prelude(&self, name: &str) -> Option<Item> {
        let t = prelude_item(name);
        self.member(&Node::Trait(t.clone())).then_some(t)
    }

    /// Whether the expression itself calls into the group with a type that grows it.
    fn expr(&self, e: &Expr) -> bool {
        match &e.kind {
            ExprKind::Call(c, targs, ..)
            | ExprKind::Project(c, targs, ..)
            | ExprKind::Callee(c, targs) => self.call(c, targs),
            ExprKind::Binary(op, a, _) => {
                let name = match op {
                    BinaryOp::Eq | BinaryOp::Ne => "Eq",
                    BinaryOp::Lt | BinaryOp::Le | BinaryOp::Gt | BinaryOp::Ge => "Ord",
                    _ => return false,
                };
                self.prelude(name)
                    .is_some_and(|t| self.self_grows(&t, &a.ty))
            }
            ExprKind::Interpolated(segments) => self.prelude("Show").is_some_and(|t| {
                segments.iter().any(|s| match s {
                    Segment::Splice(x, _) => self.self_grows(&t, &x.ty),
                    Segment::Text(_) => false,
                })
            }),
            ExprKind::Index(base, key) if base.ty.is_prelude("Map") => {
                ["Hash", "Eq"].iter().any(|n| {
                    self.prelude(n)
                        .is_some_and(|t| self.self_grows(&t, &key.ty))
                })
            }
            _ => false,
        }
    }

    fn call(&self, c: &Callee, targs: &[Ty]) -> bool {
        let node = match c {
            Callee::Function(item) => Node::Fn(FnRef::Function(item.clone())),
            Callee::Member(owner, name) => Node::Fn(FnRef::Member(owner.clone(), *name)),
            Callee::TraitMethod(t, _, self_ty) => {
                let node = Node::Trait(t.clone());
                return self.member(&node)
                    && (self.self_grows(t, self_ty) || targs.iter().any(grows_from));
            }
            Callee::Operation(..) => return false,
        };
        self.member(&node) && targs.iter().any(grows_from)
    }

    /// Whether a trait's method called on a value of type `ty` passes the group a type that
    /// grows it: through the impl of its constructor, or the impls of the types a structural
    /// impl reaches.
    fn self_grows(&self, t: &Item, ty: &Ty) -> bool {
        if !mentions_params(ty) || self.own == Some(ty) {
            return false;
        }
        match ty {
            Ty::Param(_) | Ty::SelfTy => false,
            Ty::Con(item, args) if self.decls.trait_impl(t, item).is_none() => {
                args.iter().any(|a| self.self_grows(t, a))
            }
            Ty::Tuple(ts) => ts.iter().any(|a| self.self_grows(t, a)),
            _ => true,
        }
    }
}

/// Whether a type argument grows a group: it is built from type parameters without being one.
fn grows_from(ty: &Ty) -> bool {
    !matches!(ty, Ty::Param(_) | Ty::SelfTy | Ty::Value(_)) && mentions_params(ty)
}

/// Whether a type names a type parameter or `Self`.
#[must_use]
pub fn mentions_params(ty: &Ty) -> bool {
    match ty {
        Ty::Param(_) | Ty::SelfTy | Ty::Spread(_) => true,
        Ty::Con(_, args) | Ty::Tuple(args) => args.iter().any(mentions_params),
        Ty::App(head, args) => mentions_params(head) || args.iter().any(mentions_params),
        Ty::Fn(f) => f.params.iter().any(|(_, p)| mentions_params(p)) || mentions_params(&f.ret),
        Ty::Handler(_) | Ty::Value(_) | Ty::Var(_) | Ty::Error => false,
    }
}
