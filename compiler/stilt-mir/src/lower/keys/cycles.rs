//! Which requests of an instance are made within its own cycle of the call graph (goal
//! inline-values): only along a cycle can a request be made again with bigger type arguments,
//! without end, so only there do the caps of keys apply (`super`), and generic code that doesn't
//! reach itself is compiled for its type arguments whatever their size.
//!
//! The graph's nodes are the functions with bodies, and a trait, which stands for every method
//! of its impls and its defaults, since a dictionary may serve a call with any of them. A body
//! reaches the functions it calls or names as values, the trait of each method it calls, the
//! traits that bound the type parameters of its callees, which they may call, and the prelude's
//! traits that its comparisons, interpolations and map indexes call. A closure's calls are its
//! function's. The code the compiler makes reaches what it calls: a dictionary's entry, a
//! structural impl and a dictionary's method used as a value their trait, and a function used
//! as a value the function.

use std::collections::{HashMap, HashSet};

use stilt_hir::decls::prelude_item;
use stilt_hir::hir::{BinaryOp, Item};
use stilt_types::infer_body;
use stilt_types::tast::{Callee, Code, Definition, Expr, ExprKind, walk};

use crate::FnRef;
use crate::items::{Code as Where, ImplRef, bodies, code_of};
use crate::lower::functions::{signature, trait_method};
use crate::lower::{Cx, Lower};

/// A node of the call graph.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum Node {
    Fn(FnRef),
    Trait(Item),
}

/// The node of the code of `f`, if it can reach itself.
pub(crate) fn node_of(f: &FnRef) -> Option<Node> {
    match f.generic() {
        FnRef::Closure(p, _) | FnRef::Value(p) => node_of(p),
        g @ (FnRef::Function(_)
        | FnRef::Member(..)
        | FnRef::ImplMethod(..)
        | FnRef::DefaultMethod(..)) => Some(Node::Fn(g.clone())),
        FnRef::Entry(imp, _) => match &**imp {
            ImplRef::Written { trait_item, .. } | ImplRef::Structural { trait_item, .. } => {
                Some(Node::Trait(trait_item.clone()))
            }
        },
        FnRef::Structural(t, ..) | FnRef::Method(t, _) => Some(Node::Trait(t.clone())),
        _ => None,
    }
}

/// The nodes a body reaches directly.
pub(crate) fn edges(cx: &Cx<'_>, node: &Node) -> Vec<Node> {
    match node {
        Node::Trait(t) => bodies(cx.db, cx.program)
            .code
            .keys()
            .filter(
                |f| matches!(f, FnRef::ImplMethod(tr, ..) | FnRef::DefaultMethod(tr, _) if tr == t),
            )
            .map(|f| Node::Fn(f.clone()))
            .collect(),
        Node::Fn(f) => body_edges(cx, f),
    }
}

/// The nodes the body of `f` reaches directly.
fn body_edges(cx: &Cx<'_>, f: &FnRef) -> Vec<Node> {
    let Some(Where::Body(file, index)) = code_of(cx.db, cx.program, f.clone()) else {
        return Vec::new();
    };
    let typed = &infer_body(cx.db, cx.program, file, index).body;
    let Definition::Code(code) = &typed.code else {
        return Vec::new();
    };
    let mut out = Vec::new();
    let mut visit = |e: &Expr| expr_edges(cx, e, &mut out);
    match code {
        Code::Block(b) => walk::exprs_of_block(b, &mut visit),
        Code::Expr(e) => walk::iter(e, &mut |_| {}, &mut visit),
    }
    out
}

/// The nodes that an expression itself reaches.
fn expr_edges(cx: &Cx<'_>, e: &Expr, out: &mut Vec<Node>) {
    let prelude = |name: &str| Node::Trait(prelude_item(name));
    match &e.kind {
        ExprKind::Call(c, ..) | ExprKind::Project(c, ..) | ExprKind::Callee(c, _) => {
            callee_edges(cx, c, out);
        }
        ExprKind::Interpolated(_) => out.push(prelude("Show")),
        ExprKind::Binary(BinaryOp::Eq | BinaryOp::Ne, ..) => out.push(prelude("Eq")),
        ExprKind::Binary(BinaryOp::Lt | BinaryOp::Le | BinaryOp::Gt | BinaryOp::Ge, ..) => {
            out.push(prelude("Ord"));
        }
        ExprKind::Index(base, _) if base.ty.is_prelude("Map") => {
            out.extend([prelude("Hash"), prelude("Eq")]);
        }
        _ => {}
    }
}

/// The nodes that a call of `c`, or `c` named as a value, reaches: the callee, and the traits
/// that bound its type parameters.
fn callee_edges(cx: &Cx<'_>, c: &Callee, out: &mut Vec<Node>) {
    let decls = cx.decls();
    let sig = match c {
        Callee::Function(item) => {
            let f = FnRef::Function(item.clone());
            out.push(Node::Fn(f.clone()));
            signature(&decls, &f)
        }
        Callee::Member(owner, name) => {
            let f = FnRef::Member(owner.clone(), *name);
            out.push(Node::Fn(f.clone()));
            signature(&decls, &f)
        }
        Callee::TraitMethod(t, name, _) => {
            out.push(Node::Trait(t.clone()));
            trait_method(&decls, t, *name).map(|(_, sig)| sig)
        }
        // A performance runs a handler's body, a closure of the function that writes it.
        Callee::Operation(..) => None,
    };
    for (_, traits) in sig.iter().flat_map(|s| &s.type_params) {
        out.extend(traits.iter().map(|t| Node::Trait(t.clone())));
    }
}

impl Lower<'_> {
    /// Whether code of `callee` that this function requests is in this function's cycle of the
    /// call graph: whether it reaches this function.
    pub(crate) fn in_cycle(&self, callee: &FnRef) -> bool {
        node_of(callee).is_some_and(|n| self.reaches_self(n))
    }

    /// Whether a call of a method of trait `t`, which any of its impls may serve, is in this
    /// function's cycle of the call graph.
    pub(crate) fn trait_in_cycle(&self, t: &Item) -> bool {
        self.reaches_self(Node::Trait(t.clone()))
    }

    /// Whether `from` reaches this function's node.
    fn reaches_self(&self, from: Node) -> bool {
        let Some(me) = node_of(self.b.name()) else {
            return false;
        };
        if let Some(&known) = self.cycles.borrow().get(&from) {
            return known;
        }
        let mut seen = HashSet::from([from.clone()]);
        let mut next = vec![from.clone()];
        let mut found = false;
        let mut cache: HashMap<Node, Vec<Node>> = HashMap::new();
        while let Some(n) = next.pop() {
            if n == me {
                found = true;
                break;
            }
            let out = cache.entry(n.clone()).or_insert_with(|| edges(self.cx, &n));
            for m in out.iter() {
                if seen.insert(m.clone()) {
                    next.push(m.clone());
                }
            }
        }
        self.cycles.borrow_mut().insert(from, found);
        found
    }
}
