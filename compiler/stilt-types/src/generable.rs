//! The types of a property's parameters as its generators see them (tests.generable-types and
//! tests.minimal-values): the types they hold, each a node of a graph, with each type's depth, from
//! which its minimal value and its nearest variants follow. The reference interpreter's
//! `Prop_types` builds the same graph.

use std::collections::HashMap;

use serde::{Deserialize, Serialize};
use stilt_hir::decls::{Lookup, TypeDefInfo, prelude_item};
use stilt_hir::hir::Name;

use crate::implements::{Bounds, implements_trait};
use crate::ty::{Ty, instantiate};

mod growth;

/// The depth of a type with no values.
pub const INFINITE: u32 = u32::MAX;

/// Why a type can't be generated (tests.generable-types).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Unfit {
    /// It holds a function type.
    Function,
    /// It holds this type, which has no values.
    NoValues(Ty),
    /// It holds a map whose key type, this one, doesn't implement both `Eq` and `Hash`.
    Key(Ty),
    /// It holds infinitely many types.
    Infinite,
}

/// A type as generators see it, its components by their nodes.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Node {
    /// `bool`.
    Bool,
    /// An integer type.
    Int {
        /// Its width in bits.
        bits: u32,
        /// Whether it is signed.
        signed: bool,
    },
    /// A float type.
    Float {
        /// Whether it is `f32`, rather than `f64`.
        f32: bool,
    },
    /// `str`.
    Str,
    /// `()`.
    Unit,
    /// A tuple type, by its elements' nodes.
    Tuple(Vec<usize>),
    /// A list type, by its element's node.
    List(usize),
    /// A map type, by its key's and its value's nodes.
    Map(usize, usize),
    /// A record, by its name, with its fields in declaration order.
    Record(Name, Vec<(Name, usize)>),
    /// A variant type's variants, in declaration order, with their payloads.
    Variants(Vec<(Name, Vec<usize>)>),
}

/// The types that some types hold.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Graph {
    /// The nodes, by index.
    pub nodes: Vec<Node>,
    /// The depth of each node's type, [`INFINITE`] for a type with no values.
    pub depths: Vec<u32>,
}

/// The graph of the types that `roots` hold, with the type of each node, and the node of each
/// root, or why one of them can't be generated.
///
/// # Errors
///
/// Fails with `Infinite` if the roots hold infinitely many types, else with the first reason
/// met in a walk of the types from the first root's.
pub fn graph(decls: &dyn Lookup, roots: &[Ty]) -> Result<(Graph, Vec<Ty>, Vec<usize>), Unfit> {
    if growth::infinite(decls, roots) {
        return Err(Unfit::Infinite);
    }
    let mut walk = Walk {
        decls,
        index: HashMap::new(),
        found: Vec::new(),
    };
    let params = roots
        .iter()
        .map(|t| walk.visit(t))
        .collect::<Result<Vec<_>, _>>()?;
    let (tys, nodes): (Vec<Ty>, Vec<Node>) = walk.found.into_iter().unzip();
    let depths = depths(&nodes);
    if let Some(i) = depths.iter().position(|&d| d == INFINITE) {
        return Err(Unfit::NoValues(tys[i].clone()));
    }
    Ok((Graph { nodes, depths }, tys, params))
}

/// Why a parameter's type can't be generated, if it can't. A type with an error can: no
/// diagnostic arises from it (errors.error-type).
#[must_use]
pub fn unfit(decls: &dyn Lookup, ty: &Ty) -> Option<Unfit> {
    if mentions_error(ty) {
        return None;
    }
    graph(decls, std::slice::from_ref(ty)).err()
}

fn mentions_error(ty: &Ty) -> bool {
    match ty {
        Ty::Error | Ty::Var(_) => true,
        Ty::Con(_, args) | Ty::Tuple(args) => args.iter().any(mentions_error),
        Ty::Fn(f) => f.params.iter().any(|(_, t)| mentions_error(t)) || mentions_error(&f.ret),
        Ty::Spread(s) => mentions_error(&s.elem),
        Ty::Param(_) | Ty::Handler(_) | Ty::SelfTy | Ty::App(..) | Ty::Value(_) => false,
    }
}

struct Walk<'a> {
    decls: &'a dyn Lookup,
    index: HashMap<Ty, usize>,
    found: Vec<(Ty, Node)>,
}

/// What a type's node is made of, before its components are numbered.
enum Shape {
    Scalar(Node),
    List,
    Map,
    Tuple,
    Record(Name, Vec<Name>),
    Variants(Vec<(Name, usize)>),
}

impl Walk<'_> {
    /// The node of a type, numbered the first time a walk meets it.
    fn visit(&mut self, ty: &Ty) -> Result<usize, Unfit> {
        if let Some(&i) = self.index.get(ty) {
            return Ok(i);
        }
        let i = self.found.len();
        self.index.insert(ty.clone(), i);
        self.found.push((ty.clone(), Node::Unit));
        let (shape, parts) = self.shape(ty)?;
        let slots = parts
            .iter()
            .map(|t| self.visit(t))
            .collect::<Result<Vec<_>, _>>()?;
        self.found[i].1 = match shape {
            Shape::Scalar(node) => node,
            Shape::List => Node::List(slots[0]),
            Shape::Map => Node::Map(slots[0], slots[1]),
            Shape::Tuple => Node::Tuple(slots),
            Shape::Record(name, fields) => {
                Node::Record(name, fields.into_iter().zip(slots).collect())
            }
            Shape::Variants(names) => {
                let mut rest = slots.into_iter();
                Node::Variants(
                    names
                        .into_iter()
                        .map(|(v, n)| (v, rest.by_ref().take(n).collect()))
                        .collect(),
                )
            }
        };
        Ok(i)
    }

    fn shape(&self, ty: &Ty) -> Result<(Shape, Vec<Ty>), Unfit> {
        let scalar = |node| Ok((Shape::Scalar(node), Vec::new()));
        let (item, args) = match ty {
            Ty::Con(item, args) => (item, args),
            Ty::Tuple(ts) if ts.is_empty() => return scalar(Node::Unit),
            Ty::Tuple(ts) => return Ok((Shape::Tuple, ts.clone())),
            Ty::Fn(_) | Ty::Handler(_) => return Err(Unfit::Function),
            Ty::Param(_)
            | Ty::SelfTy
            | Ty::App(..)
            | Ty::Spread(_)
            | Ty::Var(_)
            | Ty::Value(_)
            | Ty::Error => {
                return scalar(Node::Unit);
            }
        };
        if let Some(name) = ty.integer_name() {
            let bits = name[1..].parse().unwrap_or(64);
            return scalar(Node::Int {
                bits,
                signed: name.starts_with('i'),
            });
        }
        if let Some(name) = ty.numeric_name() {
            return scalar(Node::Float { f32: name == "f32" });
        }
        let info = self.decls.type_info(item);
        Ok(match info.as_ref().map(|i| &i.def) {
            _ if ty.is_prelude("bool") => (Shape::Scalar(Node::Bool), Vec::new()),
            _ if ty.is_prelude("str") => (Shape::Scalar(Node::Str), Vec::new()),
            Some(TypeDefInfo::Builtin) if ty.is_prelude("List") && args.len() == 1 => {
                (Shape::List, args.clone())
            }
            Some(TypeDefInfo::Builtin) if ty.is_prelude("Map") && args.len() == 2 => {
                if !self.keys(&args[0]) {
                    return Err(Unfit::Key(args[0].clone()));
                }
                (Shape::Map, args.clone())
            }
            Some(TypeDefInfo::Record(fields)) => {
                let params = &info.as_ref().map(|i| i.params.clone()).unwrap_or_default();
                let types = fields
                    .iter()
                    .map(|(_, t)| instantiate(t, params, args))
                    .collect();
                let names = fields.iter().map(|(f, _)| *f).collect();
                (Shape::Record(item.name, names), types)
            }
            Some(TypeDefInfo::Variants(vs)) => {
                let params = &info.as_ref().map(|i| i.params.clone()).unwrap_or_default();
                let types = vs
                    .iter()
                    .flat_map(|(_, p)| p.iter().map(|t| instantiate(t, params, args)))
                    .collect();
                let names = vs.iter().map(|(v, p)| (*v, p.len())).collect();
                (Shape::Variants(names), types)
            }
            _ => (Shape::Variants(Vec::new()), Vec::new()),
        })
    }

    /// Whether a map's key type implements both `Eq` and `Hash` (std.map-key-bounds).
    fn keys(&self, key: &Ty) -> bool {
        let bounds = Bounds::default();
        ["Eq", "Hash"]
            .iter()
            .all(|t| implements_trait(self.decls, (&bounds, &[]), key, &prelude_item(t)))
    }
}

/// The greatest depth among some nodes, 0 for none.
fn deepest(d: &[u32], slots: &[usize]) -> u32 {
    slots.iter().map(|&s| d[s]).max().unwrap_or(0)
}

/// tests.minimal-values: the least depths, found by lowering them from [`INFINITE`] until none
/// changes.
fn depths(nodes: &[Node]) -> Vec<u32> {
    let mut d: Vec<u32> = nodes
        .iter()
        .map(|n| match n {
            Node::Tuple(_) | Node::Record(..) | Node::Variants(_) => INFINITE,
            _ => 0,
        })
        .collect();
    let above = |h: u32| if h == INFINITE { INFINITE } else { h + 1 };
    loop {
        let mut changed = false;
        for (i, node) in nodes.iter().enumerate() {
            let next = match node {
                Node::Tuple(slots) => above(deepest(&d, slots)),
                Node::Record(_, fields) => {
                    let slots: Vec<usize> = fields.iter().map(|(_, s)| *s).collect();
                    above(deepest(&d, &slots))
                }
                Node::Variants(vs) => above(
                    vs.iter()
                        .map(|(_, p)| deepest(&d, p))
                        .min()
                        .unwrap_or(INFINITE),
                ),
                _ => d[i],
            };
            if next < d[i] {
                d[i] = next;
                changed = true;
            }
        }
        if !changed {
            return d;
        }
    }
}

impl Graph {
    /// The height of a variant: the greatest depth of its payloads, 0 for none.
    #[must_use]
    pub fn height(&self, payload: &[usize]) -> u32 {
        deepest(&self.depths, payload)
    }

    /// The numbers of a variant type's variants whose payload types all have values, in
    /// declaration order.
    #[must_use]
    pub fn live(&self, variants: &[(Name, Vec<usize>)]) -> Vec<usize> {
        (0..variants.len())
            .filter(|&v| self.height(&variants[v].1) != INFINITE)
            .collect()
    }

    /// The numbers of a variant type's nearest variants, in declaration order
    /// (tests.minimal-values).
    #[must_use]
    pub fn nearest(&self, variants: &[(Name, Vec<usize>)]) -> Vec<usize> {
        let live = self.live(variants);
        let least = live.iter().map(|&v| self.height(&variants[v].1)).min();
        live.into_iter()
            .filter(|&v| Some(self.height(&variants[v].1)) == least)
            .collect()
    }
}
