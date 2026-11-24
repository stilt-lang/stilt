//! Specialization, for release builds (builds.specialization,
//! builds.what-stays-generic and builds.no-specialization-hints): each instantiation of generic
//! code that the program reaches from its roots, compiled from the counted MIR of a debug build
//! with what stands for its type and value arguments put in their place.
//!
//! A debug build compiles a generic function once for the layouts of its type arguments, and
//! passes it, after the location, a witness and a dictionary for each type parameter, its value
//! parameters and the descriptors of the types it reflects on, the function's hidden
//! parameters ([`crate::mir::Function::hidden`]). A call whose hidden arguments are known
//! calls the instantiation for them, which this module makes from the function's code with
//! them in place ([`function`]): a dictionary's methods called directly, compiled for it, a
//! value parameter's number folded into the arithmetic, a descriptor's parts read where they
//! are written, and a branch they decide a jump. The code of an object, a dictionary's method or
//! a closure's, is compiled for the object that holds it, whose fields it reads. Instantiations
//! whose code is the same are one function ([`merge`]).
//!
//! What stays generic keeps its dictionaries (builds.what-stays-generic): the functions of a
//! recursive group in which a call passes type arguments that could grow without end ([`groups`]),
//! which `keep` names, and the calls of a polymorphic argument, whose callee no call knows. A
//! program asks for nothing (builds.no-specialization-hints). The constants that instantiations
//! make are bounded in size ([`known::MOST_PARTS`]), and the instantiations of a program in number,
//! so that the code a type that holds itself ever more deeply would need is made at run time
//! instead.

mod function;
pub mod groups;
mod known;
mod merge;
#[cfg(test)]
mod tests;
pub mod types;
mod visit;

use std::collections::{HashMap, VecDeque};
use std::sync::Arc;

use crate::FnRef;
use crate::mir::{Const, Function};
use function::Instances;
use known::{Key, Known, knows_nothing, parts};

/// The most instantiations of one function that a build makes.
const MOST_OF_ONE: u32 = 4096;

/// Whether `f` is the code of an object, a closure or a dictionary's method, which takes the
/// object after its location.
#[must_use]
pub fn object_code(f: &FnRef) -> bool {
    match f {
        FnRef::Instance(g, _) | FnRef::Specialized(g, _) => object_code(g),
        FnRef::Closure(..)
        | FnRef::Entry(..)
        | FnRef::Value(_)
        | FnRef::Method(..)
        | FnRef::Constructor(_)
        | FnRef::Lent(_)
        | FnRef::Forward(..)
        | FnRef::Adapt(..)
        | FnRef::Describe(_)
        | FnRef::Access(..)
        | FnRef::Shaped(..) => true,
        _ => false,
    }
}

/// A release build's code: the functions it compiles, and for each instantiation it made, the
/// function of the debug build it was made from.
#[derive(Debug, Default)]
pub struct Specialized {
    /// The functions it compiles.
    pub functions: Vec<Arc<Function>>,
    /// By the name of each function compiled: the debug build's function it instantiates.
    pub made_from: HashMap<FnRef, FnRef>,
    /// By the name of each instantiation folded into another whose code is the same: that one.
    pub folded: HashMap<FnRef, FnRef>,
}

/// Specializes `functions`, the counted MIR of every function that `roots` reach, for each
/// instantiation that the roots reach. `keep` names the functions of the debug build that keep
/// their dictionaries (builds.what-stays-generic).
#[must_use]
pub fn specialize(
    functions: &[Arc<Function>],
    roots: &[FnRef],
    keep: &dyn Fn(&FnRef) -> bool,
) -> Specialized {
    let input: HashMap<FnRef, Arc<Function>> = functions
        .iter()
        .map(|f| (f.name.clone(), Arc::clone(f)))
        .collect();
    let mut s = Specializer {
        budget: 4 * functions.len() + 1024,
        input,
        keep,
        names: HashMap::new(),
        numbers: HashMap::new(),
        queue: VecDeque::new(),
        rewritten: HashMap::new(),
        original: HashMap::new(),
    };
    for root in roots {
        s.request(root, Vec::new());
    }
    let mut made = Vec::new();
    let mut made_from = HashMap::new();
    while let Some((base, key, name)) = s.queue.pop_front() {
        let mut f = Function::clone(&s.input[&base]);
        f.name = name.clone();
        function::specialize(&mut f, &key, &mut s);
        made_from.insert(name, base);
        made.push(f);
    }
    let folded = merge::merge(&mut made);
    Specialized {
        functions: made.into_iter().map(Arc::new).collect(),
        made_from,
        folded,
    }
}

/// The instantiations a build makes, as it makes them.
struct Specializer<'a> {
    input: HashMap<FnRef, Arc<Function>>,
    keep: &'a dyn Fn(&FnRef) -> bool,
    /// Each instantiation requested, by its function and key.
    names: HashMap<(FnRef, Key), FnRef>,
    /// The number of instantiations of each function so far.
    numbers: HashMap<FnRef, u32>,
    /// The instantiations requested and not yet made.
    queue: VecDeque<(FnRef, Key, FnRef)>,
    /// Each constant with its objects' code compiled for them, and back.
    rewritten: HashMap<Const, Const>,
    original: HashMap<Const, Const>,
    /// The instantiations the build may still make.
    budget: usize,
}

impl Specializer<'_> {
    /// A key whose constants are written as the debug build wrote them, so that one
    /// instantiation has one key, and which knows nothing of a constant too large to make.
    fn canonical(&self, key: Key) -> Key {
        let key: Key = key
            .into_iter()
            .map(|k| match k {
                Known::Const(c) if parts(&c) > known::MOST_PARTS => Known::Unknown,
                Known::Const(c) => Known::Const(self.original.get(&c).cloned().unwrap_or(c)),
                other => other,
            })
            .collect();
        if knows_nothing(&key) { Vec::new() } else { key }
    }
}

impl Instances for Specializer<'_> {
    fn request(&mut self, f: &FnRef, key: Key) -> FnRef {
        let mut key = self.canonical(key);
        if (self.keep)(f.generic()) {
            key = Vec::new();
        }
        if let Some(name) = self.names.get(&(f.clone(), key.clone())) {
            return name.clone();
        }
        let n = self.numbers.get(f).copied().unwrap_or(0);
        if !key.is_empty() && (self.budget == 0 || n >= MOST_OF_ONE) {
            return self.request(f, Vec::new());
        }
        let name = if key.is_empty() {
            f.clone()
        } else {
            self.numbers.insert(f.clone(), n + 1);
            self.budget -= 1;
            FnRef::Specialized(Box::new(f.clone()), n)
        };
        self.names.insert((f.clone(), key.clone()), name.clone());
        self.queue.push_back((f.clone(), key, name.clone()));
        name
    }

    fn hidden(&self, f: &FnRef) -> Option<u32> {
        self.input.get(f).map(|g| g.hidden)
    }

    fn rewrite(&mut self, c: &Const) -> Const {
        let Const::Data(tag, fields) = c else {
            return c.clone();
        };
        if let Some(r) = self.rewritten.get(c) {
            return r.clone();
        }
        let fields = fields
            .iter()
            .map(|(field, heap)| {
                let field = match field {
                    Const::Code(g) if object_code(g) && self.input.contains_key(g) => {
                        Const::Code(self.request(g, vec![Known::Const(c.clone())]))
                    }
                    Const::Data(..) => self.rewrite(field),
                    other => other.clone(),
                };
                (field, *heap)
            })
            .collect();
        let r = Const::Data(*tag, fields);
        self.rewritten.insert(c.clone(), r.clone());
        if r != *c {
            self.original.entry(r.clone()).or_insert_with(|| c.clone());
        }
        r
    }
}
