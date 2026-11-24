//! Where the values of a declared type keep their words (facts.allocation;
//! goal inline-values).
//!
//! A value of a record, a tuple or a variant whose type isn't recursive is held inline, in the
//! words of its layout: a record's fields one after the other, a tuple's elements, and a
//! variant type's tag, the immediate of the variant's index, followed by the words its variants'
//! payloads share. Every other value is one word: a scalar, or a heap word of a built-in type or
//! of a recursive type, whose payload sits in an object.
//!
//! Where a type parameter stands, in a field that a declaration types by a parameter, a tuple's
//! element or a type argument, a value is *held* in the words of its layout, so an `Option<P>`
//! is a tag and the words of a `P`. Generic code is compiled for the layouts of its type
//! arguments (`crate::items::Held`), so it holds the value in the same words as the code that
//! names its type, whatever its size.
//!
//! A declaration's *template* gives its words with its type parameters left open: a word of a
//! parameter's class stands for the words its argument is held in, and a word of a type
//! argument that names parameters, such as the `(T, i64)` of an `Option<(T, i64)>`, for the
//! words that argument is held in once they are known. The variants of a type share words by
//! class: the first scalar word of each payload is one word, and so are the first heap words,
//! and the first words of each type parameter. A parameter's words keep a class of their own, so
//! that the layout doesn't depend on whether an argument of one word is a scalar or a heap word,
//! and generic code that holds such an argument in one word whose witness tells agrees with the
//! code that names it. A word that a variant doesn't use holds 0, which no count reads.

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use stilt_hir::decls::{Lookup, Queried, TypeDefInfo};
use stilt_hir::hir::{GenericId, Item};
use stilt_types::ty::{Ty, is_array, is_view_type};

use crate::mir::Repr;
use crate::repr::is_scalar;

/// What a word of a declared type's template holds.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum Class {
    Scalar,
    Heap,
    /// The words of a value of the declaration's type parameter of this index.
    Param(usize),
    /// The words of a value of this type, which names the declaration's type parameters, held
    /// where a type parameter stands.
    Held(Ty),
}

/// The layout of a declared type's values, with its type parameters left open.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Template {
    /// Whether its values are heap words: a built-in type's that aren't scalars, and a
    /// recursive type's.
    pub(crate) heap: bool,
    /// Whether it has variants. Held inline, its first word is the tag.
    pub(crate) tagged: bool,
    /// The declaration's type parameters, which the classes of its words name.
    pub(crate) params: Vec<GenericId>,
    /// The words of a value held inline; none for a heap type.
    pub(crate) words: Vec<Class>,
    /// Each variant, or a record's one.
    pub(crate) variants: Vec<Variant>,
}

/// Where a variant's fields are: in the value's words when it is held inline, and otherwise in
/// the object the value points to.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Variant {
    /// The words of the object of a heap type's variant: its fields.
    pub(crate) object: Vec<Class>,
    /// The positions of each field's words, in the value's words or the object's.
    pub(crate) fields: Vec<Vec<usize>>,
}

/// The templates of a program's types, computed as lowering asks for them.
pub(crate) struct Templates<'a> {
    decls: Queried<'a>,
    known: RefCell<HashMap<Item, Rc<Template>>>,
    heaps: RefCell<HashMap<Item, bool>>,
}

/// Whether a type names one of `params`.
pub(crate) fn names_param(ty: &Ty, params: &[GenericId]) -> bool {
    match ty {
        Ty::Param(g) => params.contains(g),
        Ty::Tuple(ts) | Ty::Con(_, ts) => ts.iter().any(|t| names_param(t, params)),
        Ty::App(head, ts) => names_param(head, params) || ts.iter().any(|t| names_param(t, params)),
        Ty::Spread(s) => names_param(&s.pack, params) || names_param(&s.elem, params),
        Ty::Fn(_) | Ty::Handler(_) | Ty::SelfTy | Ty::Var(_) | Ty::Value(_) | Ty::Error => false,
    }
}

/// `ty` with each of `params` replaced by its argument, a spread of a pack among them expanded
/// into the elements its argument gives it (variadics.type-spreads).
pub(crate) fn substitute(ty: &Ty, params: &[GenericId], args: &[Ty]) -> Ty {
    let s = stilt_types::ty::Subst {
        types: params.iter().cloned().zip(args.iter().cloned()).collect(),
        ..stilt_types::ty::Subst::default()
    };
    stilt_types::ty::Table::default().subst(&s, ty)
}

impl<'a> Templates<'a> {
    pub(crate) fn new(decls: Queried<'a>) -> Self {
        Self {
            decls,
            known: RefCell::new(HashMap::new()),
            heaps: RefCell::new(HashMap::new()),
        }
    }

    /// Whether the values of a declared type are heap words.
    pub(crate) fn heap(&self, item: &Item) -> bool {
        if let Some(&heap) = self.heaps.borrow().get(item) {
            return heap;
        }
        let heap = match self.decls.type_info(item).map(|t| &t.def) {
            // An array holds its elements inline (generics.array-effects).
            Some(TypeDefInfo::Builtin) if is_view_type(item, "View") || is_array(item) => false,
            Some(TypeDefInfo::Builtin) => !is_scalar(&Ty::Con(item.clone(), Vec::new())),
            Some(_) => stilt_types::is_recursive(&self.decls, item),
            None => true,
        };
        self.heaps.borrow_mut().insert(item.clone(), heap);
        heap
    }

    /// The template of a declared type.
    pub(crate) fn of(&self, item: &Item) -> Rc<Template> {
        if let Some(t) = self.known.borrow().get(item) {
            return Rc::clone(t);
        }
        let t = Rc::new(self.compute(item));
        self.known.borrow_mut().insert(item.clone(), Rc::clone(&t));
        t
    }

    fn compute(&self, item: &Item) -> Template {
        let heap = self.heap(item);
        let Some(info) = self.decls.type_info(item) else {
            return opaque(heap);
        };
        let params = &info.params;
        let classes = |t: &stilt_hir::hir::Ty| self.classes(&Ty::from_hir(t, None), params);
        let mut template = match &info.def {
            // A view is its source's word and its two offsets, held inline (views.what-view-is):
            // `{ source: T, start: i64, end: i64 }` but for its name.
            TypeDefInfo::Builtin if is_view_type(item, "View") => {
                let fields = vec![
                    vec![Class::Param(0)],
                    vec![Class::Scalar],
                    vec![Class::Scalar],
                ];
                let (words, positions) = consecutive(&fields);
                record(false, words, positions)
            }
            TypeDefInfo::Builtin => opaque(heap),
            TypeDefInfo::Record(fields) => {
                let fields: Vec<Vec<Class>> = fields.iter().map(|(_, t)| classes(t)).collect();
                let (words, positions) = consecutive(&fields);
                record(heap, words, positions)
            }
            TypeDefInfo::Variants(variants) => {
                let payloads: Vec<Vec<Vec<Class>>> = variants
                    .iter()
                    .map(|(_, payload)| payload.iter().map(classes).collect())
                    .collect();
                if heap {
                    heap_variants(&payloads)
                } else {
                    shared(&payloads)
                }
            }
        };
        template.params.clone_from(params);
        template
    }

    /// The classes of the words of a type that a declaration with the type parameters
    /// `params` names.
    pub(crate) fn classes(&self, ty: &Ty, params: &[GenericId]) -> Vec<Class> {
        match ty {
            Ty::Param(g) => vec![
                params
                    .iter()
                    .position(|p| p == g)
                    .map_or(Class::Heap, Class::Param),
            ],
            _ if is_scalar(ty) => vec![Class::Scalar],
            // A tuple that spreads a parameter has as many words as its argument gives it.
            Ty::Tuple(ts) if ts.iter().any(|t| matches!(t, Ty::Spread(_))) => {
                vec![Class::Held(ty.clone())]
            }
            Ty::Tuple(ts) => ts.iter().flat_map(|t| self.held(t, params)).collect(),
            // An array's elements, each where a type parameter stands, as many as its size,
            // or the words its layout gives it once the declaration's parameters are known
            // (generics.large-arrays and generics.array-effects).
            Ty::Con(..) if let Some((elem, size)) = ty.arrayed() => {
                let each = self.held(elem, params);
                let words = each
                    .iter()
                    .all(|c| matches!(c, Class::Scalar | Class::Heap))
                    .then_some(each.len());
                match size {
                    Ty::Value(stilt_hir::hir::Value::Int(k))
                        if words.is_some_and(|w| !crate::lower::arrays::held_in_memory(*k, w)) =>
                    {
                        let k = usize::try_from(*k).unwrap_or(0);
                        crate::lower::arrays::repeated(&each, k, Class::Scalar)
                    }
                    // A size that a parameter gives, an element whose words its arguments
                    // give, or an array held in memory or past what compiled code holds,
                    // which lowering finds where it instantiates the type.
                    _ => vec![Class::Held(ty.clone())],
                }
            }
            Ty::Con(item, args) => {
                if self.heap(item) {
                    return vec![Class::Heap];
                }
                let inner = self.of(item);
                inner
                    .words
                    .iter()
                    .flat_map(|c| match c {
                        Class::Param(j) => args
                            .get(*j)
                            .map_or(vec![Class::Heap], |a| self.held(a, params)),
                        Class::Held(t) => self.held(&substitute(t, &inner.params, args), params),
                        c => vec![c.clone()],
                    })
                    .collect()
            }
            Ty::Fn(_)
            | Ty::Handler(_)
            | Ty::SelfTy
            | Ty::App(..)
            | Ty::Spread(_)
            | Ty::Var(_)
            | Ty::Value(_)
            | Ty::Error => {
                vec![Class::Heap]
            }
        }
    }

    /// The classes of the words that hold a value of `ty` where a type parameter stands, in a
    /// declaration with the type parameters `params`: those of its layout, or for a type that
    /// names the parameters, one class that stands for the words its argument is held in.
    fn held(&self, ty: &Ty, params: &[GenericId]) -> Vec<Class> {
        if !matches!(ty, Ty::Param(_)) && names_param(ty, params) {
            vec![Class::Held(ty.clone())]
        } else {
            self.classes(ty, params)
        }
    }
}

/// The template of a type without a declaration to read: one word.
fn opaque(heap: bool) -> Template {
    Template {
        heap,
        tagged: false,
        params: Vec::new(),
        words: if heap {
            Vec::new()
        } else {
            vec![Class::Scalar]
        },
        variants: Vec::new(),
    }
}

/// The fields' words one after the other, and the positions of each field's.
fn consecutive(fields: &[Vec<Class>]) -> (Vec<Class>, Vec<Vec<usize>>) {
    let mut words = Vec::new();
    let mut positions = Vec::new();
    for f in fields {
        positions.push((words.len()..words.len() + f.len()).collect());
        words.extend_from_slice(f);
    }
    (words, positions)
}

fn record(heap: bool, words: Vec<Class>, fields: Vec<Vec<usize>>) -> Template {
    let (words, object) = if heap {
        (Vec::new(), words)
    } else {
        (words, Vec::new())
    };
    Template {
        heap,
        tagged: false,
        params: Vec::new(),
        words,
        variants: vec![Variant { object, fields }],
    }
}

/// A recursive type's variants, each payload in an object of its own.
fn heap_variants(payloads: &[Vec<Vec<Class>>]) -> Template {
    Template {
        heap: true,
        tagged: true,
        params: Vec::new(),
        words: Vec::new(),
        variants: payloads
            .iter()
            .map(|fields| {
                let (object, fields) = consecutive(fields);
                Variant { object, fields }
            })
            .collect(),
    }
}

/// A variant type held inline: its tag, then the words its payloads share by class, the
/// scalars first, then the heap words, then each type parameter's, then each held type's, in
/// the order the payloads first name them.
fn shared(payloads: &[Vec<Vec<Class>>]) -> Template {
    let mut order: Vec<Class> = vec![Class::Scalar, Class::Heap];
    let mut most: HashMap<Class, usize> = HashMap::new();
    for fields in payloads {
        let mut used: HashMap<Class, usize> = HashMap::new();
        for c in fields.iter().flatten() {
            *used.entry(c.clone()).or_default() += 1;
            if !order.contains(c) {
                order.push(c.clone());
            }
        }
        for (c, n) in used {
            let m = most.entry(c).or_default();
            *m = (*m).max(n);
        }
    }
    order[2..].sort_by_key(|c| match c {
        Class::Param(j) => (0, *j),
        _ => (1, 0),
    });
    let mut words = vec![Class::Scalar];
    let mut start: HashMap<Class, usize> = HashMap::new();
    for c in &order {
        start.insert(c.clone(), words.len());
        words.extend(std::iter::repeat_n(
            c.clone(),
            most.get(c).copied().unwrap_or(0),
        ));
    }
    let variants = payloads
        .iter()
        .map(|fields| {
            let mut next = start.clone();
            let fields = fields
                .iter()
                .map(|f| {
                    f.iter()
                        .map(|c| {
                            let at = next.entry(c.clone()).or_default();
                            *at += 1;
                            *at - 1
                        })
                        .collect()
                })
                .collect();
            Variant {
                object: Vec::new(),
                fields,
            }
        })
        .collect();
    Template {
        heap: false,
        tagged: true,
        params: Vec::new(),
        words,
        variants,
    }
}

/// A declared type's layout for known arguments: its words, and where each variant's fields
/// are.
#[derive(Clone, Debug)]
pub(crate) struct Instance {
    pub(crate) heap: bool,
    pub(crate) tagged: bool,
    pub(crate) words: Vec<Repr>,
    /// For each variant, the words of its object, for a heap type, and the positions of each
    /// field's words.
    pub(crate) variants: Vec<(Vec<Repr>, Vec<Vec<usize>>)>,
}

impl Template {
    /// The layout of the type for the arguments `args`: each word of a parameter's class, or of
    /// a held type's, becomes the words that `held` gives for its type.
    pub(crate) fn instantiate(&self, args: &[Ty], held: &dyn Fn(&Ty) -> Vec<Repr>) -> Instance {
        let expand = |words: &[Class]| -> (Vec<Repr>, Vec<usize>) {
            let mut out = Vec::new();
            let mut starts = Vec::with_capacity(words.len() + 1);
            for c in words {
                starts.push(out.len());
                match c {
                    Class::Scalar => out.push(Repr::Scalar),
                    Class::Heap => out.push(Repr::Heap),
                    Class::Param(j) => match args.get(*j) {
                        Some(a) => out.extend(held(a)),
                        None => out.push(Repr::Heap),
                    },
                    Class::Held(t) => out.extend(held(&substitute(t, &self.params, args))),
                }
            }
            starts.push(out.len());
            (out, starts)
        };
        let moved = |fields: &[Vec<usize>], starts: &[usize]| -> Vec<Vec<usize>> {
            fields
                .iter()
                .map(|at| {
                    at.iter()
                        .flat_map(|&p| match (starts.get(p), starts.get(p + 1)) {
                            (Some(&a), Some(&b)) => a..b,
                            _ => 0..0,
                        })
                        .collect()
                })
                .collect()
        };
        let (words, starts) = expand(&self.words);
        let variants = self
            .variants
            .iter()
            .map(|v| {
                if self.heap {
                    let (object, at) = expand(&v.object);
                    (object, moved(&v.fields, &at))
                } else {
                    (Vec::new(), moved(&v.fields, &starts))
                }
            })
            .collect();
        Instance {
            heap: self.heap,
            tagged: self.tagged,
            words,
            variants,
        }
    }
}
