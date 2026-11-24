//! Values as words (`crate::layout`): the layout of a type where lowering stands, the fields of
//! a value, building one, the words that hold a value where a type parameter stands, and the
//! one word in which natives and the methods of dictionaries take a value: its box, lent for a
//! call or made on the heap.

use std::rc::Rc;

use stilt_hir::decls::{Lookup, TypeDefInfo};
use stilt_types::ty::{Ty, instantiate, is_view_type};

use super::Lower;
use super::exprs::immediate;
use crate::layout::Instance;
use crate::mir::{Arg, Heapness, Local, Operand, Repr, Rvalue, Stmt, Variant};
use crate::repr::is_scalar;

/// Where the fields of a record, a tuple or a variant are.
#[derive(Clone, Debug)]
pub(crate) struct Fields {
    /// Whether the value is tagged, its first word or its object's header giving its variant.
    pub(crate) tagged: bool,
    /// The words of the object that holds the fields, for a value of a recursive type, which is
    /// a heap word; `None` when they are the value's own words.
    pub(crate) object: Option<Vec<Repr>>,
    /// Each field, in declaration order.
    pub(crate) all: Vec<Field>,
    /// The tag of the object that holds the fields, for a declared type whose values are held
    /// in one: the variant's index, or 0 for a record.
    pub(crate) tag: Option<u16>,
}

/// A field of a value.
#[derive(Clone, Debug)]
pub(crate) struct Field {
    pub(crate) ty: Ty,
    /// The positions of its words, in the value's words or its object's.
    pub(crate) at: Vec<usize>,
}

/// The word at position `i` of a value, or 0 where code is unreachable and the value a
/// placeholder.
pub(crate) fn word(v: &[Operand], i: usize) -> Operand {
    v.get(i).cloned().unwrap_or(Operand::word(0))
}

impl Lower<'_> {
    /// The words of a value of type `ty`: a type parameter's are those its generic holds it
    /// in, and a tuple and a declared type hold the words of their arguments inline, each as a
    /// type parameter's place holds it ([`Lower::held`]).
    pub(crate) fn layout(&self, ty: &Ty) -> Vec<Repr> {
        match ty {
            Ty::Param(_) | Ty::SelfTy => self
                .generic(ty)
                .map_or(vec![Repr::Heap], super::Generic::layout),
            // A constructor parameter applied is known in every instance of its function, which
            // the instance's key names, so only code with an error holds one.
            // A value argument is no value's type (generics.value-arguments).
            Ty::Error | Ty::App(..) | Ty::Value(_) => {
                self.b.met_error();
                vec![Repr::Heap]
            }
            _ if is_scalar(ty) => vec![Repr::Scalar],
            Ty::Tuple(_) if super::packs::is_dynamic_tuple(ty) => vec![Repr::Heap],
            Ty::Tuple(ts) => ts.iter().flat_map(|t| self.layout(t)).collect(),
            Ty::Con(..) if let Some((elem, size)) = ty.arrayed() => self.array_layout(elem, size),
            Ty::Con(item, args) if !self.templates.heap(item) => {
                self.instance_of(item, args).words.clone()
            }
            // A spread that no instance expands holds its elements in a list.
            Ty::Con(..) | Ty::Fn(_) | Ty::Handler(_) | Ty::Spread(_) | Ty::Var(_) => {
                vec![Repr::Heap]
            }
        }
    }

    /// The layout of a declared type for its arguments.
    pub(crate) fn instance_of(&self, item: &stilt_hir::hir::Item, args: &[Ty]) -> Rc<Instance> {
        let key = Ty::Con(item.clone(), args.to_vec());
        if let Some(i) = self.instances.borrow().get(&key) {
            return Rc::clone(i);
        }
        let instance = Rc::new(
            self.templates
                .of(item)
                .instantiate(args, &|t: &Ty| self.layout(t)),
        );
        self.instances
            .borrow_mut()
            .insert(key, Rc::clone(&instance));
        instance
    }

    /// The one word that holds a value of type `ty` where natives and the methods of
    /// dictionaries take it: its own, or for a value of several words, its box, a heap word.
    pub(crate) fn repr(&self, ty: &Ty) -> Repr {
        match self.layout(ty).as_slice() {
            [r] if !matches!(r, Repr::Array(_)) => *r,
            _ => Repr::Heap,
        }
    }

    /// What the slot of an `inout` pointer to a value of type `ty` holds, as its parameter's
    /// representation says: the value's one word, or for a value of several words, a scalar.
    pub(crate) fn ref_repr(&self, ty: &Ty) -> Repr {
        match self.layout(ty).as_slice() {
            [r] if !matches!(r, Repr::Array(_)) => *r,
            _ => Repr::Scalar,
        }
    }

    /// Whether a value of type `ty` is held in one word: not in several, and not in the words
    /// of an array held in memory.
    pub(crate) fn one_word(&self, ty: &Ty) -> bool {
        one_word(&self.layout(ty))
    }

    /// The number of words of a value of type `ty`, in memory.
    pub(crate) fn words_of(&self, ty: &Ty) -> usize {
        crate::mir::offsets(self.layout(ty)).1
    }

    /// The argument that lends a value of type `ty`, whose words the caller keeps, in one word
    /// to a callee that borrows it: its word, or a box of its words on the caller's stack.
    pub(crate) fn lend(&mut self, words: Vec<Operand>, ty: &Ty) -> Arg {
        let layout = self.layout(ty);
        if one_word(&layout) {
            return Arg::Borrow(self.boxed(words, ty));
        }
        let words = words.into_iter().chain(std::iter::repeat(Operand::word(0)));
        Arg::Lend(
            words
                .zip(layout)
                .map(|(w, r)| (w, Heapness::of(r)))
                .collect(),
        )
    }

    /// New locals for the words of a value of type `ty`, one after the other.
    pub(crate) fn temps(&mut self, ty: &Ty) -> Vec<Local> {
        self.layout(ty)
            .into_iter()
            .map(|r| self.b.temp(r))
            .collect()
    }

    /// Where the fields of `variant` of a value of type `ty` are: a record's, whose one
    /// variant is 0, a tuple's elements, or a variant's payload.
    pub(crate) fn fields_of(&self, ty: &Ty, variant: usize) -> Fields {
        let (item, args) = match ty {
            Ty::Tuple(ts) => {
                let mut next = 0;
                let fields = ts
                    .iter()
                    .map(|t| {
                        let n = self.layout(t).len();
                        next += n;
                        Field {
                            ty: t.clone(),
                            at: (next - n..next).collect(),
                        }
                    })
                    .collect();
                return Fields {
                    tagged: false,
                    object: None,
                    all: fields,
                    tag: None,
                };
            }
            Ty::Con(..) if let Some((elem, size)) = ty.arrayed() => {
                return self.array_fields(elem, size);
            }
            Ty::Con(item, args) => (item, args),
            _ => {
                return Fields {
                    tagged: false,
                    object: None,
                    all: Vec::new(),
                    tag: None,
                };
            }
        };
        let instance = self.instance_of(item, args);
        let declared = self.declared_fields(item, variant, args);
        let v = instance.variants.get(variant);
        let fields = declared
            .into_iter()
            .enumerate()
            .map(|(j, ty)| {
                let at = v.and_then(|v| v.1.get(j)).cloned().unwrap_or_default();
                Field { ty, at }
            })
            .collect();
        let declared = self.declared(item);
        let tag = if instance.tagged { variant } else { 0 };
        Fields {
            tagged: instance.tagged,
            object: instance
                .heap
                .then(|| v.map(|v| v.0.clone()).unwrap_or_default()),
            all: fields,
            tag: (declared && instance.heap)
                .then(|| u16::try_from(tag).ok())
                .flatten(),
        }
    }

    /// Whether a type is a record or variants that the program or the standard library declares.
    fn declared(&self, item: &stilt_hir::hir::Item) -> bool {
        self.decls().type_info(item).is_some_and(|info| {
            matches!(info.def, TypeDefInfo::Record(_) | TypeDefInfo::Variants(_))
        })
    }

    /// The types of the fields of `variant` of a declared type, with its arguments.
    fn declared_fields(&self, item: &stilt_hir::hir::Item, variant: usize, args: &[Ty]) -> Vec<Ty> {
        let decls = self.decls();
        let Some(info) = decls.type_info(item) else {
            return Vec::new();
        };
        let inst = |t: &stilt_hir::hir::Ty| instantiate(t, &info.params, args);
        match &info.def {
            TypeDefInfo::Record(fields) => fields.iter().map(|(_, t)| inst(t)).collect(),
            TypeDefInfo::Variants(variants) => variants
                .get(variant)
                .map(|(_, payload)| payload.iter().map(inst).collect())
                .unwrap_or_default(),
            // A view holds its source and its two offsets (`crate::layout`).
            TypeDefInfo::Builtin if is_view_type(item, "View") => {
                vec![
                    args.first().cloned().unwrap_or(Ty::Error),
                    Ty::i64(),
                    Ty::i64(),
                ]
            }
            TypeDefInfo::Builtin => Vec::new(),
        }
    }

    /// The words of a field of a value whose words are `v`, read from its object for a value of
    /// a recursive type.
    pub(crate) fn field_words(&mut self, v: &[Operand], fields: &Fields, j: usize) -> Vec<Operand> {
        let Some(f) = fields.all.get(j) else {
            return vec![Operand::word(0)];
        };
        match &fields.object {
            None => f.at.iter().map(|&p| word(v, p)).collect(),
            Some(object) => {
                let (at, len) = crate::mir::offsets(object.iter().copied());
                let variant = fields.tag.map(|tag| Variant {
                    tag,
                    layout: fixed_layout(object),
                });
                let len = u32::try_from(len).expect("under 4G words");
                f.at.iter()
                    .map(|&p| {
                        let index =
                            u32::try_from(at.get(p).copied().unwrap_or(0)).expect("under 4G words");
                        let base = word(v, 0);
                        let repr = object.get(p).copied().unwrap_or(Repr::Heap);
                        self.b.define_op(
                            repr,
                            Rvalue::Field {
                                base,
                                len,
                                index,
                                variant,
                            },
                        )
                    })
                    .collect()
            }
        }
    }

    /// A value of type `ty`, `variant` of it, from the words of its fields, which it consumes.
    pub(crate) fn build(
        &mut self,
        ty: &Ty,
        variant: usize,
        values: Vec<Vec<Operand>>,
    ) -> Vec<Operand> {
        let fields = self.fields_of(ty, variant);
        let layout = match &fields.object {
            Some(object) => object.clone(),
            None => self.layout(ty),
        };
        let mut words: Vec<Option<Operand>> = vec![None; layout.len()];
        for (f, v) in fields.all.iter().zip(values) {
            for (&p, w) in f.at.iter().zip(v) {
                if let Some(slot) = words.get_mut(p) {
                    *slot = Some(w);
                }
            }
        }
        // A word that the variant doesn't use holds 0, and an array held in memory there zeros.
        let mut words: Vec<Operand> = words
            .into_iter()
            .zip(layout)
            .map(|(w, r)| match (w, r) {
                (Some(w), _) => w,
                (None, Repr::Array(_)) => self.b.define_op(r, Rvalue::Use(Operand::word(0))),
                (None, _) => Operand::word(0),
            })
            .collect();
        let index = u32::try_from(variant).expect("under 4G variants");
        match fields.object {
            Some(_) if fields.tagged && words.is_empty() => vec![Operand::word(immediate(index))],
            Some(object) => {
                let tag = if fields.tagged { index } else { 0 };
                let tag = u16::try_from(tag).expect("under 65536 variants");
                let heapness = object.into_iter().map(Heapness::of);
                vec![self.alloc(tag, words.into_iter().zip(heapness).collect())]
            }
            None => {
                if fields.tagged
                    && let Some(first) = words.first_mut()
                {
                    *first = Operand::word(immediate(index));
                }
                words
            }
        }
    }

    /// The words of a value of type `ty` from the one word that holds it: the word itself, or
    /// the fields of its box, borrowed.
    pub(crate) fn unbox(&mut self, w: Operand, ty: &Ty) -> Vec<Operand> {
        let layout = self.layout(ty);
        if one_word(&layout) {
            return vec![w];
        }
        let (at, len) = crate::mir::offsets(layout.iter().copied());
        let len = u32::try_from(len).expect("under 4G words");
        layout
            .into_iter()
            .zip(at)
            .map(|(repr, at)| {
                let index = u32::try_from(at).expect("under 4G words");
                let base = w.clone();
                self.b.define_op(
                    repr,
                    Rvalue::Field {
                        base,
                        len,
                        index,
                        variant: None,
                    },
                )
            })
            .collect()
    }

    /// [`Self::unbox`] of the box of a parameter that the function borrows, which outlives
    /// the call: the words it reads borrow from the box for as long as they live, as a captured
    /// variable read from a closure does (`stilt-rc`'s copies that borrow).
    pub(crate) fn unbox_lasting(&mut self, param: Local, ty: &Ty) -> Vec<Operand> {
        let words = self.unbox(Operand::Local(param), ty);
        if !self.one_word(ty) {
            for w in &words {
                if let Operand::Local(l) = w {
                    self.b.decl_mut(*l).borrowed = true;
                }
            }
        }
        words
    }

    /// The one word that holds a value of type `ty`, whose words it consumes: its word, or a
    /// new box of its words.
    pub(crate) fn boxed(&mut self, words: Vec<Operand>, ty: &Ty) -> Operand {
        let layout = self.layout(ty);
        let mut words = words.into_iter().chain(std::iter::repeat(Operand::word(0)));
        if one_word(&layout) {
            return words.next().unwrap_or(Operand::word(0));
        }
        let fields = words
            .zip(layout)
            .map(|(w, r)| (w, Heapness::of(r)))
            .collect();
        self.alloc(crate::mir::BOX, fields)
    }

    /// The words of a value of type `ty` that a pointer points to, borrowed.
    pub(crate) fn load_words(&mut self, pointer: &Operand, ty: &Ty) -> Vec<Operand> {
        let layout = self.layout(ty);
        let (at, _) = crate::mir::offsets(layout.iter().copied());
        layout
            .into_iter()
            .zip(at)
            .map(|(repr, at)| {
                let at = self.offset(pointer.clone(), at);
                self.b.define_op(repr, Rvalue::Load(at))
            })
            .collect()
    }

    /// Stores the words of a value of type `ty`, which it consumes, where a pointer points.
    pub(crate) fn store_words(&mut self, pointer: &Operand, words: Vec<Operand>, ty: &Ty) {
        let words = words.into_iter().chain(std::iter::repeat(Operand::word(0)));
        let layout = self.layout(ty);
        let (at, _) = crate::mir::offsets(layout.iter().copied());
        for ((repr, value), at) in layout.into_iter().zip(words).zip(at) {
            let slot = self.offset(pointer.clone(), at);
            self.b.emit(Stmt::Store { slot, value, repr });
        }
    }

    /// A pointer `words` words past `pointer`.
    pub(crate) fn offset(&mut self, pointer: Operand, words: usize) -> Operand {
        if words == 0 {
            return pointer;
        }
        let words = u32::try_from(words).expect("under 4G words");
        self.b
            .define_op(Repr::Scalar, Rvalue::Offset(pointer, words))
    }

    /// The words of a value of type `ty` that holds nothing, which no count reads: each word
    /// 0, and an array held in memory a local whose words are all 0.
    pub(crate) fn zeros(&mut self, ty: &Ty) -> Vec<Operand> {
        self.layout(ty)
            .into_iter()
            .map(|r| match r {
                Repr::Array(_) => self.b.define_op(r, Rvalue::Use(Operand::word(0))),
                _ => Operand::word(0),
            })
            .collect()
    }

    /// Copies of the words of a value into new locals of type `ty`'s layout, one after the
    /// other, which it returns.
    pub(crate) fn copy_into_temps(&mut self, words: Vec<Operand>, ty: &Ty) -> Vec<Local> {
        let locals = self.temps(ty);
        let words = words.into_iter().chain(std::iter::repeat(Operand::word(0)));
        for (&l, w) in locals.iter().zip(words) {
            self.b.assign(l, Rvalue::Use(w));
        }
        locals
    }
}

/// Whether a word of this representation is a heap word, as an operand whose lowest bit tells:
/// 0 or 1, or the witness of a type parameter (`crate::shape`). The words of an array held in
/// memory are no one word, and the code that meets one reads its elements' instead.
pub(crate) fn witness_of(repr: Repr) -> Operand {
    match repr {
        Repr::Scalar | Repr::Array(_) => Operand::word(0),
        Repr::Heap => Operand::word(1),
        Repr::Generic(w) => Operand::Local(w),
    }
}

/// Whether a layout is one word: not several, and not the words of an array held in memory.
pub(crate) fn one_word(layout: &[Repr]) -> bool {
    matches!(layout, [r] if !matches!(r, Repr::Array(_)))
}

/// The operands of locals.
pub(crate) fn operands(locals: &[Local]) -> Vec<Operand> {
    locals.iter().copied().map(Operand::Local).collect()
}

/// The layout word of an object of these words, if the heapness of each is fixed: none holds a
/// type parameter's value or an array.
fn fixed_layout(words: &[Repr]) -> Option<u32> {
    let mut mask = 0u64;
    for (i, r) in words.iter().enumerate() {
        match r {
            Repr::Scalar => {}
            Repr::Heap if i < 64 => mask |= 1 << i,
            _ => return None,
        }
    }
    Some(crate::mir::data_layout(words.len(), mask))
}
