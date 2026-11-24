//! Structural impls (traits.structural-impls): equality, order, hashing and text, made from the
//! impls of a value's components, which they call from the first component to the last, so that the
//! calls they make are fixed. Each takes the values it compares in the words of their layout.

use stilt_hir::decls::{Lookup, TypeDefInfo, prelude_item};
use stilt_hir::hir::{Item, Name};
use stilt_types::ty::Ty;

mod arrays;
mod runtime;

use super::{shape_params, shape_type};
use crate::FnRef;
use crate::items::Shape;
use crate::lower::dicts::PRELUDE_TRAITS;
use crate::lower::traits::{EQUAL, GREATER, LESS};
use crate::lower::words::word;
use crate::lower::{Cx, Lower};
use crate::mir::{
    BlockId, Const, Function, NumKind, Operand, ParamMode, Prim, Repr, Runtime, Rvalue, Terminator,
};

/// What a value of the impl's type holds: one tuple of fields, or variants each with a
/// payload, the number of its fields.
enum Parts {
    Fields(Option<Name>),
    Variants(Vec<(Name, usize)>),
    /// A list or a map, whose impls are the runtime's.
    Builtin(Item),
    /// An array's elements, compared, hashed and shown in order, and written as a list is
    /// (generics.array-traits).
    Array,
}

/// The words of the values a structural impl's method takes, and their type.
struct Values<'v> {
    ty: &'v Ty,
    a: &'v [Operand],
    b: &'v [Operand],
}

pub(super) fn structural(
    cx: &Cx<'_>,
    f: &FnRef,
    t: &Item,
    name: Name,
    shape: &Shape,
) -> Option<Function> {
    let decls = cx.decls();
    let params = shape_params(&decls, shape);
    let mut lower = Lower::new(cx, f.clone(), true);
    let pack = matches!(shape, Shape::Con(item) if crate::lower::packs::has_pack(&decls, item));
    for (i, param) in params.iter().enumerate() {
        let traits: Vec<Item> = PRELUDE_TRAITS.iter().map(|n| prelude_item(n)).collect();
        if pack && i + 1 == params.len() {
            lower.add_type_pack(param, &traits);
        } else {
            lower.add_generic(Ty::Param(param.clone()), &traits);
        }
    }
    let ty = lower.cons.ty(&shape_type(shape, &params));
    let binary = matches!(&*name, "eq" | "compare");
    let mut words = || -> Vec<Operand> {
        lower
            .layout(&ty)
            .into_iter()
            .map(|r| Operand::Local(lower.b.param(r, ParamMode::Borrowed, None)))
            .collect()
    };
    let first = words();
    let second = if binary { words() } else { Vec::new() };
    lower.ret = crate::lower::Conv::of(Ty::bool());
    let value = if crate::lower::traits::primitive(&ty) {
        let args = std::iter::once(word(&first, 0))
            .chain(binary.then(|| word(&second, 0)))
            .collect();
        let loc = Operand::Local(lower.loc);
        lower.primitive_trait(t, &name, &ty, args, loc)
    } else if *shape == Shape::Pack {
        let v = Values {
            ty: &ty,
            a: &first,
            b: &second,
        };
        lower.pack_method(&name, &v)
    } else if ty.viewed().is_some() {
        // views.functions-of-views: a view's impls are the viewed type's, on the viewed part.
        let values: &[&[Operand]] = if binary {
            &[&first, &second]
        } else {
            &[&first]
        };
        lower.view_trait(&name, &ty, values)
    } else {
        let parts = parts(&decls, shape, &ty)?;
        let v = Values {
            ty: &ty,
            a: &first,
            b: &second,
        };
        match &*name {
            "eq" => lower.structural_eq(&parts, &v),
            "compare" => lower.structural_compare(&parts, &v),
            "hash" => lower.structural_hash(&parts, &v),
            _ => lower.structural_show(&parts, &v),
        }
    };
    lower.b.terminate(Terminator::Return(vec![value]));
    Some(lower.into_function())
}

fn parts(decls: &dyn Lookup, shape: &Shape, ty: &Ty) -> Option<Parts> {
    let item = match (shape, ty) {
        (Shape::Tuple(_), Ty::Tuple(_)) => return Some(Parts::Fields(None)),
        (_, Ty::Con(item, _)) => item,
        _ => return None,
    };
    let info = decls.type_info(item)?;
    Some(match &info.def {
        TypeDefInfo::Record(_) => Parts::Fields(Some(item.name)),
        TypeDefInfo::Variants(variants) => Parts::Variants(
            variants
                .iter()
                .map(|(n, payload)| (*n, payload.len()))
                .collect(),
        ),
        TypeDefInfo::Builtin if stilt_types::ty::is_array(item) => Parts::Array,
        TypeDefInfo::Builtin => Parts::Builtin(item.clone()),
    })
}

impl Lower<'_> {
    fn here(&self) -> Operand {
        Operand::Local(self.loc)
    }

    /// The words of each field of `variant` of a value, the first of `v`'s values if `first`.
    fn parts_of(&mut self, v: &Values<'_>, variant: usize, first: bool) -> Vec<(Ty, Vec<Operand>)> {
        let fields = self.fields_of(v.ty, variant);
        let words = if first { v.a } else { v.b };
        (0..fields.all.len())
            .map(|j| {
                (
                    fields.all[j].ty.clone(),
                    self.field_words(words, &fields, j),
                )
            })
            .collect()
    }

    /// The dictionaries of the element types of a list or a map for `trait_name`, as the
    /// runtime's impls of them take them.
    fn element_dicts(&mut self, trait_name: &str) -> Vec<Operand> {
        let t = prelude_item(trait_name);
        self.generics
            .clone()
            .iter()
            .map(|(ty, _)| self.dict(ty, &t))
            .collect()
    }

    /// The index of the variant a value is, from its tag word or its object.
    fn tag_of(&mut self, words: &[Operand]) -> Operand {
        self.b.define_op(Repr::Scalar, Rvalue::Tag(word(words, 0)))
    }

    /// One block per variant, which the code switches to on the tag. A type without variants, which
    /// only a declaration with a syntax error has (program.syntax-errors-at-run), has no values, so
    /// the code is never reached.
    fn by_variant(&mut self, tag: Operand, variants: usize) -> Vec<BlockId> {
        if variants == 0 {
            self.b.terminate(Terminator::Unreachable);
            return Vec::new();
        }
        let blocks: Vec<BlockId> = (0..variants).map(|_| self.b.new_block()).collect();
        let cases = blocks
            .iter()
            .enumerate()
            .map(|(i, b)| (i as u64, *b))
            .collect();
        self.b.terminate(Terminator::Switch {
            value: tag,
            cases,
            otherwise: blocks[0],
        });
        blocks
    }

    fn structural_eq(&mut self, parts: &Parts, v: &Values<'_>) -> Operand {
        let result = self.b.temp(Repr::Scalar);
        let (unequal, join) = (self.b.new_block(), self.b.new_block());
        match parts {
            Parts::Fields(..) | Parts::Array => {
                self.eq_fields(v, 0, unequal);
                self.b.assign(result, Rvalue::Use(Operand::word(1)));
                self.b.goto(join);
            }
            Parts::Variants(variants) => {
                let (ta, tb) = (self.tag_of(v.a), self.tag_of(v.b));
                let same = self.b.define_op(
                    Repr::Scalar,
                    Rvalue::Prim(Prim::WordEq, vec![ta.clone(), tb], self.here()),
                );
                let next = self.b.new_block();
                self.b.branch(same, next, unequal);
                self.b.switch_to(next);
                let blocks = self.by_variant(ta, variants.len());
                for (i, block) in blocks.into_iter().enumerate() {
                    self.b.switch_to(block);
                    self.eq_fields(v, i, unequal);
                    self.b.assign(result, Rvalue::Use(Operand::word(1)));
                    self.b.goto(join);
                }
            }
            Parts::Builtin(item) => {
                let value = self.builtin(item, "eq", v);
                self.b.assign(result, Rvalue::Use(value));
                self.b.goto(join);
            }
        }
        self.b.switch_to(unequal);
        self.b.assign(result, Rvalue::Use(Operand::word(0)));
        self.b.goto(join);
        self.b.switch_to(join);
        Operand::Local(result)
    }

    /// Compares the fields of `variant` with `eq`, going to `unequal` at the first unequal
    /// pair.
    fn eq_fields(&mut self, v: &Values<'_>, variant: usize, unequal: BlockId) {
        if let Some(parts) = self.in_memory_parts(v.ty) {
            return self.eq_elements(v, parts, unequal);
        }
        let xs = self.parts_of(v, variant, true);
        let ys = self.parts_of(v, variant, false);
        for ((t, x), (_, y)) in xs.into_iter().zip(ys) {
            let here = self.here();
            let eq = self.trait_call("Eq", "eq", &t, vec![x, y], here);
            let next = self.b.new_block();
            self.b.branch(eq, next, unequal);
            self.b.switch_to(next);
        }
    }

    fn structural_compare(&mut self, parts: &Parts, v: &Values<'_>) -> Operand {
        let result = self.b.temp(Repr::Scalar);
        let join = self.b.new_block();
        match parts {
            Parts::Fields(..) | Parts::Array => self.compare_fields(v, 0, result, join),
            Parts::Variants(variants) => {
                let (ta, tb) = (self.tag_of(v.a), self.tag_of(v.b));
                let order = self.b.define_op(
                    Repr::Scalar,
                    Rvalue::Prim(
                        Prim::Compare(NumKind::U64),
                        vec![ta.clone(), tb],
                        self.here(),
                    ),
                );
                let same = self.b.define_op(
                    Repr::Scalar,
                    Rvalue::Prim(
                        Prim::WordEq,
                        vec![order.clone(), Operand::word(EQUAL)],
                        self.here(),
                    ),
                );
                let (next, differ) = (self.b.new_block(), self.b.new_block());
                self.b.branch(same, next, differ);
                self.b.switch_to(differ);
                self.b.assign(result, Rvalue::Use(order));
                self.b.goto(join);
                self.b.switch_to(next);
                let blocks = self.by_variant(ta, variants.len());
                for (i, block) in blocks.into_iter().enumerate() {
                    self.b.switch_to(block);
                    self.compare_fields(v, i, result, join);
                }
            }
            Parts::Builtin(item) => {
                let value = self.builtin(item, "compare", v);
                self.b.assign(result, Rvalue::Use(value));
                self.b.goto(join);
            }
        }
        self.b.switch_to(join);
        Operand::Local(result)
    }

    /// Compares the fields of `variant` lexicographically, with `compare`, into `result`.
    fn compare_fields(
        &mut self,
        v: &Values<'_>,
        variant: usize,
        result: crate::mir::Local,
        join: BlockId,
    ) {
        if let Some(parts) = self.in_memory_parts(v.ty) {
            return self.compare_elements(v, parts, (result, join));
        }
        let xs = self.parts_of(v, variant, true);
        let ys = self.parts_of(v, variant, false);
        for ((t, x), (_, y)) in xs.into_iter().zip(ys) {
            let here = self.here();
            let order = self.trait_call("Ord", "compare", &t, vec![x, y], here);
            self.b.assign(result, Rvalue::Use(order.clone()));
            let same = self.b.define_op(
                Repr::Scalar,
                Rvalue::Prim(Prim::WordEq, vec![order, Operand::word(EQUAL)], self.here()),
            );
            let next = self.b.new_block();
            self.b.branch(same, next, join);
            self.b.switch_to(next);
        }
        self.b.assign(result, Rvalue::Use(Operand::word(EQUAL)));
        self.b.goto(join);
        let _ = (LESS, GREATER);
    }

    fn structural_hash(&mut self, parts: &Parts, v: &Values<'_>) -> Operand {
        let start = self.b.define_op(
            Repr::Scalar,
            Rvalue::Runtime(Runtime::HashStart, Vec::new()),
        );
        match parts {
            Parts::Fields(..) | Parts::Array => self.hash_fields(v, 0, start),
            Parts::Variants(variants) => {
                let result = self.b.temp(Repr::Scalar);
                let join = self.b.new_block();
                let tag = self.tag_of(v.a);
                let h = self.b.define_op(
                    Repr::Scalar,
                    Rvalue::Runtime(Runtime::HashMix, vec![start, tag.clone()]),
                );
                let blocks = self.by_variant(tag, variants.len());
                for (i, block) in blocks.into_iter().enumerate() {
                    self.b.switch_to(block);
                    let value = self.hash_fields(v, i, h.clone());
                    self.b.assign(result, Rvalue::Use(value));
                    self.b.goto(join);
                }
                self.b.switch_to(join);
                Operand::Local(result)
            }
            Parts::Builtin(item) => self.builtin(item, "hash", v),
        }
    }

    fn hash_fields(&mut self, v: &Values<'_>, variant: usize, mut h: Operand) -> Operand {
        if let Some(parts) = self.in_memory_parts(v.ty) {
            return self.hash_elements(v, parts, h);
        }
        for (t, x) in self.parts_of(v, variant, true) {
            let here = self.here();
            let hx = self.trait_call("Hash", "hash", &t, vec![x], here);
            h = self
                .b
                .define_op(Repr::Scalar, Rvalue::Runtime(Runtime::HashMix, vec![h, hx]));
        }
        h
    }

    fn structural_show(&mut self, parts: &Parts, v: &Values<'_>) -> Operand {
        match parts {
            Parts::Fields(name) => {
                let pieces = self.show_fields(v, 0, name.as_deref(), true);
                self.concat(pieces)
            }
            Parts::Variants(variants) => {
                let result = self.b.temp(Repr::Heap);
                let join = self.b.new_block();
                let tag = self.tag_of(v.a);
                let blocks = self.by_variant(tag, variants.len());
                for (i, (block, (name, payload))) in blocks.into_iter().zip(variants).enumerate() {
                    self.b.switch_to(block);
                    let value = if *payload == 0 {
                        Operand::Const(Const::Str((*name).into()))
                    } else {
                        let pieces = self.show_fields(v, i, Some(name), false);
                        self.concat(pieces)
                    };
                    self.b.assign(result, Rvalue::Use(value));
                    self.b.goto(join);
                }
                self.b.switch_to(join);
                Operand::Local(result)
            }
            Parts::Builtin(item) => self.builtin(item, "show", v),
            Parts::Array => {
                if let Some(parts) = self.in_memory_parts(v.ty) {
                    return self.show_array_elements(v, parts);
                }
                let pieces = self.show_elements(v);
                self.concat(pieces)
            }
        }
    }

    /// The pieces of a value's text (std.show-output): `Name { f: v }` for a record, `Name(v)`
    /// for a variant, and `(v, w)` or `(v,)` for a tuple.
    fn show_fields(
        &mut self,
        v: &Values<'_>,
        variant: usize,
        name: Option<&str>,
        record: bool,
    ) -> Vec<Operand> {
        let field_names = match (name, record) {
            (Some(_), true) => self.record_field_names(),
            _ => Vec::new(),
        };
        let xs = self.parts_of(v, variant, true);
        let text = |s: &str| Operand::Const(Const::Str(s.into()));
        let mut parts = Vec::new();
        let (open, close) = match (name, record) {
            (Some(n), true) if xs.is_empty() => return vec![text(&format!("{n} {{}}"))],
            // An anonymous record has no name to show (records.field-order).
            (Some(_), true) if self.is_anonymous() => ("{ ".to_owned(), " }"),
            (Some(n), true) => (format!("{n} {{ "), " }"),
            (Some(n), false) => (format!("{n}("), ")"),
            (None, _) => ("(".to_owned(), if xs.len() == 1 { ",)" } else { ")" }),
        };
        parts.push(text(&open));
        for (i, (t, x)) in xs.into_iter().enumerate() {
            if i > 0 {
                parts.push(text(", "));
            }
            if let Some(f) = field_names.get(i) {
                parts.push(text(&format!("{f}: ")));
            }
            let here = self.here();
            parts.push(self.trait_call("Show", "show_nested", &t, vec![x], here));
        }
        parts.push(text(close));
        parts
    }

    /// The pieces of an array's text, as a list's: `[v, w]` (generics.array-traits).
    fn show_elements(&mut self, v: &Values<'_>) -> Vec<Operand> {
        let text = |s: &str| Operand::Const(Const::Str(s.into()));
        let mut parts = vec![text("[")];
        for (i, (t, x)) in self.parts_of(v, 0, true).into_iter().enumerate() {
            if i > 0 {
                parts.push(text(", "));
            }
            let here = self.here();
            parts.push(self.trait_call("Show", "show_nested", &t, vec![x], here));
        }
        parts.push(text("]"));
        parts
    }

    /// Whether this structural impl is an anonymous record type's.
    fn is_anonymous(&self) -> bool {
        matches!(
            self.b.name().generic(),
            FnRef::Structural(_, _, Shape::Con(item)) if item.is_record()
        )
    }

    /// The names of the fields of the record type this structural impl is for.
    fn record_field_names(&self) -> Vec<Name> {
        let FnRef::Structural(_, _, Shape::Con(item)) = self.b.name().generic() else {
            return Vec::new();
        };
        self.field_names(item)
    }
}
