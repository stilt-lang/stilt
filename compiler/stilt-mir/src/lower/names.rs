//! The names a debugger shows the words of a named value by (goal debuggable-builds): a value of
//! one word under the source's name, and the words of a value held inline each under a name
//! that says which part it is: `p.x` for a record's field, `t.0` for a tuple's element, and for
//! a variant type, the tag under the value's own name, shown as the variant's name, then the
//! payload's words, `o.0`, `o.1` and so on. An array held in memory is one word under its own
//! name, shown element by element (generics.large-arrays).

use std::sync::Arc;

use stilt_hir::decls::{Lookup, TypeDefInfo};
use stilt_hir::hir::Name;
use stilt_types::ty::Ty;

use super::Lower;
use crate::mir::{Local, Repr, Shown, ShownElements, ShownKind};
use crate::repr::{shown, write_type};

/// A word of a named value: how it is held, and what a debugger shows it as.
pub(crate) struct Word {
    pub(crate) repr: Repr,
    pub(crate) name: Option<Name>,
    pub(crate) shown: Option<Shown>,
}

impl Lower<'_> {
    /// The words of a value of type `ty` that the source names `name`, if it does.
    pub(crate) fn words_named(&self, name: Option<&Name>, ty: &Ty, by_ref: bool) -> Vec<Word> {
        let layout = self.layout(ty);
        let Some(name) = name else {
            return layout
                .into_iter()
                .map(|repr| Word {
                    repr,
                    name: None,
                    shown: None,
                })
                .collect();
        };
        let shown = self.shown_words(ty, by_ref);
        let names = self.part_names(*name, ty);
        layout
            .into_iter()
            .zip(names)
            .zip(shown)
            .map(|((repr, name), shown)| Word {
                repr,
                name: Some(name),
                shown: Some(shown),
            })
            .collect()
    }

    /// New locals for the words of a value of type `ty` that the source names `name`.
    pub(crate) fn named_locals(
        &mut self,
        name: Option<&Name>,
        ty: &Ty,
        by_ref: bool,
    ) -> Vec<Local> {
        self.words_named(name, ty, by_ref)
            .into_iter()
            .map(|w| {
                let l = self.b.local(w.repr, w.name);
                self.b.decl_mut(l).shown = w.shown;
                l
            })
            .collect()
    }

    /// The names of the words of a value of type `ty` named `name`.
    fn part_names(&self, name: Name, ty: &Ty) -> Vec<Name> {
        let n = self.layout(ty).len();
        if n == 1 && !self.tagged(ty) {
            return vec![name];
        }
        if matches!(ty, Ty::Param(_) | Ty::SelfTy) {
            // An instance holds a value of a type parameter in the words of its argument's
            // layout, which it knows by position only.
            return (0..n).map(|i| format!("{name}.{i}").into()).collect();
        }
        if self.tagged(ty) {
            return std::iter::once(name)
                .chain((0..n - 1).map(|i| format!("{name}.{i}").into()))
                .collect();
        }
        let labels = self.field_labels(ty);
        let fields = self.fields_of(ty, 0);
        let mut out = Vec::with_capacity(n);
        let array = ty.arrayed().is_some();
        for (f, label) in fields.all.iter().zip(labels) {
            // An array's element is named as the source reads it (generics.array-elements).
            let part: Name = if array {
                format!("{name}[{label}]").into()
            } else {
                format!("{name}.{label}").into()
            };
            if f.at.len() == 1 {
                out.push(part);
            } else {
                out.extend(self.part_names(part, &f.ty));
            }
        }
        out
    }

    /// The labels of the fields of a record or a tuple: their names, or their positions.
    fn field_labels(&self, ty: &Ty) -> Vec<String> {
        match ty {
            Ty::Tuple(ts) => (0..ts.len()).map(|i| i.to_string()).collect(),
            Ty::Con(..) if ty.arrayed().is_some() => (0..self.fields_of(ty, 0).all.len())
                .map(|i| i.to_string())
                .collect(),
            Ty::Con(item, _) => self
                .field_names(item)
                .iter()
                .map(ToString::to_string)
                .collect(),
            _ => Vec::new(),
        }
    }

    /// Whether a type is a variant type held inline, whose first word is its tag.
    fn tagged(&self, ty: &Ty) -> bool {
        matches!(ty, Ty::Con(item, _) if !self.templates.heap(item) && self.templates.of(item).tagged)
    }

    /// What a debugger shows each word of a value of type `ty` as.
    fn shown_words(&self, ty: &Ty, by_ref: bool) -> Vec<Shown> {
        let n = self.layout(ty).len();
        if self.tagged(ty) {
            let mut out = vec![None; n];
            out[0] = Some(self.tag_shown(ty));
            self.payload_shown(ty, &mut out);
            return out
                .into_iter()
                .map(|s| s.unwrap_or_else(|| shown(&Ty::unit(), false)))
                .collect();
        }
        if n == 1 {
            return vec![self.word_shown(ty, by_ref)];
        }
        if matches!(ty, Ty::Param(_) | Ty::SelfTy) {
            return vec![shown(ty, false); n];
        }
        let fields = self.fields_of(ty, 0);
        let mut out = Vec::with_capacity(n);
        for f in &fields.all {
            if f.at.len() == 1 {
                out.push(self.word_shown(&f.ty, false));
            } else {
                out.extend(self.shown_words(&f.ty, false));
            }
        }
        out
    }

    /// What a debugger shows the one word of a value of type `ty` as: an array held in memory
    /// element by element, and any other value as its type says.
    fn word_shown(&self, ty: &Ty, by_ref: bool) -> Shown {
        let (Some(e), Some((elem, _))) = (self.array_in_memory(ty), ty.arrayed()) else {
            return shown(ty, by_ref);
        };
        let names = self.part_names(Name::from(""), elem);
        let words = names
            .into_iter()
            .map(|n| Arc::from(&*n))
            .zip(self.shown_words(elem, false))
            .collect();
        let mut name = String::new();
        write_type(&mut name, elem);
        Shown {
            kind: ShownKind::Array,
            elements: Some(ShownElements {
                name: name.into(),
                len: e.len(),
                words,
            }),
            ..shown(ty, by_ref)
        }
    }

    /// How a debugger shows a variant type's tag: as the name of the variant it stands for.
    fn tag_shown(&self, ty: &Ty) -> Shown {
        let Ty::Con(item, _) = ty else {
            return shown(ty, false);
        };
        let variants: Vec<Arc<str>> = match self.decls().type_info(item).map(|t| &t.def) {
            Some(TypeDefInfo::Variants(vs)) => vs.iter().map(|(n, _)| Arc::from(&**n)).collect(),
            _ => Vec::new(),
        };
        let mut name = String::new();
        write_type(&mut name, ty);
        Shown {
            name: name.into(),
            kind: ShownKind::Tag,
            by_ref: false,
            variants: variants.into(),
            elements: None,
        }
    }

    /// How a debugger shows each word of a variant type's payloads that `out` doesn't show yet:
    /// as the first field that uses it shows it.
    fn payload_shown(&self, ty: &Ty, out: &mut [Option<Shown>]) {
        let Ty::Con(item, _) = ty else {
            return;
        };
        let count = self.templates.of(item).variants.len();
        for v in 0..count {
            let fields = self.fields_of(ty, v);
            for f in &fields.all {
                if f.at
                    .iter()
                    .all(|&at| out.get(at).is_none_or(Option::is_some))
                {
                    continue;
                }
                let words = if f.at.len() == 1 {
                    vec![self.word_shown(&f.ty, false)]
                } else {
                    self.shown_words(&f.ty, false)
                };
                for (&at, word) in f.at.iter().zip(words) {
                    if let Some(slot @ None) = out.get_mut(at) {
                        *slot = Some(word);
                    }
                }
            }
        }
    }
}
