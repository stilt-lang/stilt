//! The places whose path goes through an index that the words at its end can't be reached
//! through by a pointer: a map's, whose key type's `hash` and `eq` it calls, so the place is
//! read and written back as the interpreter does, once each; and a list's element held in
//! fewer bytes than its words, as a narrow scalar is, or by its shape when the code runs, as a
//! value of a type parameter is (`super::super::lists`).

use stilt_types::ty::Ty;

use super::super::Lower;
use super::super::lists::Elem;
use super::super::words::word;
use super::{Place, Root, Step};
use crate::mir::{BOX, Operand, Repr, Runtime, Rvalue, Stmt};

/// The value before a step of a place: its words, or a pointer to them that nothing has read.
type Before = Result<Vec<Operand>, Operand>;

impl Lower<'_> {
    /// Stores `value` at a place whose step `at` indexes a map, as the interpreter stores it:
    /// the value there read, changed by the rest of the path, and inserted back.
    pub(super) fn store_through_map(&mut self, place: &Place, at: usize, value: Vec<Operand>) {
        let root = self.root_slot(&place.root);
        let map_slot = self.walk(root, place, at);
        let Step::Index {
            container,
            key,
            loc,
            ..
        } = &place.steps[at]
        else {
            unreachable!("a map's index")
        };
        let value_ty = &place.types[at + 1];
        let inner = if at + 1 == place.steps.len() {
            self.map_word(value, value_ty)
        } else {
            let map = self.b.define_op(Repr::Heap, Rvalue::Load(map_slot.clone()));
            let current = self.index_value(container, map, key.clone(), loc.clone(), value_ty);
            let temps = self.copy_into_temps(current, value_ty);
            let rest = Place {
                root: Root::Locals(temps.clone()),
                steps: place.steps[at + 1..].to_vec(),
                types: place.types[at + 1..].to_vec(),
            };
            self.store_place(&rest, value);
            let words = self.read_locals(&temps);
            self.map_word(words, value_ty)
        };
        let key_ty = key_ty(container);
        let k = self.map_word(key.clone(), &key_ty);
        let (eq, hash) = self.key_dicts(&key_ty);
        self.b.emit(Stmt::Effect(
            Runtime::MapStore,
            vec![loc.clone(), eq, hash, map_slot, k, inner],
        ));
    }

    /// The words of a place whose step `k` indexes a list that holds its elements inline, in
    /// whole words, and whose later steps are fields held inline, read from that part of the
    /// element alone. `before` is the value before step `k`, its words or a pointer to them,
    /// and is given back for any other place.
    pub(super) fn read_list_part(
        &mut self,
        place: &Place,
        k: usize,
        before: Before,
    ) -> Result<Vec<Operand>, Before> {
        let Some(Step::Index {
            container,
            key,
            loc,
        }) = place.steps.get(k)
        else {
            return Err(before);
        };
        if container.is_prelude("Map") || container.is_view() || k + 1 == place.steps.len() {
            return Err(before);
        }
        let Some(mut part) = self.part_of_element(&place.types[k + 1]) else {
            return Err(before);
        };
        for s in &place.steps[k + 1..] {
            let Step::Inline { offset, len, .. } = s else {
                return Err(before);
            };
            part.start += offset;
            part.len = *len;
        }
        let list = match before {
            Ok(v) => word(&v, 0),
            Err(p) => self.b.define_op(Repr::Heap, Rvalue::Load(p)),
        };
        Ok(self.read_part((&list, &word(key, 0)), loc.clone(), &part))
    }

    /// Whether the words at the end of a place are whole words that a pointer reaches: not a
    /// list's element held in fewer bytes, or by its shape when the code runs.
    pub(super) fn whole_words_at_end(&mut self, place: &Place) -> bool {
        !matches!(self.list_end(place), Some(e) if e.packed() || matches!(e, Elem::Dynamic(_)))
    }

    /// How the list that the last step of a place indexes holds its elements, if it does.
    fn list_end(&mut self, place: &Place) -> Option<Elem> {
        match place.steps.last() {
            Some(Step::Index { container, .. }) if !container.is_prelude("Map") => {
                Some(self.elem(place.ty()))
            }
            _ => None,
        }
    }

    /// Stores `value` at a place whose last step indexes a list that holds an element in
    /// fewer bytes than its words, or by its shape when the code runs, and tells whether it
    /// did: a narrow scalar is stored in its width, and a value of a type parameter by the
    /// runtime, which converts its word.
    pub(super) fn store_list_end(&mut self, place: &Place, value: &[Operand]) -> bool {
        let Some(elem) = self.list_end(place) else {
            return false;
        };
        let n = place.steps.len();
        let Some(Step::Index { key, loc, .. }) = place.steps.last() else {
            return false;
        };
        let (key, loc) = (word(key, 0), loc.clone());
        match elem {
            Elem::Inline { shape, .. } if elem.packed() => {
                let root = self.root_slot(&place.root);
                let slot = self.walk(root, place, n);
                let args = vec![slot, word(value, 0), Operand::word(shape)];
                self.b.emit(Stmt::Effect(Runtime::StorePacked, args));
            }
            // An element of a view's source, whose count isn't checked
            // (projections.places-through-views).
            Elem::Dynamic(_) if place.ty_before_end().is_view() => {
                let root = self.root_slot(&place.root);
                let slot = self.walk(root, place, n - 1);
                self.view_put(place, &slot, word(value, 0));
            }
            Elem::Dynamic(_) => {
                let root = self.root_slot(&place.root);
                let slot = self.walk(root, place, n - 1);
                let args = vec![loc, slot, key, word(value, 0)];
                self.b.emit(Stmt::Effect(Runtime::ListPut, args));
            }
            Elem::Inline { .. } => return false,
        }
        true
    }
}

impl Lower<'_> {
    /// The one word in which the runtime's functions of maps take a key or a value of type
    /// `ty`, whose words it consumes: the word that holds it where a type parameter stands, or
    /// for a value of several words, a box of them in slots of the function's frame, which hold
    /// their references until they are written again or the function ends (`stilt_runtime`'s
    /// `map`).
    pub(crate) fn map_word(&mut self, held: Vec<Operand>, ty: &Ty) -> Operand {
        let reprs = self.layout(ty);
        if super::super::words::one_word(&reprs) {
            return word(&held, 0);
        }
        let n = crate::mir::offsets(reprs.iter().copied()).1 as u64;
        let header = [self.b.temp(Repr::Scalar), self.b.temp(Repr::Scalar)];
        let words: Vec<_> = reprs.into_iter().map(|r| self.b.temp(r)).collect();
        self.b
            .assign(header[0], Rvalue::Use(Operand::word(u64::from(BOX) << 48)));
        let layout = crate::mir::data_layout(usize::try_from(n).expect("under 2^63 words"), 0);
        self.b
            .assign(header[1], Rvalue::Use(Operand::word(u64::from(layout))));
        for (&l, w) in words.iter().zip(held) {
            self.b.assign(l, Rvalue::Use(w));
        }
        let all: Vec<_> = header.into_iter().chain(words).collect();
        self.b.make_slots(&all);
        self.b.define_op(Repr::Scalar, Rvalue::SlotOf(all[0]))
    }

    /// The words that hold a key, or a value if `value` is set, of type `ty` of a map, which a
    /// pointer that the map gave points to, borrowed from the map. A type parameter held in one
    /// word is read through the runtime, by the map's shape, with references of its own, since
    /// past the caps of instances a value of several words is held in its box.
    pub(crate) fn map_words(
        &mut self,
        map: &Operand,
        pointer: &Operand,
        ty: &Ty,
        value: bool,
    ) -> Vec<Operand> {
        let held = self.layout(ty);
        if let [repr @ Repr::Generic(_)] = held.as_slice() {
            let args = vec![
                map.clone(),
                pointer.clone(),
                Operand::word(u64::from(value)),
            ];
            return vec![
                self.b
                    .define_op(*repr, Rvalue::Runtime(Runtime::MapHeld, args)),
            ];
        }
        let (at, _) = crate::mir::offsets(held.iter().copied());
        held.into_iter()
            .zip(at)
            .map(|(repr, i)| {
                let args = vec![map.clone(), pointer.clone(), Operand::word(i as u64)];
                self.b
                    .define_op(repr, Rvalue::Runtime(Runtime::MapWord, args))
            })
            .collect()
    }
}

/// The key type of a map.
pub(crate) fn key_ty(container: &Ty) -> Ty {
    match container {
        Ty::Con(_, args) => args.first().cloned().unwrap_or(Ty::Error),
        _ => Ty::Error,
    }
}
