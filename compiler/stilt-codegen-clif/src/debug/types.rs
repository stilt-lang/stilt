//! The DWARF types of the words that a debugger shows (`Shown`), which a build writes once in
//! its unit, after the functions whose locals have them ([`super::assemble`]): an integer, a
//! float or a `bool` as its value, a variant type's tag as the name of its variant, an array
//! held in memory element by element, and any other value as a pointer to its object, whose
//! header a debugger can show, and for a string, its length and bytes.
//!
//! Each type is written after the types it names, so that every reference in the area points
//! back to an entry already written, at its offset in the unit.

use gimli::constants::{self as dw, DwAte};
use rustc_hash::FxHashMap as HashMap;
use stilt_mir::mir::{Shown, ShownKind};

use super::encode::{self, Bytes};

/// The types of a unit, each written once, at offsets from `base` in the unit.
pub(super) struct Types<'a> {
    base: u32,
    pub(super) out: Bytes,
    shown: HashMap<&'a Shown, u32>,
    bases: HashMap<(&'static str, DwAte, u8), u32>,
    objects: Option<(u32, u32)>,
}

impl<'a> Types<'a> {
    pub(super) fn new(base: u32) -> Self {
        Self {
            base,
            out: Bytes::default(),
            shown: HashMap::default(),
            bases: HashMap::default(),
            objects: None,
        }
    }

    /// The offset in the unit of the entry that starts here.
    fn here(&self) -> u32 {
        self.base + u32::try_from(self.out.len()).unwrap_or(u32::MAX)
    }

    /// The type a debugger shows a word by, at its offset in the unit.
    pub(super) fn of(&mut self, shown: &'a Shown) -> u32 {
        if let Some(&at) = self.shown.get(shown) {
            return at;
        }
        // A debugger may show a base type by the C type of its size, so a typedef keeps the
        // type's own name.
        let value = match shown.kind {
            ShownKind::Signed(_) => {
                let base = self.base("long", dw::DW_ATE_signed, 8);
                self.typedef(&shown.name, base)
            }
            ShownKind::Unsigned(_) | ShownKind::Opaque => {
                let base = self.base("unsigned long", dw::DW_ATE_unsigned, 8);
                self.typedef(&shown.name, base)
            }
            ShownKind::Float(bits) => {
                let (name, size) = if bits == 32 {
                    ("float", 4)
                } else {
                    ("double", 8)
                };
                let base = self.base(name, dw::DW_ATE_float, size);
                self.typedef(&shown.name, base)
            }
            ShownKind::Bool => {
                let base = self.base("bool", dw::DW_ATE_boolean, 1);
                self.typedef(&shown.name, base)
            }
            ShownKind::Str | ShownKind::Heap => {
                let (object, string) = self.objects();
                let target = if shown.kind == ShownKind::Str {
                    string
                } else {
                    object
                };
                let pointer = self.pointer(target);
                self.typedef(&shown.name, pointer)
            }
            ShownKind::Tag => self.enumeration(shown),
            ShownKind::Array => self.array(shown),
        };
        let at = if shown.by_ref {
            self.pointer(value)
        } else {
            value
        };
        self.shown.insert(shown, at);
        at
    }

    /// A base type of the runtime's layout, written once.
    fn base(&mut self, name: &'static str, encoding: DwAte, size: u8) -> u32 {
        if let Some(&at) = self.bases.get(&(name, encoding, size)) {
            return at;
        }
        let at = self.here();
        self.out.uleb(encode::BASE);
        self.out.string(name);
        self.out.u8(encoding.0);
        self.out.u8(size);
        self.bases.insert((name, encoding, size), at);
        at
    }

    fn pointer(&mut self, target: u32) -> u32 {
        let at = self.here();
        self.out.uleb(encode::POINTER);
        self.out.u8(8);
        self.out.u32(target);
        at
    }

    fn typedef(&mut self, name: &str, target: u32) -> u32 {
        let at = self.here();
        self.out.uleb(encode::TYPEDEF);
        self.out.string(name);
        self.out.u32(target);
        at
    }

    /// The type of a variant type's tag word, whose values are the immediates of its variants'
    /// indexes, each shown by the variant's name.
    fn enumeration(&mut self, shown: &Shown) -> u32 {
        let base = self.base("unsigned long", dw::DW_ATE_unsigned, 8);
        let at = self.here();
        self.out.uleb(encode::ENUMERATION);
        self.out.string(&shown.name);
        self.out.u8(8);
        self.out.u32(base);
        for (i, variant) in (0u64..).zip(shown.variants.iter()) {
            self.out.uleb(encode::ENUMERATOR);
            self.out.string(variant);
            self.out.uleb(i << 1 | 1);
        }
        self.out.u8(0);
        at
    }

    /// The type of an array held in memory (generics.large-arrays): its elements one after the
    /// other, each of the type of its one word, or a structure of its words, each under the name of
    /// the part of the element that it holds.
    fn array(&mut self, shown: &'a Shown) -> u32 {
        let Some(elements) = &shown.elements else {
            let base = self.base("unsigned long", dw::DW_ATE_unsigned, 8);
            return self.typedef(&shown.name, base);
        };
        let element = match &*elements.words {
            [(part, word)] if part.is_empty() => self.of(word),
            words => {
                let mut at = 0;
                let mut members = Vec::with_capacity(words.len());
                for (part, word) in words {
                    let name = match part.strip_prefix('.') {
                        Some(name) => name,
                        None if part.is_empty() => "tag",
                        None => part,
                    };
                    members.push((name, self.of(word), at));
                    at += bytes(word);
                }
                self.structure(&elements.name, at, &members)
            }
        };
        let array = self.here();
        self.out.uleb(encode::ARRAY);
        self.out.u32(element);
        self.out.uleb(encode::COUNTED);
        self.out.uleb(u64::from(elements.len));
        self.out.u8(0);
        self.typedef(&shown.name, array)
    }

    /// The layouts of an object's header and of a string, as `stilt-runtime` defines them.
    fn objects(&mut self) -> (u32, u32) {
        if let Some(objects) = self.objects {
            return objects;
        }
        let u8_ = self.base("u8", dw::DW_ATE_unsigned, 1);
        let u16_ = self.base("u16", dw::DW_ATE_unsigned, 2);
        let u32_ = self.base("u32", dw::DW_ATE_unsigned, 4);
        let u64_ = self.base("u64", dw::DW_ATE_unsigned, 8);
        let char_ = self.base("char", dw::DW_ATE_unsigned_char, 1);
        let header = [
            ("rc", u32_, 0),
            ("kind", u8_, 4),
            ("flags", u8_, 5),
            ("tag", u16_, 6),
            ("len", u32_, 8),
        ];
        let object = self.structure("stilt.object", 16, &header);
        let bytes = self.here();
        self.out.uleb(encode::ARRAY);
        self.out.u32(char_);
        self.out.uleb(encode::SUBRANGE);
        self.out.u8(0);
        let string = self.structure(
            "stilt.str",
            24,
            &[("rc", u32_, 0), ("size", u64_, 16), ("bytes", bytes, 24)],
        );
        self.objects = Some((object, string));
        (object, string)
    }

    fn structure(&mut self, name: &str, size: u64, members: &[(&str, u32, u64)]) -> u32 {
        let at = self.here();
        self.out.uleb(encode::STRUCTURE);
        self.out.string(name);
        self.out.uleb(size);
        for &(member, ty, offset) in members {
            self.out.uleb(encode::MEMBER);
            self.out.string(member);
            self.out.u32(ty);
            self.out.uleb(offset);
        }
        self.out.u8(0);
        at
    }
}

/// The bytes that a word a debugger shows as `shown` takes in memory: an array held in memory
/// all its elements' words, and any other one word.
fn bytes(shown: &Shown) -> u64 {
    match &shown.elements {
        Some(elements) => {
            let each: u64 = elements.words.iter().map(|(_, w)| bytes(w)).sum();
            u64::from(elements.len) * each
        }
        None => 8,
    }
}
