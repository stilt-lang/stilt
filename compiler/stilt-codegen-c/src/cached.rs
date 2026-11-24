//! The list operations that read a list's header from the locals that hold it ([`crate::lists`]):
//! element reads and slots, the length, making a list unique, appends and pops. Each loads
//! the header into the locals where they don't hold it, and sets them again where it changes.

use std::fmt::Write;

use stilt_mir::mir::{Local, Operand, Runtime};
use stilt_mir::shape;

use crate::function::{Emit, Expr};
use crate::lists::Key;
use crate::runtime::constant;

/// The names of the locals of a list's header: the list, its length and its elements.
pub(crate) struct Header {
    pub(crate) list: String,
    pub(crate) len: String,
    pub(crate) data: String,
}

/// The size of an element of a constant shape, and whether reading a narrow one extends its
/// sign.
fn sized(elem: &Operand) -> Option<(u64, u8)> {
    let s = constant(elem)?;
    let size = shape::size(s);
    Some((size, u8::from(size < 8 && shape::signed(s))))
}

impl Emit<'_, '_> {
    /// The locals of a key's header, which hold it once this returns.
    pub(crate) fn header(&mut self, key: Key) -> Header {
        let header = match key {
            Key::Place(p) => Header {
                list: format!("cl{p}"),
                len: format!("cn{p}"),
                data: format!("cd{p}"),
            },
            Key::Value(v) => Header {
                list: self.local(Local(u32::try_from(v).unwrap_or(0))).w(),
                len: format!("vn{v}"),
                data: format!("vd{v}"),
            },
        };
        if !self.lists.holds(key) {
            if let Key::Place(p) = key {
                let value = self.place_value(p);
                let _ = write!(self.out, "{} = {value}; ", header.list);
            }
            self.reread(&header);
            self.lists.state.held.insert(key);
        }
        header
    }

    /// Reads into the locals the header of the list that a place that holds lists was just
    /// given, and those of the lists the parameters hold, where the function starts.
    pub(crate) fn placed(&mut self, l: Local) {
        let i = l.0 as usize;
        if self.lists.is_list_place(i) {
            self.lists.used.insert(Key::Place(i));
            let value = self.local(l).w();
            let _ = write!(self.out, "cl{i} = {value}; ");
            self.reread(&Header {
                list: format!("cl{i}"),
                len: format!("cn{i}"),
                data: format!("cd{i}"),
            });
        }
    }

    /// Reads the headers of the lists the parameters hold, where the function starts.
    pub(crate) fn parameters(&mut self) {
        for p in self.lists.params.clone() {
            self.lists.used.insert(Key::Value(p));
            let list = self.local(Local(u32::try_from(p).unwrap_or(0))).w();
            self.reread(&Header {
                list,
                len: format!("vn{p}"),
                data: format!("vd{p}"),
            });
        }
    }

    /// The list place `p` holds: the local's word, or the word its pointer points to for the
    /// caller's slot of an `inout` parameter.
    fn place_value(&self, p: usize) -> String {
        let local = self.local(Local(u32::try_from(p).unwrap_or(0))).w();
        if self.lists.is_pointed(p) {
            format!("lt_load({local})")
        } else {
            local
        }
    }

    /// Reads a header into its locals from its list.
    fn reread(&mut self, h: &Header) {
        let _ = writeln!(
            self.out,
            "{} = lt_list_len({l}); {} = lt_list_data({l});",
            h.len,
            h.data,
            l = h.list
        );
    }

    /// The header of the list that place `p`, which `slot` points to, holds, made unique.
    fn made_unique(&mut self, p: usize, slot: &str) -> Header {
        let h = self.header(Key::Place(p));
        let _ = write!(
            self.out,
            "if (LT_UNLIKELY(!lt_is_unique({l}))) {{ {l} = stilt_rt_unique({slot}); ",
            l = h.list
        );
        self.reread(&h);
        self.out.push_str("}\n");
        h
    }

    /// The value of a list operation with the locals of its list's header, when it has them.
    pub(crate) fn cached_value(
        &mut self,
        f: Runtime,
        args: &[Operand],
    ) -> Result<Option<Expr>, String> {
        let value = match (f, args) {
            (Runtime::ListIndex, [loc, list, i, elem, word]) => {
                let Some(key) = self.lists.key_of(list) else {
                    return Ok(None);
                };
                let (size, sign) = sized(elem).ok_or("an element of a constant shape")?;
                let (loc, i, w) = (self.word(loc)?, self.word(i)?, constant(word).unwrap_or(0));
                let h = self.header(key);
                let _ = writeln!(
                    self.out,
                    "if (LT_UNLIKELY({i} >= {})) lt_fail_index({loc}, {}, {i});",
                    h.len, h.list
                );
                format!(
                    "lt_read({} + {i} * {size} + {}, {size}, {sign})",
                    h.data,
                    8 * w
                )
            }
            (Runtime::ListAt, [list, i, elem, word]) => {
                let Some(key) = self.lists.key_of(list) else {
                    return Ok(None);
                };
                let (size, sign) = sized(elem).ok_or("an element of a constant shape")?;
                let (i, w) = (self.word(i)?, constant(word).unwrap_or(0));
                let h = self.header(key);
                format!(
                    "lt_read({} + {i} * {size} + {}, {size}, {sign})",
                    h.data,
                    8 * w
                )
            }
            (Runtime::ListLen, [list]) => match self.lists.key_of(list) {
                Some(key) => self.header(key).len,
                None => return Ok(None),
            },
            _ => return self.cached_slot(f, args),
        };
        Ok(Some(Expr::word(value)))
    }

    /// An element's slot, or a list made unique, through the place that holds it.
    fn cached_slot(&mut self, op: Runtime, args: &[Operand]) -> Result<Option<Expr>, String> {
        let (loc, slot, index, elem) = match (op, args) {
            (Runtime::ListSlot | Runtime::ListElement, [loc, slot, i, elem]) => {
                (Some(loc), slot, Some(i), Some(elem))
            }
            (Runtime::ListSlotAt | Runtime::ListElementAt, [slot, i, elem]) => {
                (None, slot, Some(i), Some(elem))
            }
            (Runtime::Unique, [slot]) => (None, slot, None, None),
            _ => return Ok(None),
        };
        let Some(place) = self.lists.place_of(slot) else {
            return Ok(None);
        };
        let size = match elem {
            Some(elem) => sized(elem).ok_or("an element of a constant shape")?.0,
            None => 0,
        };
        let pointer = self.word(slot)?;
        let header = self.header(Key::Place(place));
        if let (Some(loc), Some(index)) = (loc, index) {
            let (loc, i) = (self.word(loc)?, self.word(index)?);
            let _ = writeln!(
                self.out,
                "if (LT_UNLIKELY({i} >= {})) lt_fail_slot({loc}, {pointer}, {i});",
                header.len
            );
        }
        let header = if matches!(
            op,
            Runtime::ListSlot | Runtime::ListSlotAt | Runtime::Unique
        ) {
            self.made_unique(place, &pointer)
        } else {
            header
        };
        Ok(Some(Expr::word(match index {
            Some(i) => format!("({} + {} * {size})", header.data, self.word(i)?),
            None => header.list,
        })))
    }

    /// The address of the words of an array that an element of a list holds, read in place,
    /// with the locals of its list's header.
    pub(crate) fn cached_array(
        &mut self,
        f: Runtime,
        args: &[Operand],
    ) -> Result<Option<String>, String> {
        let (loc, list, i, elem, at) = match (f, args) {
            (Runtime::ListAt, [list, i, elem, at]) => (None, list, i, elem, at),
            (Runtime::ListIndex, [loc, list, i, elem, at]) => (Some(loc), list, i, elem, at),
            _ => return Ok(None),
        };
        let Some(key) = self.lists.key_of(list) else {
            return Ok(None);
        };
        let (size, _) = sized(elem).ok_or("an element of a constant shape")?;
        let (i, at) = (self.word(i)?, constant(at).unwrap_or(0));
        let h = self.header(key);
        if let Some(loc) = loc {
            let loc = self.word(loc)?;
            let _ = writeln!(
                self.out,
                "if (LT_UNLIKELY({i} >= {})) lt_fail_index({loc}, {}, {i});",
                h.len, h.list
            );
        }
        Ok(Some(format!("({} + {i} * {size} + {})", h.data, 8 * at)))
    }

    /// Makes the list a place holds unique, for its effect, with the locals of its header.
    pub(crate) fn cached_unique(&mut self, slot: &Operand) -> Result<bool, String> {
        let Some(p) = self.lists.place_of(slot) else {
            return Ok(false);
        };
        let s = self.word(slot)?;
        self.made_unique(p, &s);
        Ok(true)
    }

    /// Appends an element of `size` bytes, whose words `words` are, to the list a place holds,
    /// which nothing else references, with the locals of its header.
    pub(crate) fn cached_push(
        &mut self,
        p: usize,
        words: &[Operand],
        size: u64,
    ) -> Result<(), String> {
        let h = self.header(Key::Place(p));
        self.out.push_str("{ ");
        let (store, memory) = self.element_words(words, size)?;
        let _ = writeln!(
            self.out,
            "if (LT_LIKELY({n} < lt_load({l} + LT_LIST_CAP))) {{ u64 a_ = {d} + {n} * {size};",
            n = h.len,
            l = h.list,
            d = h.data
        );
        self.out.push_str(&store);
        let _ = writeln!(
            self.out,
            "{n} = {n} + 1; lt_store({l} + LT_LIST_LEN, {n}); }} else {{ {memory}stilt_rt_list_push_words({l}, (u64)m_);",
            n = h.len,
            l = h.list
        );
        self.reread(&h);
        self.out.push_str("} }\n");
        Ok(())
    }

    /// `xs.pop()` on the list a place holds, of elements of `size` bytes, with the locals of
    /// its header: `None`, or `Some` of its last element, which moves out of the list once it
    /// is unique, as it is already when `unique` says so. Gives the expressions of the result's
    /// two words.
    pub(crate) fn cached_pop(
        &mut self,
        p: usize,
        slot: &str,
        (size, sign): (u64, u8),
        unique: bool,
    ) -> [String; 2] {
        let h = self.header(Key::Place(p));
        let _ = writeln!(self.out, "lt_ret p_ = {{1, 0}}; if ({} != 0) {{", h.len);
        let h = if unique { h } else { self.made_unique(p, slot) };
        let _ = writeln!(
            self.out,
            "{n} = {n} - 1; lt_store({l} + LT_LIST_LEN, {n}); p_.a = 3; p_.b = lt_read({d} + {n} * {size}, {size}, {sign}); }}",
            n = h.len,
            l = h.list,
            d = h.data
        );
        ["p_.a".to_owned(), "p_.b".to_owned()]
    }
}
