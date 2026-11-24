//! Statements and rvalues: assignments, stores, counting, data objects, fields, tags, slots and
//! constants. Each copy, release and count of an array held in memory is a loop over its
//! elements with a constant bound, which ends.

use std::fmt::Write;

use stilt_mir::mir::{Elements, Heapness, Kept, Local, Operand, Repr, Rvalue, Stmt, offsets};
use stilt_runtime::layout;

use crate::function::{Emit, Expr};
use crate::lists::Key;

/// How a word is counted: one more reference, one less, one less through the runtime (on a
/// path that raises, as the debug back end does), or marked shared (a constant's value).
#[derive(Clone, Copy, Debug)]
pub(crate) enum Count {
    Dup,
    Drop,
    DropCold,
    Share,
}

impl Count {
    fn function(self) -> &'static str {
        match self {
            Count::Dup => "lt_dup",
            Count::Drop => "lt_drop",
            Count::DropCold => "stilt_rt_drop",
            Count::Share => "stilt_rt_constant_share",
        }
    }
}

/// Writes the code that counts the word `v` of the representation `repr`, or each counted word
/// of an array held in memory at the address `v`; `witness` gives a type parameter's witness.
pub(crate) fn count_code(
    out: &mut String,
    v: &str,
    repr: Repr,
    count: Count,
    witness: &dyn Fn(Local) -> String,
) {
    match repr {
        Repr::Scalar => {}
        Repr::Heap => {
            let _ = writeln!(out, "{}({v});", count.function());
        }
        Repr::Generic(w) => {
            let _ = writeln!(out, "if ({} & 1) {}({v});", witness(w), count.function());
        }
        Repr::Array(e) => each_counted(out, v, e, 0, &mut |out, addr, r| {
            count_code(out, &format!("lt_load({addr})"), r, count, witness);
        }),
    }
}

/// Writes `f` for each word of an array of the layout `e` at `base` that may need its
/// references counted, in a loop over its elements, with the word's address.
fn each_counted(
    out: &mut String,
    base: &str,
    e: Elements<Repr>,
    depth: usize,
    f: &mut dyn FnMut(&mut String, &str, Repr),
) {
    if !e.counted() {
        return;
    }
    let width = 8 * e.element_words();
    let (at, _) = offsets(e.each().iter().copied());
    let _ = writeln!(
        out,
        "for (u64 i{depth} = 0; i{depth} < {}; i{depth}++) {{ u64 e{depth} = {base} + {width} * i{depth};",
        e.len()
    );
    for (&r, &k) in e.each().iter().zip(&at) {
        let addr = format!("(e{depth} + {})", 8 * k);
        match r {
            Repr::Scalar => {}
            Repr::Heap | Repr::Generic(_) => f(out, &addr, r),
            Repr::Array(inner) => each_counted(out, &addr, inner, depth + 1, f),
        }
    }
    out.push_str("}\n");
}

impl Emit<'_, '_> {
    pub(crate) fn stmt(&mut self, s: &Stmt) -> Result<(), String> {
        match s {
            Stmt::Assign(l, r) => {
                if let Repr::Array(e) = self.repr(*l) {
                    self.assign_array(*l, e, r)
                } else {
                    self.rvalue(*l, r)?;
                    self.placed(*l);
                    Ok(())
                }
            }
            Stmt::Store { slot, value, repr } => self.store(slot, value, *repr),
            Stmt::Effect(f, args) => self.effect(*f, args),
            Stmt::ReleaseConstants => {
                self.out.push_str("lt_release_constants();\n");
                Ok(())
            }
            Stmt::Dup(l) | Stmt::Drop(l) => {
                let count = match (s, self.raising) {
                    (Stmt::Dup(_), _) => Count::Dup,
                    (_, false) => Count::Drop,
                    (_, true) => Count::DropCold,
                };
                let v = self.local(*l).w();
                self.count(&v, self.repr(*l), count);
                Ok(())
            }
            Stmt::At(word) => {
                self.at(*word);
                Ok(())
            }
            // A mark of what a profile counts, which the function's hints read
            // (builds.profile-use).
            Stmt::Count(..) => Ok(()),
        }
    }

    /// Counts the word `v` of the representation `repr`.
    pub(crate) fn count(&mut self, v: &str, repr: Repr, count: Count) {
        let mut out = std::mem::take(&mut self.out);
        count_code(&mut out, v, repr, count, &|w| self.local(w).w());
        self.out = out;
    }

    fn rvalue(&mut self, l: Local, r: &Rvalue) -> Result<(), String> {
        let e = match r {
            Rvalue::Use(o) => self.operand(o)?,
            Rvalue::Prim(p, args, loc) => return self.prim(l, *p, args, loc),
            Rvalue::Alloc(tag, fields) => return self.alloc(l, *tag, fields),
            Rvalue::AllocIn(memory, tag, fields, kept) => {
                return self.alloc_in(l, memory, (*tag, *kept), fields);
            }
            Rvalue::Field { base, index, .. } => {
                Expr::word(format!("lt_load(lt_field({}, {index}))", self.word(base)?))
            }
            Rvalue::Tag(o) => Expr::word(format!("lt_tag({})", self.word(o)?)),
            Rvalue::Load(o) => match self.lists.place_of(o) {
                Some(p) if self.lists.holds(Key::Place(p)) => Expr::word(format!("cl{p}")),
                _ => Expr::word(format!("lt_load({})", self.word(o)?)),
            },
            Rvalue::SlotOf(s) => Expr::word(self.slot_of(*s)?),
            Rvalue::Offset(o, words) => {
                Expr::word(format!("({} + {})", self.word(o)?, 8 * u64::from(*words)))
            }
            Rvalue::FieldSlot { slot, index, .. } => Expr::word(format!(
                "lt_field(lt_unique({}), {index})",
                self.word(slot)?
            )),
            Rvalue::Runtime(f, args) => return self.runtime_value(l, *f, args),
            Rvalue::Constant(f, loc, k, words, _) => {
                let at = self.constant_value(f, loc, *k, words)?;
                Expr::word(format!("lt_load({at})"))
            }
        };
        self.set(l, &e);
        Ok(())
    }

    /// The address of a local that lives in memory.
    fn slot_of(&self, l: Local) -> Result<String, String> {
        self.address_of(l)
            .ok_or_else(|| format!("a pointer to {l}, which isn't in memory"))
    }

    /// The address of value `k` of a constant's value, of the words `words`, computed where it
    /// is first used (declarations.constant-evaluation).
    pub(crate) fn constant_value(
        &mut self,
        f: &stilt_mir::FnRef,
        loc: &Operand,
        k: u32,
        words: &[Repr],
    ) -> Result<String, String> {
        let cell = self.prog.cell(f, words);
        self.refs.cells.insert(cell);
        let (at, _) = offsets(words.iter().copied());
        let at = 8 + 8 * at.get(k as usize).copied().unwrap_or(0);
        let loc = self.word(loc)?;
        Ok(format!(
            "(lt_cell_{}({loc}) + {at})",
            self.prog.cells[cell].name
        ))
    }

    /// Gives an array local the words of the rvalue `r`: those it copies, or none for a
    /// constant, which clears it.
    fn assign_array(
        &mut self,
        array: Local,
        layout: Elements<Repr>,
        rvalue: &Rvalue,
    ) -> Result<(), String> {
        let to = self.local(array).text;
        let bytes = 8 * layout.words();
        let from = match rvalue {
            Rvalue::Use(Operand::Const(_)) => {
                let _ = writeln!(self.out, "__builtin_memset((void *){to}, 0, {bytes});");
                return Ok(());
            }
            Rvalue::Use(o) | Rvalue::Load(o) => self.word(o)?,
            Rvalue::Field { base, index, .. } => {
                format!("lt_field({}, {index})", self.word(base)?)
            }
            Rvalue::Constant(f, loc, k, words, _) => self.constant_value(f, loc, *k, words)?,
            Rvalue::Runtime(f, args) => self.array_in_runtime(*f, args)?,
            _ => return Err(format!("an array in memory from {rvalue:?}")),
        };
        let _ = writeln!(
            self.out,
            "__builtin_memcpy((void *){to}, (const void *){from}, {bytes});"
        );
        Ok(())
    }

    /// Writes a word into the slot a pointer points to, releasing the word it held, or for an
    /// array held in memory, its words.
    fn store(&mut self, slot: &Operand, value: &Operand, repr: Repr) -> Result<(), String> {
        let p = self.word(slot)?;
        self.out.push_str("{\n");
        let _ = writeln!(self.out, "u64 p_ = {p};");
        if let Repr::Array(e) = repr {
            self.count("p_", repr, Count::Drop);
            let n = 8 * e.words();
            match value {
                Operand::Local(_) => {
                    let v = self.word(value)?;
                    let _ = writeln!(
                        self.out,
                        "__builtin_memcpy((void *)p_, (const void *){v}, {n});"
                    );
                }
                Operand::Const(_) => {
                    let _ = writeln!(self.out, "__builtin_memset((void *)p_, 0, {n});");
                }
            }
        } else {
            let v = self.word(value)?;
            let _ = writeln!(self.out, "u64 o_ = lt_load(p_); lt_store(p_, {v});");
            self.count("o_", repr, Count::Drop);
        }
        self.out.push_str("}\n");
        Ok(())
    }

    /// A new data object, its fields and layout set.
    fn alloc(&mut self, l: Local, tag: u16, fields: &[(Operand, Heapness)]) -> Result<(), String> {
        let (len, layout) = self.layout_of(fields);
        let _ = writeln!(
            self.out,
            "{{ u64 o_ = lt_alloc_data({len}, {tag}, {layout});"
        );
        self.fill_data("o_", fields)?;
        self.set(l, &Expr::word("o_"));
        self.out.push_str("}\n");
        Ok(())
    }

    /// [`Self::alloc`], in the memory that `memory` holds when it isn't 0, which
    /// `lt_renew` makes a new object's. Kept memory whose header is the new object's, and the
    /// words that hold their values already, aren't written again.
    fn alloc_in(
        &mut self,
        l: Local,
        memory: &Operand,
        (tag, kept): (u16, Kept),
        fields: &[(Operand, Heapness)],
    ) -> Result<(), String> {
        let (len, layout) = self.layout_of(fields);
        let memory = self.word(memory)?;
        let small = len <= layout::INLINE_FIELDS;
        let renew = if kept.header && small {
            format!("m_ ? m_ : lt_alloc_data({len}, {tag}, {layout})")
        } else {
            format!("lt_renew(m_, {len}, {tag}, {layout})")
        };
        let _ = writeln!(self.out, "{{ u64 m_ = {memory}; u64 o_ = {renew};");
        let kept = (small && kept.words != 0).then_some(kept.words);
        self.fill_kept("o_", fields, kept)?;
        self.set(l, &Expr::word("o_"));
        self.out.push_str("}\n");
        Ok(())
    }

    /// The number of words of a data object of these fields, and its layout word as an
    /// expression: the bits of its heap words, those of a type parameter's by its witness, and
    /// the bit of its length (`stilt_runtime::layout::data_layout`), or for a large object, its
    /// length, its heap bits then going to the masks after its fields. The bits of an array's
    /// heap words are set as it is copied in ([`Self::fill_data`]).
    pub(crate) fn layout_of(&self, fields: &[(Operand, Heapness)]) -> (usize, String) {
        let (at, len) = offsets(fields.iter().map(|(_, h)| match h {
            Heapness::Array(e) => Repr::Array(*e),
            _ => Repr::Scalar,
        }));
        if len > layout::INLINE_FIELDS {
            return (len, format!("{:#x}ULL", layout::data_layout(len, 0)));
        }
        let mut bits = 0u64;
        let mut dynamic = String::new();
        for ((_, heap), &i) in fields.iter().zip(&at) {
            match heap {
                Heapness::Static(true) => bits |= 1 << i,
                Heapness::Witness(w) => {
                    let _ = write!(dynamic, " | (({} & 1) << {i})", self.local(*w).w());
                }
                Heapness::Static(false) | Heapness::Array(_) => {}
            }
        }
        let fixed = format!("{:#x}ULL", layout::data_layout(len, bits));
        if dynamic.is_empty() {
            (len, fixed)
        } else {
            (len, format!("({fixed}{dynamic})"))
        }
    }

    /// Stores the fields of the data object `object`, whose layout word is set but for the bits
    /// of its arrays' heap words, each after the last; and for a large object, the bits of its
    /// heap words in the masks after them, which are zero.
    pub(crate) fn fill_data(
        &mut self,
        object: &str,
        fields: &[(Operand, Heapness)],
    ) -> Result<(), String> {
        self.fill_kept(object, fields, None)
    }

    /// [`Self::fill_data`], but for the words that `kept` names, which memory kept in `m_`
    /// holds already, and which only a new object, when `m_` is 0, needs written.
    fn fill_kept(
        &mut self,
        object: &str,
        fields: &[(Operand, Heapness)],
        kept: Option<u64>,
    ) -> Result<(), String> {
        let (at, len) = offsets(fields.iter().map(|(_, h)| match h {
            Heapness::Array(e) => Repr::Array(*e),
            _ => Repr::Scalar,
        }));
        let large = len > layout::INLINE_FIELDS;
        let mask_at = 16 + 8 * len;
        // Without an array field, the stores here set every mask bit, so each mask is stored
        // whole: the zero it was made with is never read, and the C compiler drops that store.
        let whole = !fields.iter().any(|(_, h)| matches!(h, Heapness::Array(_)));
        let mut masks: Vec<(u64, Vec<String>)> = vec![(0, Vec::new()); len.div_ceil(64)];
        for ((field, heap), &i) in fields.iter().zip(&at) {
            let to = format!("({object} + {})", 16 + 8 * i);
            let bit = i % 64;
            match heap {
                Heapness::Array(e) => {
                    let bits = if large {
                        Bits::Masks(mask_at)
                    } else {
                        Bits::Layout
                    };
                    self.fill_array(object, &to, field, bits, *e)?;
                    continue;
                }
                Heapness::Static(true) => masks[i / 64].0 |= 1 << bit,
                Heapness::Static(false) => {}
                Heapness::Witness(w) => {
                    let w = self.local(*w).w();
                    masks[i / 64].1.push(format!("(({w} & 1) << {bit})"));
                }
            }
            let v = self.word(field)?;
            let held = kept.is_some_and(|k| i < 64 && k >> i & 1 == 1);
            let when = if held { "if (!m_) " } else { "" };
            let _ = writeln!(self.out, "{when}lt_store({to}, {v});");
        }
        if !large {
            return Ok(());
        }
        for (j, (bits, dynamic)) in masks.into_iter().enumerate() {
            if bits == 0 && dynamic.is_empty() && !whole {
                continue;
            }
            let mut mask = format!("{bits:#x}ULL");
            for d in dynamic {
                mask = format!("{mask} | {d}");
            }
            let op = if whole { "=" } else { "|=" };
            let _ = writeln!(
                self.out,
                "*(u64 *)({object} + {}) {op} {mask};",
                mask_at + 8 * j
            );
        }
        Ok(())
    }

    /// Copies an array field's words to `to` in a data object, and sets the bits of its heap
    /// words where the object keeps them.
    fn fill_array(
        &mut self,
        object: &str,
        to: &str,
        field: &Operand,
        bits: Bits,
        e: Elements<Repr>,
    ) -> Result<(), String> {
        let n = 8 * e.words();
        match field {
            Operand::Local(_) => {
                let from = self.word(field)?;
                let _ = writeln!(
                    self.out,
                    "__builtin_memcpy((void *){to}, (const void *){from}, {n});"
                );
            }
            Operand::Const(_) => {
                let _ = writeln!(self.out, "__builtin_memset((void *){to}, 0, {n});");
            }
        }
        let witness = |w: Local| self.local(w).w();
        let mut out = String::new();
        each_counted(&mut out, to, e, 0, &mut |out, addr, r| {
            let heap = match r {
                Repr::Generic(w) => format!("({} & 1)", witness(w)),
                _ => "1".to_owned(),
            };
            let _ = match bits {
                Bits::Layout => writeln!(
                    out,
                    "{{ u64 w_ = ({addr} - {object} - 16) / 8; *(u32 *)({object} + 8) |= (u32)({heap} << w_); }}"
                ),
                Bits::Masks(mask_at) => writeln!(
                    out,
                    "{{ u64 w_ = ({addr} - {object} - 16) / 8; *(u64 *)({object} + {mask_at} + 8 * (w_ / 64)) |= {heap} << (w_ % 64); }}"
                ),
            };
        });
        self.out.push_str(&out);
        Ok(())
    }
}

/// Where a data object keeps the bits of its heap words: in its layout word, or for a large
/// object, in the masks at this byte of it.
#[derive(Clone, Copy)]
enum Bits {
    Layout,
    Masks(usize),
}
