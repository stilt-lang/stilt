//! Runtime functions that compiled code calls: those with a fast path as the header's inline
//! functions, with the constant shape of a list's elements folded into the call as its size,
//! and every other as a call of the Rust runtime.

use std::fmt::Write;

use stilt_mir::mir::{Const, INLINE_FIELDS, Local, Operand, Runtime, known_variant};
use stilt_mir::shape;

use crate::function::{Emit, Expr};
use crate::lists::Key;

/// The value of a constant word.
pub(crate) fn constant(o: &Operand) -> Option<u64> {
    match o {
        Operand::Const(Const::Word(w)) => Some(*w),
        _ => None,
    }
}

fn word_of(o: &Operand) -> Result<u64, String> {
    constant(o).ok_or_else(|| format!("a constant operand, not {o:?}"))
}

/// The size in bytes of an element of a constant shape, and whether a narrow one's reads
/// extend its sign.
fn sized(elem: &Operand) -> Result<(u64, u8), String> {
    let s = word_of(elem)?;
    let size = shape::size(s);
    Ok((size, u8::from(size < 8 && shape::signed(s))))
}

impl Emit<'_, '_> {
    fn words(&mut self, args: &[Operand]) -> Result<Vec<String>, String> {
        args.iter().map(|a| self.word(a)).collect()
    }

    /// Declares a runtime function as `f`'s calls take it, and gives its name.
    fn declared(&mut self, f: Runtime, params: usize) -> String {
        let result = if f.returns() { "u64" } else { "void" };
        let name = self.prog.declare_extern(f.symbol(), params, result);
        self.refs.externs.insert(name.clone());
        name
    }

    /// Assigns the local `l` the result of the runtime function `f`, computed inline where it
    /// has a fast path, with the locals of a list's header where it has them ([`crate::lists`]).
    pub(crate) fn runtime_value(
        &mut self,
        l: Local,
        f: Runtime,
        args: &[Operand],
    ) -> Result<(), String> {
        if let Some(e) = self.cached_value(f, args)? {
            self.set(l, &e);
            return Ok(());
        }
        let e = match (f, args) {
            (
                Runtime::ListIndex
                | Runtime::ListAt
                | Runtime::ListLen
                | Runtime::ListSlot
                | Runtime::ListElement
                | Runtime::ListSlotAt
                | Runtime::ListElementAt,
                _,
            ) => self.list_op(f, args)?,
            (Runtime::ListGet, [loc, list, i, shape]) => {
                let v = self.words(&[loc.clone(), list.clone(), i.clone(), shape.clone()])?;
                format!("lt_list_get({})", v.join(", "))
            }
            (Runtime::Shape, words) => return self.shape_of(l, words),
            (Runtime::ShapeParts, parts) => {
                return self.in_memory(l, "stilt_rt_shape_parts", parts, parts.len() / 2);
            }
            (Runtime::MapWord, [_, pointer, i]) => {
                format!("lt_load({} + {})", self.word(pointer)?, 8 * word_of(i)?)
            }
            (Runtime::Unique, [slot]) => format!("lt_unique({})", self.word(slot)?),
            (Runtime::Reclaim, [object, len, taken, known]) => {
                let (object, n, taken) = (self.word(object)?, word_of(len)?, self.word(taken)?);
                match known_variant(word_of(known)?).and_then(|v| v.layout) {
                    Some(layout) if n <= INLINE_FIELDS as u64 => {
                        let heap = u64::from(layout) & ((1 << n) - 1);
                        format!("lt_reclaim_known({object}, {n}, {taken}, {heap:#x}ULL)")
                    }
                    _ => format!("lt_reclaim({object}, {n}, {taken})"),
                }
            }
            _ => {
                let values = self.words(args)?;
                let name = self.declared(f, values.len());
                if f.returns() {
                    format!("{name}({})", values.join(", "))
                } else {
                    let _ = writeln!(self.out, "{name}({});", values.join(", "));
                    "0".to_owned()
                }
            }
        };
        self.set(l, &Expr::word(e));
        Ok(())
    }

    /// A list operation without the locals of its list's header: an element read, the length,
    /// or an element's slot, made unique or known so.
    fn list_op(&mut self, f: Runtime, args: &[Operand]) -> Result<String, String> {
        Ok(match (f, args) {
            (Runtime::ListIndex, [loc, list, i, elem, word]) => {
                let (size, sign) = sized(elem)?;
                let (loc, list, i) = (self.word(loc)?, self.word(list)?, self.word(i)?);
                let w = word_of(word)?;
                format!("lt_list_index({loc}, {list}, {i}, {size}, {sign}, {w})")
            }
            (Runtime::ListAt, [list, i, elem, word]) => {
                let (size, sign) = sized(elem)?;
                let (list, i, w) = (self.word(list)?, self.word(i)?, word_of(word)?);
                format!("lt_list_at({list}, {i}, {size}, {sign}, {w})")
            }
            (Runtime::ListLen, [list]) => format!("lt_list_len({})", self.word(list)?),
            (Runtime::ListSlot | Runtime::ListElement, [loc, slot, i, elem]) => {
                let name = if f == Runtime::ListSlot {
                    "slot"
                } else {
                    "element"
                };
                let (size, _) = sized(elem)?;
                let (loc, slot, i) = (self.word(loc)?, self.word(slot)?, self.word(i)?);
                format!("lt_list_{name}({loc}, {slot}, {i}, {size})")
            }
            (Runtime::ListSlotAt | Runtime::ListElementAt, [slot, i, elem]) => {
                let name = if f == Runtime::ListSlotAt {
                    "slot"
                } else {
                    "element"
                };
                let (size, _) = sized(elem)?;
                let (slot, i) = (self.word(slot)?, self.word(i)?);
                format!("lt_list_{name}_at({slot}, {i}, {size})")
            }
            _ => return Err(format!("{f:?} of {} operands", args.len())),
        })
    }

    /// Assigns `l` the result of `name`, which takes a pointer to the words of `args` in
    /// memory, and `n`.
    fn in_memory(
        &mut self,
        l: Local,
        name: &str,
        args: &[Operand],
        n: usize,
    ) -> Result<(), String> {
        let values = self.words(args)?;
        let _ = writeln!(
            self.out,
            "{{ u64 m_[{}] = {{{}}};",
            values.len().max(1),
            values.join(", ")
        );
        self.set(l, &Expr::word(format!("{name}((u64)m_, {n})")));
        self.out.push_str("}\n");
        Ok(())
    }

    /// The shape of a value of words of these operands, each 0 for a scalar, 1 for a heap word
    /// or the witness of a type parameter, whose lowest bit tells.
    fn shape_of(&mut self, l: Local, words: &[Operand]) -> Result<(), String> {
        let Some(fixed) = shape::of_words(&vec![false; words.len()]) else {
            return self.in_memory(l, "stilt_rt_large_shape", words, words.len());
        };
        let mut e = format!("{fixed:#x}ULL");
        for (k, w) in words.iter().enumerate() {
            let heap = format!("({} & 1)", self.word(w)?);
            let _ = write!(
                e,
                " | ({heap} << {})",
                u64::from(shape::MASK_SHIFT) + k as u64
            );
            if words.len() == 1 {
                let _ = write!(e, " | {heap}");
            }
        }
        self.set(l, &Expr::word(e));
        Ok(())
    }

    /// A runtime function called for its effect, inline where it has a fast path.
    pub(crate) fn effect(&mut self, f: Runtime, args: &[Operand]) -> Result<(), String> {
        match (f, args) {
            (Runtime::ListPush, [target, elem, words @ ..])
                if let (Some(Key::Place(p)), Some(s)) =
                    (self.lists.key_of(target), constant(elem)) =>
            {
                self.cached_push(p, words, shape::size(s))
            }
            (Runtime::ListPush | Runtime::ListAppend, [target, elem, words @ ..]) => {
                self.append(f == Runtime::ListAppend, target, elem, words)
            }
            (Runtime::StorePacked, [pointer, x, elem]) => {
                let (size, _) = sized(elem)?;
                let (p, x) = (self.word(pointer)?, self.word(x)?);
                let _ = writeln!(self.out, "lt_write({p}, {x}, {size});");
                Ok(())
            }
            (Runtime::Discard, [memory]) => {
                let memory = self.word(memory)?;
                let _ = writeln!(self.out, "lt_discard({memory});");
                Ok(())
            }
            (Runtime::Unique, [slot]) => {
                if !self.cached_unique(slot)? {
                    let slot = self.word(slot)?;
                    let _ = writeln!(self.out, "(void)lt_unique({slot});");
                }
                Ok(())
            }
            _ => {
                let values = self.words(args)?;
                let name = self.declared(f, values.len());
                let _ = writeln!(self.out, "{name}({});", values.join(", "));
                Ok(())
            }
        }
    }

    /// Appends an element to a list that nothing else references, or with `slot`, to the list
    /// a slot holds: inline when the list is unique and has room, and otherwise through the
    /// runtime, which takes the element's words in memory, or a value of a type parameter in
    /// its one word.
    fn append(
        &mut self,
        slot: bool,
        target: &Operand,
        elem: &Operand,
        words: &[Operand],
    ) -> Result<(), String> {
        let t = self.word(target)?;
        let Some(s) = constant(elem) else {
            let (w, x) = (self.word(elem)?, self.word(&words[0])?);
            let name = if slot {
                "lt_append_value"
            } else {
                "lt_push_value"
            };
            let _ = writeln!(self.out, "{name}({t}, {w}, {x});");
            return Ok(());
        };
        let size = shape::size(s);
        let (ready, list) = if slot {
            ("lt_is_unique(l_) && lt_has_room(l_)", "lt_load(t_)")
        } else {
            ("lt_has_room(l_)", "t_")
        };
        let _ = writeln!(self.out, "{{ u64 t_ = {t}; u64 l_ = {list};");
        let (store, memory) = self.element_words(words, size)?;
        let _ = writeln!(self.out, "if (LT_LIKELY({ready})) {{");
        let _ = writeln!(
            self.out,
            "u64 n_ = lt_list_len(l_); u64 a_ = lt_element(l_, n_, {size}, 0);"
        );
        self.out.push_str(&store);
        self.out
            .push_str("lt_store(l_ + LT_LIST_LEN, n_ + 1);\n} else {\n");
        let fallback = if slot {
            "stilt_rt_list_append_words"
        } else {
            "stilt_rt_list_push_words"
        };
        let _ = writeln!(self.out, "{memory}{fallback}(t_, (u64)m_);\n}}\n}}");
        Ok(())
    }

    /// The code that stores an element's words at `a_`, in an element of `size` bytes, and the
    /// code that puts them in `m_` for the runtime. The words of an element that holds an array
    /// in memory go to `m_` first, and from there to the list; any other's are stored from
    /// where they are, and go to memory only on the slow path.
    pub(crate) fn element_words(
        &mut self,
        words: &[Operand],
        size: u64,
    ) -> Result<(String, String), String> {
        let mut n = 0;
        let mut fill = String::new();
        let mut store = String::new();
        let arrays = words.iter().any(|w| self.array_operand(w).is_some());
        for w in words {
            let v = self.word(w)?;
            if let Some(k) = self.array_operand(w) {
                let _ = writeln!(
                    fill,
                    "__builtin_memcpy(m_ + {n}, (const void *){v}, {});",
                    8 * k
                );
                n += k;
                continue;
            }
            let _ = writeln!(fill, "m_[{n}] = {v};");
            if size < 8 {
                let _ = writeln!(store, "lt_write(a_, {v}, {size});");
            } else {
                let _ = writeln!(store, "lt_store(a_ + {}, {v});", 8 * n);
            }
            n += 1;
        }
        let declare = format!("u64 m_[{}];\n", n.max(1));
        if arrays {
            self.out.push_str(&declare);
            self.out.push_str(&fill);
            let copy = format!("__builtin_memcpy((void *)a_, m_, {});\n", 8 * n);
            return Ok((copy, String::new()));
        }
        Ok((store, declare + &fill))
    }

    /// The address of the words of an array that a runtime function reads in place: an
    /// element of a list, or a key or a value of a map.
    pub(crate) fn array_in_runtime(
        &mut self,
        f: Runtime,
        args: &[Operand],
    ) -> Result<String, String> {
        if let Some(address) = self.cached_array(f, args)? {
            return Ok(address);
        }
        match (f, args) {
            (Runtime::ListAt, [list, i, elem, at]) => {
                let (size, _) = sized(elem)?;
                let (list, i) = (self.word(list)?, self.word(i)?);
                Ok(format!("lt_element({list}, {i}, {size}, {})", word_of(at)?))
            }
            (Runtime::ListIndex, [loc, list, i, elem, at]) => {
                let (size, _) = sized(elem)?;
                let (loc, list, i) = (self.word(loc)?, self.word(list)?, self.word(i)?);
                let at = word_of(at)?;
                Ok(format!(
                    "lt_checked_element({loc}, {list}, {i}, {size}, {at})"
                ))
            }
            (Runtime::MapWord, [_, pointer, at]) => {
                Ok(format!("({} + {})", self.word(pointer)?, 8 * word_of(at)?))
            }
            _ => Err(format!("an array in memory from {f:?}")),
        }
    }
}
