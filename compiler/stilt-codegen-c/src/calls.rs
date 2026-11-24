//! Calls (`stilt_runtime::abi`): a direct call of a compiled function calls its C function, a
//! release build having no slots to patch; a closure's and a dictionary method's code is
//! reached through the slot its object's field holds, as the runtime reaches it; and a native
//! returns two words, its result's, or its result and the raised flag. The natives that debug
//! builds compute inline, a list's length, whether it is empty and its pop, are the header's.

use std::fmt::Write;

use stilt_mir::FnRef;
use stilt_mir::mir::{
    Arg, BlockId, Callee, Heapness, Local, Operand, Rvalue, Stmt, Terminator, offsets,
};

use crate::function::{Emit, Expr, result_type};
use crate::lists;

/// The runtime's name for a native of the standard library.
pub(crate) fn native_symbol(f: &FnRef) -> Option<String> {
    let flat = |home: &str| home.replace('.', "_");
    match f {
        FnRef::Function(item) => Some(format!("stilt_{}_{}", flat(&item.home), item.name)),
        FnRef::Member(owner, name) => {
            Some(format!("stilt_{}_{}_{name}", flat(&owner.home), owner.name))
        }
        _ => None,
    }
}

/// Where a call goes on: the locals its result goes to, the block after it, and for a call that
/// can raise, the locals its error goes to and the block that takes it.
pub(crate) type Then<'a> = (&'a [Local], BlockId, Option<&'a (Vec<Local>, BlockId)>);

/// Where the words a call returned are: each in an expression, or in the array `r_`.
pub(crate) enum Results {
    Words(Vec<String>),
    Memory,
}

impl Emit<'_, '_> {
    pub(crate) fn call(
        &mut self,
        callee: &Callee,
        args: &[Arg],
        dest: &[Local],
        next: BlockId,
        raised: Option<&(Vec<Local>, BlockId)>,
    ) -> Result<(), String> {
        self.out.push_str("{\n");
        if let Callee::Direct(FnRef::Foreign(c)) = callee {
            return self.call_foreign(c, args, (dest, next, raised));
        }
        let mut values = Vec::with_capacity(args.len() + 1);
        let mut rest = args.iter();
        if let Some(Arg::Borrow(loc)) = rest.next() {
            values.push(self.word(loc)?);
        }
        let code = match callee {
            Callee::Direct(_) => None,
            Callee::Value(o) | Callee::Method(o, _) => {
                let index = if let Callee::Method(_, i) = callee {
                    *i
                } else {
                    0
                };
                let object = self.word(o)?;
                let code = format!("lt_load(lt_load(lt_field({object}, {index})))");
                values.push(object);
                Some(code)
            }
        };
        for a in rest {
            values.push(match a {
                Arg::Borrow(o) | Arg::Own(o) | Arg::Ref(o) => self.word(o)?,
                Arg::Lend(words) => self.lent(words)?,
            });
        }
        let words = self
            .words_of(dest)
            .max(raised.map_or(0, |(e, _)| self.words_of(e)));
        let (results, flag) = match (callee, code) {
            (Callee::Direct(f), _) => match self.prog.compiled(f) {
                Some(g) => {
                    self.refs.functions.insert(g);
                    let (name, results) =
                        (self.prog.name(g).to_owned(), self.prog.functions[g].results);
                    if raised.is_none() && self.tail(results, dest, next) {
                        let _ = writeln!(self.out, "return {name}({});\n}}", values.join(", "));
                        return Ok(());
                    }
                    self.call_code(&name, &values, results, false)
                }
                None => return self.call_native(f, (&values, args), dest, next, raised),
            },
            (_, Some(code)) => {
                let results = u32::try_from(words).map_err(|e| e.to_string())?;
                self.call_code(&code, &values, results, true)
            }
            (_, None) => unreachable!("an indirect call has code"),
        };
        self.returned(&results, Some(&flag), dest, next, raised);
        self.out.push_str("}\n");
        Ok(())
    }

    /// Whether a call that can't raise, of a function that returns `results` words, is the
    /// function's last act: what follows it only moves its one word, the result, from local to
    /// local, and returns it, so that the call can return what the callee returns, its raised
    /// flag 0, and the C compiler can make a call of the function itself a jump.
    fn tail(&self, results: u32, dest: &[Local], next: BlockId) -> bool {
        let &[mut value] = dest else {
            return false;
        };
        if results != 1 || self.f.results != 1 {
            return false;
        }
        let mut block = next;
        for _ in 0..16 {
            let b = &self.f.blocks[block.0 as usize];
            for s in &b.stmts {
                match s {
                    Stmt::At(_) | Stmt::Count(..) => {}
                    Stmt::Assign(to, Rvalue::Use(Operand::Local(from))) if *from == value => {
                        value = *to;
                    }
                    _ => return false,
                }
            }
            match &b.term {
                Terminator::Goto(to) => block = *to,
                Terminator::Return(os) => return os.as_slice() == [Operand::Local(value)],
                _ => return false,
            }
        }
        false
    }

    /// The number of words of memory that a value of these locals takes.
    fn words_of(&self, locals: &[Local]) -> usize {
        offsets(locals.iter().map(|&l| self.repr(l))).1
    }

    /// Calls compiled code that returns `results` words, `code` a function's name or, if
    /// `indirect`, its address, and gives where its words are and its raised flag.
    fn call_code(
        &mut self,
        code: &str,
        values: &[String],
        results: u32,
        indirect: bool,
    ) -> (Results, String) {
        let mut values = values.to_vec();
        let callee = if indirect {
            let mut params = vec!["u64"; values.len()];
            if results > 1 {
                params.push("u64 *");
            }
            let ret = result_type(results);
            format!("(({ret} (*)({}))({code}))", params.join(", "))
        } else {
            code.to_owned()
        };
        if results > 1 {
            let _ = writeln!(self.out, "u64 r_[{results}];");
            values.push("r_".to_owned());
            let _ = writeln!(self.out, "u64 f_ = {callee}({});", values.join(", "));
            return (Results::Memory, "f_".to_owned());
        }
        let _ = writeln!(self.out, "lt_ret r_ = {callee}({});", values.join(", "));
        if results == 1 {
            (Results::Words(vec!["r_.a".to_owned()]), "r_.b".to_owned())
        } else {
            (Results::Words(Vec::new()), "r_.a".to_owned())
        }
    }

    /// Calls the native `f`, or computes it inline, and goes on.
    fn call_native(
        &mut self,
        f: &FnRef,
        (values, args): (&[String], &[Arg]),
        dest: &[Local],
        next: BlockId,
        raised: Option<&(Vec<Local>, BlockId)>,
    ) -> Result<(), String> {
        let symbol = native_symbol(f).ok_or_else(|| format!("no code for {f}"))?;
        if let Some(words) = self.inline_native(f, values, args) {
            self.returned(&Results::Words(words), None, dest, next, raised);
            self.out.push_str("}\n");
            return Ok(());
        }
        let name = self.prog.declare_extern(&symbol, values.len(), "lt_ret");
        self.refs.externs.insert(name.clone());
        let _ = writeln!(self.out, "lt_ret r_ = {name}({});", values.join(", "));
        if raised.is_some() {
            let words = Results::Words(vec!["r_.a".to_owned()]);
            self.returned(&words, Some("r_.b"), dest, next, raised);
        } else {
            let words = Results::Words(vec!["r_.a".to_owned(), "r_.b".to_owned()]);
            self.returned(&words, None, dest, next, raised);
        }
        self.out.push_str("}\n");
        Ok(())
    }

    /// The results of a native that the code computes inline, if it is one, with the locals
    /// of its list's header where it has them ([`crate::lists`]). Each takes its location and
    /// its element type's witness, then the list, or the slot of an `inout` one.
    fn inline_native(&mut self, f: &FnRef, values: &[String], args: &[Arg]) -> Option<Vec<String>> {
        let list = values.get(2)?;
        let operand = match args.get(2)? {
            Arg::Borrow(o) | Arg::Ref(o) => Some(o),
            _ => None,
        };
        if lists::inline_read(f) {
            let len = match operand.and_then(|o| self.lists.key_of(o)) {
                Some(key) => self.header(key).len,
                None => format!("lt_list_len({list})"),
            };
            let empty = matches!(f, FnRef::Member(_, name) if &**name == "is_empty");
            return Some(vec![if empty {
                format!("(u64)({len} == 0)")
            } else {
                len
            }]);
        }
        if let Some((size, sign)) = lists::get_size(f, args) {
            let i = values.get(3)?;
            let (len, data) = match operand.and_then(|o| self.lists.key_of(o)) {
                Some(key) => {
                    let h = self.header(key);
                    (h.len, h.data)
                }
                None => (
                    format!("lt_list_len({list})"),
                    format!("lt_list_data({list})"),
                ),
            };
            let _ = writeln!(
                self.out,
                "lt_ret p_ = {{1, 0}}; if ((u64){i} < {len}) {{ p_.a = 3; p_.b = lt_read({data} + (u64){i} * {size}, {size}, {sign}); }}"
            );
            return Some(vec!["p_.a".to_owned(), "p_.b".to_owned()]);
        }
        let (size, sign) = lists::pop_size(f, args)?;
        if let Some(p) = operand.and_then(|o| self.lists.place_of(o)) {
            let unique = lists::popped_unique(args);
            return Some(self.cached_pop(p, list, (size, sign), unique).to_vec());
        }
        let _ = writeln!(self.out, "lt_ret p_ = lt_pop({list}, {size}, {sign});");
        Some(vec!["p_.a".to_owned(), "p_.b".to_owned()])
    }

    /// Goes on after a call that returned `results`, and the raised flag `flag` if it can
    /// raise: to `next` with the result in `dest`, or when it raised, to the raised edge with
    /// the error in its locals.
    pub(crate) fn returned(
        &mut self,
        results: &Results,
        flag: Option<&str>,
        dest: &[Local],
        next: BlockId,
        raised: Option<&(Vec<Local>, BlockId)>,
    ) {
        if let (Some((error, block)), Some(flag)) = (raised, flag) {
            let _ = writeln!(self.out, "if ({flag}) {{");
            self.give(results, error);
            let _ = writeln!(self.out, "goto bb{}; }}", block.0);
        }
        self.give(results, dest);
        let _ = writeln!(self.out, "goto bb{};", next.0);
    }

    /// Gives `locals` the words a call returned, one after the other: an array held in memory
    /// its words, copied.
    fn give(&mut self, results: &Results, locals: &[Local]) {
        match results {
            Results::Words(words) => {
                for (&l, w) in locals.iter().zip(words) {
                    self.set(l, &Expr::word(w.clone()));
                }
            }
            Results::Memory => {
                let (at, _) = offsets(locals.iter().map(|&l| self.repr(l)));
                for (&l, i) in locals.iter().zip(at) {
                    let w = if self.array_words(l).is_some() {
                        format!("(u64)&r_[{i}]")
                    } else {
                        format!("r_[{i}]")
                    };
                    self.set(l, &Expr::word(w));
                }
            }
        }
    }

    /// A box of the words `fields` on the stack, lent for a call: its header has a count of 0,
    /// which no count changes or frees, and the tag of a box (`stilt_runtime::abi`).
    fn lent(&mut self, fields: &[(Operand, Heapness)]) -> Result<String, String> {
        let (len, layout) = self.layout_of(fields);
        let name = format!("b{}_", self.out.len());
        let size = 2 + len + stilt_runtime::layout::mask_words(len);
        let _ = writeln!(
            self.out,
            "u64 {name}[{size}] = {{{:#x}ULL, {layout}}};",
            u64::from(stilt_mir::mir::BOX) << 48
        );
        self.fill_data(&format!("(u64){name}"), fields)?;
        Ok(format!("(u64){name}"))
    }
}
