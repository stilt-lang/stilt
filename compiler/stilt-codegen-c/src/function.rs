//! One MIR function as one C function: its locals become C variables, a `double` for one that
//! holds an `f64` ([`crate::floats`]), or words of an array for those a pointer is taken to, one
//! array per group of the words of one value, and for an array held in memory; its blocks
//! become labels, and its control flow `goto`s, so that no loop is a C iteration statement,
//! which C lets a compiler assume ends (C11, 6.8.5).
//!
//! A function of at most one word of result returns its result and the raised flag as a
//! `lt_ret`, which is how the runtime calls closures and the methods of dictionaries
//! (`stilt_runtime::abi`); one of more words writes them to memory that its caller passes a
//! pointer to, as its last parameter, and returns the flag.
//!
//! The code of each stretch of the source, from one `Stmt::At` to the next, is one line of C
//! after a `#line` directive of the source's line, so that every instruction of it is the
//! source line's in the line tables (builds.line-tables).

use std::fmt::Write;

use stilt_mir::mir::{Function, Local, Operand, Repr, Terminator, line_of, offsets};

use crate::file::FileData;
use crate::lists::{Key, Lists};
use crate::names::c_string;
use crate::program::{Program, Refs};

/// A C expression, of a word or of a `double`.
#[derive(Clone, Debug)]
pub(crate) struct Expr {
    pub(crate) text: String,
    pub(crate) double: bool,
}

impl Expr {
    pub(crate) fn word(text: impl Into<String>) -> Self {
        Self {
            text: text.into(),
            double: false,
        }
    }

    pub(crate) fn double(text: impl Into<String>) -> Self {
        Self {
            text: text.into(),
            double: true,
        }
    }

    /// The expression as a word, a `double`'s bits.
    pub(crate) fn w(&self) -> String {
        if self.double {
            format!("lt_bits({})", self.text)
        } else {
            self.text.clone()
        }
    }

    /// The expression as a `double`, a word's bits.
    pub(crate) fn d(&self) -> String {
        if self.double {
            self.text.clone()
        } else {
            format!("lt_f64({})", self.text)
        }
    }
}

/// Where a local lives.
#[derive(Clone, Copy, Debug)]
enum Place {
    Var,
    /// Word `k` of the array of the group that starts at the local `first`.
    Group(usize, usize),
    /// An array of its own, of the words of an array held in memory.
    Array,
}

pub(crate) struct Emit<'p, 'f> {
    pub(crate) prog: &'p mut Program<'f>,
    pub(crate) file: &'p mut FileData,
    pub(crate) f: &'f Function,
    pub(crate) out: String,
    pub(crate) refs: Refs,
    doubles: Vec<bool>,
    places: Vec<Place>,
    /// Whether the block being emitted raises, which releases through the runtime.
    pub(crate) raising: bool,
    /// Where the C of the current stretch of the source starts in `out`.
    stretch: usize,
    /// The lists whose length and elements locals hold ([`crate::lists`]).
    pub(crate) lists: Lists,
}

/// The C result type of a function of `results` words.
pub(crate) fn result_type(results: u32) -> &'static str {
    if results <= 1 { "lt_ret" } else { "u64" }
}

/// The C declaration of compiled function `i`, `static` or of external linkage.
pub(crate) fn prototype(prog: &Program<'_>, i: usize, linkage: &str) -> String {
    let f = &prog.functions[i];
    let mut params: Vec<String> = (0..f.params.len()).map(|k| format!("u64 p{k}")).collect();
    if f.results > 1 {
        params.push("u64 *out".to_owned());
    }
    if params.is_empty() {
        params.push("void".to_owned());
    }
    let ret = result_type(f.results);
    let heat = match prog.hints.heat(f) {
        Some(crate::hints::Heat::Hot) => "__attribute__((hot)) ",
        Some(crate::hints::Heat::Cold) => "__attribute__((cold)) ",
        None => "",
    };
    format!(
        "{heat}{linkage}{ret} {}({})",
        prog.name(i),
        params.join(", ")
    )
}

/// The C body of compiled function `i`, from its `{`, and what it names. A function that
/// lowering marked broken is compiled as it is, as a debug build compiles it: only a program
/// with errors has one that runs, and a release build refuses such a program.
pub(crate) fn function(
    prog: &mut Program<'_>,
    file: &mut FileData,
    i: usize,
) -> Result<(String, Refs), String> {
    let functions = prog.functions;
    let f = &functions[i];
    let mut e = Emit {
        prog,
        file,
        f,
        out: String::new(),
        refs: Refs::default(),
        doubles: crate::floats::double_locals(f),
        places: vec![Place::Var; f.locals.len()],
        raising: false,
        stretch: 0,
        lists: Lists::new(f),
    };
    e.out.push_str("{\n");
    if e.prog.options.wasm {
        e.out.push_str("LT_STACK_CHECK();\n");
    }
    e.declare_locals();
    let headers = e.out.len();
    for (k, p) in f.params.iter().enumerate() {
        e.set(p.local, &Expr::word(format!("p{k}")));
    }
    e.parameters();
    e.stretch = e.out.len();
    for (b, block) in f.blocks.iter().enumerate() {
        e.lists.enter(b);
        let _ = writeln!(e.out, "bb{b}:;");
        e.raising = matches!(block.term, Terminator::Raise(_));
        for s in &block.stmts {
            e.stmt(s)?;
            e.lists.step(s);
        }
        e.term(&block.term)?;
        e.lists.term(&block.term);
    }
    e.end_stretch();
    e.out.push_str("}\n");
    let declared = e.header_locals();
    e.out.insert_str(headers, &declared);
    Ok((e.out, e.refs))
}

impl Emit<'_, '_> {
    /// Starts the stretch of the source at the location `word`: the C before it becomes one
    /// line, and a `#line` gives the source's line to what follows. A location in no file of
    /// the program, as the standard library's are, leaves the line where it was.
    pub(crate) fn at(&mut self, word: u64) {
        let file = usize::try_from(word >> 44).unwrap_or(usize::MAX);
        let Some(path) = self.prog.files.get(file) else {
            return;
        };
        self.end_stretch();
        let path = c_string(path.as_bytes());
        let _ = writeln!(self.out, "#line {} {path}", line_of(word));
        self.stretch = self.out.len();
    }

    /// Puts the C of the current stretch on one line.
    fn end_stretch(&mut self) {
        let text = self.out.split_off(self.stretch);
        let line = text.split('\n').map(str::trim).filter(|l| !l.is_empty());
        let joined: Vec<&str> = line.collect();
        if !joined.is_empty() {
            self.out.push_str(&joined.join(" "));
            self.out.push('\n');
        }
        self.stretch = self.out.len();
    }

    /// Declares every local, holding 0 until it is assigned, so that a drop of a local not yet
    /// assigned releases nothing.
    fn declare_locals(&mut self) {
        let locals = &self.f.locals;
        for (i, decl) in locals.iter().enumerate() {
            if decl.slot && decl.grouped {
                continue;
            }
            if decl.slot {
                let n = 1
                    + (locals[i + 1..].iter())
                        .take_while(|d| d.slot && d.grouped)
                        .count();
                let (at, words) = offsets((i..i + n).map(|j| locals[j].repr));
                for (j, k) in (i..i + n).zip(at) {
                    self.places[j] = Place::Group(i, k);
                }
                let _ = writeln!(self.out, "u64 g{i}[{}] = {{0}};", words.max(1));
            } else if let Repr::Array(e) = decl.repr {
                self.places[i] = Place::Array;
                let zero = if e.counted() { " = {0}" } else { "" };
                let _ = writeln!(self.out, "u64 a{i}[{}]{zero};", e.words().max(1));
            } else {
                let ty = if self.doubles[i] { "double" } else { "u64" };
                let _ = writeln!(self.out, "{ty} l{i} = 0;");
            }
        }
    }

    pub(crate) fn repr(&self, l: Local) -> Repr {
        self.f.locals[l.0 as usize].repr
    }

    /// The words of the array a local holds in memory, if it holds one.
    pub(crate) fn array_words(&self, l: Local) -> Option<usize> {
        match self.repr(l) {
            Repr::Array(e) => Some(e.words()),
            _ => None,
        }
    }

    /// The words of the array an operand names, if it names one.
    pub(crate) fn array_operand(&self, o: &Operand) -> Option<usize> {
        o.local().and_then(|l| self.array_words(l))
    }

    /// The declarations of the locals of every list's header that the code uses.
    fn header_locals(&self) -> String {
        let mut out = String::new();
        for key in &self.lists.used {
            let _ = match key {
                Key::Place(p) => writeln!(out, "u64 cl{p} = 0, cn{p} = 0, cd{p} = 0;"),
                Key::Value(v) => writeln!(out, "u64 vn{v} = 0, vd{v} = 0;"),
            };
        }
        out
    }

    /// A local's value: for an array held in memory, the address of its words.
    pub(crate) fn local(&self, l: Local) -> Expr {
        let i = l.0 as usize;
        match self.places[i] {
            Place::Var => Expr {
                text: format!("l{i}"),
                double: self.doubles[i],
            },
            Place::Group(g, k) if self.array_words(l).is_some() => {
                Expr::word(format!("(u64)&g{g}[{k}]"))
            }
            Place::Group(g, k) => Expr::word(format!("g{g}[{k}]")),
            Place::Array => Expr::word(format!("(u64)a{i}")),
        }
    }

    /// The address of a local that lives in memory, if it does.
    pub(crate) fn address_of(&self, l: Local) -> Option<String> {
        let i = l.0 as usize;
        match self.places[i] {
            Place::Var => None,
            Place::Group(g, k) => Some(format!("(u64)&g{g}[{k}]")),
            Place::Array => Some(format!("(u64)a{i}")),
        }
    }

    /// Gives a local the value `e`, converted to its type: an array held in memory the words
    /// that `e` points to, copied.
    pub(crate) fn set(&mut self, l: Local, e: &Expr) {
        if let Some(n) = self.array_words(l) {
            let to = self.local(l).text;
            let _ = writeln!(
                self.out,
                "__builtin_memcpy((void *){to}, (const void *){}, {});",
                e.w(),
                8 * n
            );
            return;
        }
        let target = self.local(l);
        let value = if target.double { e.d() } else { e.w() };
        let _ = writeln!(self.out, "{} = {value};", target.text);
    }

    /// An operand's value.
    pub(crate) fn operand(&mut self, o: &Operand) -> Result<Expr, String> {
        use stilt_mir::mir::Const;
        Ok(match o {
            // A place whose list's header the locals hold holds the list they hold.
            Operand::Local(l)
                if self.lists.is_place(l.0 as usize)
                    && self.repr(*l) == Repr::Heap
                    && self.lists.holds(Key::Place(l.0 as usize)) =>
            {
                Expr::word(format!("cl{}", l.0))
            }
            Operand::Local(l) => self.local(*l),
            Operand::Const(Const::Word(w)) => Expr::word(format!("{w:#x}ULL")),
            Operand::Const(Const::Code(f)) => {
                let g = (self.prog.compiled(f)).ok_or_else(|| format!("no code for {f}"))?;
                self.refs.slots.insert(g);
                self.file.slots.insert(g);
                Expr::word(format!("(u64)&s_{}", self.prog.name(g)))
            }
            Operand::Const(c) => {
                let d = self.file.datum(self.prog, c)?;
                Expr::word(format!("(u64)d{d}"))
            }
        })
    }

    /// An operand's value as a word.
    pub(crate) fn word(&mut self, o: &Operand) -> Result<String, String> {
        Ok(self.operand(o)?.w())
    }

    fn term(&mut self, t: &Terminator) -> Result<(), String> {
        match t {
            Terminator::Goto(b) => {
                let _ = writeln!(self.out, "goto bb{};", b.0);
            }
            Terminator::Branch {
                cond,
                then,
                otherwise,
            } => {
                let mut c = self.word(cond)?;
                if let Some(p) = self.prog.hints.likely(self.f, *then, *otherwise) {
                    c = format!("__builtin_expect_with_probability(({c}) != 0, 1, {p:.4})");
                }
                let (y, n) = (then.0, otherwise.0);
                let _ = writeln!(self.out, "if ({c}) goto bb{y}; else goto bb{n};");
            }
            Terminator::Switch {
                value,
                cases,
                otherwise,
            } => {
                let v = self.word(value)?;
                let _ = write!(self.out, "switch ({v}) {{");
                for (k, b) in cases {
                    let _ = write!(self.out, " case {k:#x}ULL: goto bb{};", b.0);
                }
                let _ = writeln!(self.out, " default: goto bb{}; }}", otherwise.0);
            }
            Terminator::Call {
                callee,
                args,
                dest,
                next,
                raised,
            } => self.call(callee, args, dest, *next, raised.as_ref())?,
            Terminator::Return(os) => self.return_words(os, false)?,
            Terminator::Raise(os) => self.return_words(os, true)?,
            // An array's index that verification proves in bounds: clang drops the test that
            // leads here (builds.dropped-checks).
            Terminator::Panic { kind, loc, .. } if self.prog.proved(loc).rules_out(*kind) => {
                self.out.push_str("__builtin_unreachable();\n");
            }
            Terminator::Panic { kind, detail, loc } => {
                let loc = self.word(loc)?;
                let detail = match detail {
                    Some(d) => self.word(d)?,
                    None => "0".to_owned(),
                };
                let _ = writeln!(self.out, "stilt_rt_panic({loc}, {kind}, {detail});");
            }
            Terminator::Unreachable => self.out.push_str("__builtin_trap();\n"),
        }
        Ok(())
    }

    /// Returns, or raises if `raise`, the words of a value, the unused words of the function's
    /// results being 0.
    fn return_words(&mut self, os: &[Operand], raise: bool) -> Result<(), String> {
        let flag = u64::from(raise);
        let results = self.f.results as usize;
        if results <= 1 {
            let first = match os.first() {
                Some(o) => self.word(o)?,
                None => "0".to_owned(),
            };
            let (a, b) = if results == 0 {
                (flag.to_string(), "0".to_owned())
            } else {
                (first, flag.to_string())
            };
            let _ = writeln!(self.out, "{{ lt_ret r_ = {{{a}, {b}}}; return r_; }}");
            return Ok(());
        }
        let mut at = 0;
        for o in os {
            let w = self.word(o)?;
            if let Some(n) = self.array_operand(o) {
                let _ = writeln!(
                    self.out,
                    "__builtin_memcpy(out + {at}, (const void *){w}, {});",
                    8 * n
                );
                at += n;
            } else {
                let _ = writeln!(self.out, "out[{at}] = {w};");
                at += 1;
            }
        }
        if at < results {
            let _ = writeln!(
                self.out,
                "__builtin_memset(out + {at}, 0, {});",
                8 * (results - at)
            );
        }
        let _ = writeln!(self.out, "return {flag};");
        Ok(())
    }
}
