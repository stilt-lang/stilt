//! The static data of one C file: the immortal objects of the constant strings and data
//! objects that its functions name, as `stilt-runtime` lays objects out, each numbered in
//! the order the file first names it, so that a file's C depends only on its own functions.
//! A constant that two files name is an object in each, which nothing tells apart, since an
//! immortal object is never written and only its contents are compared.

use std::collections::{BTreeSet, HashMap};
use std::fmt::Write as _;

use stilt_mir::mir::Const;
use stilt_runtime::layout;

use crate::program::Program;

/// An object of static data: its words, as C initializers.
#[derive(Debug)]
pub(crate) struct Datum {
    pub(crate) words: Vec<String>,
}

/// The static data of a file, and the functions whose slots it holds.
#[derive(Debug, Default)]
pub(crate) struct FileData {
    index: HashMap<Const, usize>,
    pub(crate) datums: Vec<Datum>,
    pub(crate) slots: BTreeSet<usize>,
}

impl FileData {
    /// The index of the static object of a constant string or data object.
    pub(crate) fn datum(&mut self, prog: &Program<'_>, c: &Const) -> Result<usize, String> {
        if let Some(&i) = self.index.get(c) {
            return Ok(i);
        }
        let datum = match c {
            Const::Str(s) => Datum {
                words: string_words(s),
            },
            Const::Data(tag, fields) => self.data_object(prog, *tag, fields)?,
            Const::Word(_) | Const::Code(_) => return Err("a word is no data".to_owned()),
        };
        let i = self.datums.len();
        self.datums.push(datum);
        self.index.insert(c.clone(), i);
        Ok(i)
    }

    /// A data object of the fields `fields`: its header, of count 0, then its fields and
    /// masks. The objects it points to come before it.
    fn data_object(
        &mut self,
        prog: &Program<'_>,
        tag: u16,
        fields: &[(Const, bool)],
    ) -> Result<Datum, String> {
        let len = fields.len();
        let mut masks = vec![0u64; len.div_ceil(64)];
        for (i, (_, heap)) in fields.iter().enumerate() {
            if *heap {
                masks[i / 64] |= 1 << (i % 64);
            }
        }
        let first = masks.first().copied().unwrap_or(0);
        let mut words = vec![
            format!("{:#x}ULL", header(layout::KIND_DATA, tag)),
            format!("{:#x}ULL", layout::data_layout(len, first)),
        ];
        if len <= layout::INLINE_FIELDS {
            masks.clear();
        }
        for (field, _) in fields {
            words.push(match field {
                Const::Word(w) => format!("{w:#x}ULL"),
                Const::Code(f) => {
                    let g = prog.compiled(f).ok_or_else(|| format!("no code for {f}"))?;
                    self.slots.insert(g);
                    address(prog, &format!("&s_{}", prog.name(g)))
                }
                other => address(prog, &format!("d{}", self.datum(prog, other)?)),
            });
        }
        words.extend(masks.iter().map(|m| format!("{m:#x}ULL")));
        Ok(Datum { words })
    }

    /// The definitions of the file's slots, then of its data, each before what points to it.
    /// WebAssembly's data is of `lt_word`s, whose addresses its 32-bit relocations fill.
    pub(crate) fn definitions(&self, prog: &Program<'_>, out: &mut String) {
        let word = if prog.options.wasm { "lt_word" } else { "u64" };
        for &s in &self.slots {
            let name = prog.name(s);
            let code = address(prog, &format!("&{name}"));
            let _ = writeln!(out, "static const {word} s_{name} = {code};");
        }
        for (d, datum) in self.datums.iter().enumerate() {
            let n = datum.words.len();
            let words: Vec<String> = (datum.words.iter())
                .map(|w| {
                    if prog.options.wasm && !w.starts_with('{') {
                        format!("{{.w = {w}}}")
                    } else {
                        w.clone()
                    }
                })
                .collect();
            let words = words.join(", ");
            let _ = writeln!(out, "static const {word} d{d}[{n}] = {{{words}}};");
        }
    }
}

/// A word of static data that holds the address `of`: on WebAssembly, whose addresses are 32
/// bits, a `lt_word` whose low half the address fills.
fn address(prog: &Program<'_>, of: &str) -> String {
    if prog.options.wasm {
        format!("{{.a = (const void *){of}}}")
    } else {
        format!("(u64){of}")
    }
}

/// The first word of an immortal object's header: a count of 0, its kind and its tag.
fn header(kind: u8, tag: u16) -> u64 {
    u64::from(kind) << (8 * layout::KIND) | u64::from(tag) << (8 * layout::TAG)
}

/// The words of a string object: its header, its length and its bytes, little-endian.
fn string_words(s: &str) -> Vec<String> {
    let mut words = vec![
        format!("{:#x}ULL", header(layout::KIND_STR, 0)),
        "0ULL".to_owned(),
    ];
    words.push(format!("{}ULL", s.len()));
    for chunk in s.as_bytes().chunks(8) {
        let mut bytes = [0u8; 8];
        bytes[..chunk.len()].copy_from_slice(chunk);
        words.push(format!("{:#x}ULL", u64::from_le_bytes(bytes)));
    }
    words
}
