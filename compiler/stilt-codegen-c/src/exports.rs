//! The end of a library's `program.c` (c.exported-functions, c.calls-from-c and c.static-library):
//! for each exported function, a C function under its own name, which takes and returns its values
//! as C passes them, makes the runtime ready, through `stilt_runtime_once`, calls the compiled
//! function with each value in a word, as compiled code holds it, and makes what the call wrote
//! reach its file. `stilt_runtime_once` is defined here, so that a C program that links two Stilt
//! libraries is rejected by its linker.

use std::fmt::Write as _;

use stilt_mir::{CType, Export, FnRef};

use crate::names::c_string;
use crate::program::Program;

/// The C type that `<stdint.h>` and `<stdbool.h>` name `t`, by the compiler's own name of it,
/// since the C includes no system header.
pub(crate) fn c_type(t: CType) -> &'static str {
    match t {
        CType::I8 => "__INT8_TYPE__",
        CType::I16 => "__INT16_TYPE__",
        CType::I32 => "__INT32_TYPE__",
        CType::I64 => "__INT64_TYPE__",
        CType::U8 => "__UINT8_TYPE__",
        CType::U16 => "__UINT16_TYPE__",
        CType::U32 => "__UINT32_TYPE__",
        CType::U64 => "__UINT64_TYPE__",
        CType::F32 => "float",
        CType::F64 => "double",
        CType::Bool => "_Bool",
        CType::Ptr => "void *",
    }
}

/// The word that compiled code holds `x`, of type `t`, in: an integer extended by its sign or
/// with zeros, a `bool` as 0 or 1, an `f64`'s bits, and an `f32`'s bits in the low half.
pub(crate) fn to_word(out: &mut String, word: &str, x: &str, t: CType) {
    let _ = match t {
        CType::F64 => writeln!(out, "u64 {word}; __builtin_memcpy(&{word}, &{x}, 8);"),
        CType::F32 => writeln!(
            out,
            "__UINT32_TYPE__ {word}_bits; __builtin_memcpy(&{word}_bits, &{x}, 4); u64 {word} = {word}_bits;"
        ),
        _ if t.signed() => writeln!(out, "u64 {word} = (u64)(i64){x};"),
        _ => writeln!(out, "u64 {word} = (u64){x};"),
    };
}

/// Returns the value of type `t` that the word `word` holds.
fn from_word(out: &mut String, word: &str, t: CType) {
    let _ = match t {
        CType::F64 => writeln!(out, "double x; __builtin_memcpy(&x, &{word}, 8); return x;"),
        CType::F32 => writeln!(
            out,
            "__UINT32_TYPE__ bits = (__UINT32_TYPE__){word}; float x; __builtin_memcpy(&x, &bits, 4); return x;"
        ),
        CType::Bool => writeln!(out, "return {word} != 0;"),
        _ => writeln!(out, "return ({}){word};", c_type(t)),
    };
}

/// The indexes of the exported functions' compiled code, in the order of `exports`.
pub(crate) fn compiled(prog: &Program<'_>, exports: &[Export]) -> Result<Vec<usize>, String> {
    (exports.iter())
        .map(|e| {
            (prog.compiled(&FnRef::Function(e.item.clone())))
                .ok_or_else(|| format!("{} wasn't compiled", e.symbol))
        })
        .collect()
}

/// The end of `program.c`: the table of the program's files, `stilt_runtime_once`, and the C
/// function of each export, whose compiled code is at `code`.
pub(crate) fn wrappers(prog: &Program<'_>, exports: &[Export], code: &[usize]) -> String {
    let mut table = Vec::new();
    for path in prog.files {
        table.extend_from_slice(path.as_bytes());
        table.push(0);
    }
    let mut out = format!(
        "static const char lt_files[] = {};\nvoid stilt_rt_ready(u64 files);\nvoid stilt_rt_returned(void);\nvoid stilt_runtime_once(void) {{ stilt_rt_ready((u64)lt_files); }}\n",
        c_string(&table)
    );
    for (export, &g) in exports.iter().zip(code) {
        let params: Vec<String> = (export.params.iter().enumerate())
            .map(|(i, &t)| format!("{} x{i}", c_type(t)))
            .collect();
        let params = if params.is_empty() {
            "void".to_owned()
        } else {
            params.join(", ")
        };
        let result = export.result.map_or("void", c_type);
        let _ = writeln!(
            out,
            "{result} {}({params}) {{\nstilt_runtime_once();",
            export.symbol
        );
        let mut args = vec!["(u64)0".to_owned()];
        for (i, &t) in export.params.iter().enumerate() {
            to_word(&mut out, &format!("w{i}"), &format!("x{i}"), t);
            args.push(format!("w{i}"));
        }
        let _ = writeln!(
            out,
            "lt_ret r = {}({});\nstilt_rt_returned();",
            prog.name(g),
            args.join(", ")
        );
        match export.result {
            Some(t) => from_word(&mut out, "r.a", t),
            None => out.push_str("(void)r;\n"),
        }
        out.push_str("}\n");
    }
    out
}
