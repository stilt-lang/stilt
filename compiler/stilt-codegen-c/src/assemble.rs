//! Putting a program's C together, one file per module and `program.c`: each
//! starts with the header, then declares what its functions name, defines its static data and
//! slots, and defines its functions. `program.c` holds the code that no module holds, such as
//! the program's entry and the methods of structural impls, the constants' cells and the code
//! that computes each, and C's `main`. A function is `static` unless another file names it.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write;

use stilt_mir::mir::{Repr, offsets};
use stilt_mir::{Export, FnRef};

use crate::file::FileData;
use crate::function::{function, prototype};
use crate::names::{c_string, file_name};
use crate::program::{Program, Refs};
use crate::stmts::{Count, count_code};

/// A C file of a program.
#[derive(Debug)]
pub struct Source {
    /// The file's name.
    pub name: String,
    /// Its C code.
    pub text: String,
}

/// One file's functions, with their bodies, what they name and the file's data.
#[derive(Debug)]
struct Unit {
    module: Option<String>,
    bodies: Vec<(usize, String)>,
    refs: Refs,
    data: FileData,
}

/// The module a function's code comes from, which names its file, or none for code the
/// compiler makes apart from any module's.
fn home(f: &FnRef) -> Option<String> {
    match f {
        FnRef::Function(i)
        | FnRef::Member(i, _)
        | FnRef::Const(i)
        | FnRef::MemberConst(i, _)
        | FnRef::DefaultMethod(i, _)
        | FnRef::ImplMethod(_, i, _) => Some(i.home.to_string()),
        FnRef::Closure(g, _)
        | FnRef::Instance(g, _)
        | FnRef::Value(g)
        | FnRef::Specialized(g, _) => home(g),
        _ => None,
    }
}

/// The program's files: one per module, in the order of their names, then `program.c`, which
/// ends with C's `main`, or for a library with the C functions of `exports` (c.exported-functions).
pub(crate) fn assemble(
    prog: &mut Program<'_>,
    exports: Option<&[Export]>,
) -> Result<Vec<Source>, String> {
    let roots = match exports {
        Some(exports) => crate::exports::compiled(prog, exports)?,
        None => vec![(prog.compiled(&FnRef::Main)).ok_or("the program has no entry")?],
    };
    let mut groups: BTreeMap<Option<String>, Vec<usize>> = BTreeMap::new();
    groups.insert(None, Vec::new());
    for (i, f) in prog.functions.iter().enumerate() {
        groups.entry(home(&f.name)).or_default().push(i);
    }
    let mut file_of = vec![0; prog.functions.len()];
    let mut units = Vec::with_capacity(groups.len());
    for (k, (module, functions)) in groups.into_iter().enumerate() {
        let mut unit = Unit {
            module,
            bodies: Vec::with_capacity(functions.len()),
            refs: Refs::default(),
            data: FileData::default(),
        };
        for i in functions {
            file_of[i] = k;
            let (body, refs) = function(prog, &mut unit.data, i)?;
            unit.refs.extend(&refs);
            unit.bodies.push((i, body));
        }
        units.push(unit);
    }
    // `program.c`, the first unit, names the entry, or the exported functions, and the code of
    // every constant.
    units[0].refs.functions.extend(roots.iter().copied());
    let cells: Vec<usize> = (prog.cells.iter())
        .filter_map(|c| prog.compiled(&c.f))
        .collect();
    units[0].refs.functions.extend(cells);
    units[0].refs.cells.extend(0..prog.cells.len());
    let mut external = vec![false; prog.functions.len()];
    for (k, unit) in units.iter().enumerate() {
        for &g in named(unit) {
            external[g] |= file_of[g] != k;
        }
    }
    let mut sources: Vec<Source> = (units.iter().enumerate())
        .map(|(k, unit)| Source {
            name: file_name(unit.module.as_deref()),
            text: text(prog, unit, k == 0, &|g| {
                if file_of[g] != k || external[g] {
                    ""
                } else {
                    "static "
                }
            }),
        })
        .collect();
    let program = sources.remove(0);
    let end = match exports {
        Some(exports) => crate::exports::wrappers(prog, exports, &roots),
        None => c_main(prog, roots[0]),
    };
    sources.push(Source {
        text: program.text + &end,
        ..program
    });
    Ok(sources)
}

/// The functions a unit's code names.
fn named(unit: &Unit) -> impl Iterator<Item = &usize> {
    (unit.refs.functions.iter())
        .chain(&unit.refs.slots)
        .chain(&unit.data.slots)
}

/// A file's text: the header, the declarations of what it names, its data and slots, the
/// cells, defined in `program.c`, and its functions, of the linkage `linkage` gives each.
fn text(
    prog: &Program<'_>,
    unit: &Unit,
    program: bool,
    linkage: &dyn Fn(usize) -> &'static str,
) -> String {
    let mut out = crate::header::header();
    for name in &unit.refs.externs {
        let _ = writeln!(out, "{}", prog.externs[name]);
    }
    let mut declared: BTreeSet<usize> = named(unit).copied().collect();
    declared.extend(unit.bodies.iter().map(|(i, _)| *i));
    for &i in &declared {
        let _ = writeln!(out, "{};", prototype(prog, i, linkage(i)));
    }
    out.push_str("void lt_release_constants(void);\n");
    unit.data.definitions(prog, &mut out);
    for &c in &unit.refs.cells {
        let cell = &prog.cells[c];
        let n = 1 + offsets(cell.words.iter().copied()).1;
        let name = &cell.name;
        if program {
            let _ = writeln!(out, "u64 k_{name}[{n}];");
            compute(prog, c, &mut out);
        } else {
            let _ = writeln!(
                out,
                "extern u64 k_{name}[{n}];\nvoid lt_compute_{name}(u64 loc);"
            );
        }
        let _ = writeln!(
            out,
            "LT_INLINE u64 lt_cell_{name}(u64 loc) {{ if (LT_UNLIKELY(!(__atomic_load_n(&k_{name}[0], __ATOMIC_ACQUIRE) & 1))) lt_compute_{name}(loc); return (u64)k_{name}; }}"
        );
    }
    for (i, body) in &unit.bodies {
        let _ = write!(out, "{} {body}", prototype(prog, *i, linkage(*i)));
    }
    if program {
        release_constants(prog, &mut out);
    }
    out
}

/// The function that releases the constants' values that were computed, which the entry
/// calls last.
fn release_constants(prog: &Program<'_>, out: &mut String) {
    out.push_str("void lt_release_constants(void) {\n");
    for cell in &prog.cells {
        let _ = writeln!(out, "if (k_{}[0] == 1) {{", cell.name);
        each_word(&cell.words, &format!("k_{}", cell.name), Count::Drop, out);
        out.push_str("}\n");
    }
    out.push_str("}\n");
}

/// Counts each heap word of a cell's value, in the array `cell`.
fn each_word(words: &[Repr], cell: &str, count: Count, out: &mut String) {
    let (at, _) = offsets(words.iter().copied());
    for (&repr, i) in words.iter().zip(at) {
        let v = match repr {
            Repr::Array(_) => format!("(u64)&{cell}[{}]", 1 + i),
            _ => format!("{cell}[{}]", 1 + i),
        };
        count_code(out, &v, repr, count, &|_| "0".to_owned());
    }
}

/// The code that computes constant `c` into its cell, once a thread claims it, marks what its
/// value reaches shared, since every thread may read it, and says it is computed.
fn compute(prog: &Program<'_>, c: usize, out: &mut String) {
    let cell = &prog.cells[c];
    let k = format!("k_{}", cell.name);
    let _ = writeln!(out, "void lt_compute_{}(u64 loc) {{", cell.name);
    let _ = writeln!(out, "if (!stilt_rt_constant_claim((u64){k})) return;");
    if let Some(g) = prog.compiled(&cell.f) {
        let name = prog.name(g);
        match prog.functions[g].results {
            0 => {
                let _ = writeln!(out, "(void){name}(loc);");
            }
            1 => {
                let _ = writeln!(out, "{k}[1] = {name}(loc).a;");
            }
            _ => {
                let _ = writeln!(out, "(void){name}(loc, &{k}[1]);");
            }
        }
    }
    each_word(&cell.words, &k, Count::Share, out);
    let _ = writeln!(out, "stilt_rt_constant_done((u64){k});\n}}");
}

/// C's `main`, which returns `stilt_rt_start` of its arguments, the entry, the table of the
/// program's files, each ended by a NUL and the whole by an empty one, and whether the program
/// checks its counts at its end (cycles.check-at-exit). WASI's start calls the
/// `main` of a freestanding program by the name clang gives a hosted one's, and the runtime
/// reaches the stack pointer through the functions after it.
fn c_main(prog: &Program<'_>, main: usize) -> String {
    let mut table = Vec::new();
    for path in prog.files {
        table.extend_from_slice(path.as_bytes());
        table.push(0);
    }
    let name = if prog.options.wasm {
        "__main_argc_argv"
    } else {
        "main"
    };
    let mut out = format!(
        "static const char lt_files[] = {};\nint {name}(int argc, char **argv) {{ return (int)stilt_rt_start((u64)argc, (u64)argv, (u64)&{}, (u64)lt_files, {}); }}\n",
        c_string(&table),
        prog.name(main),
        u8::from(prog.options.counts)
    );
    if prog.options.wasm {
        out.push_str(STACK_POINTER);
    }
    out
}

/// The functions through which the runtime reads the stack pointer of WebAssembly's C stack,
/// and moves it to the stack of a body that resumes (`stilt_runtime`'s `fiber`).
const STACK_POINTER: &str = "\
__UINTPTR_TYPE__ stilt_rt_stack_pointer(void) { __UINTPTR_TYPE__ sp; __asm__ volatile(\"global.get __stack_pointer\\n\\tlocal.set %0\" : \"=r\"(sp)); return sp; }
void stilt_rt_set_stack_pointer(__UINTPTR_TYPE__ sp) { __asm__ volatile(\"local.get %0\\n\\tglobal.set __stack_pointer\" : : \"r\"(sp)); }
";
