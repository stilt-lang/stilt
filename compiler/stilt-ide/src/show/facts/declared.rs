//! The functions that a file's module declares, as `show` addresses them, their facts not yet
//! inferred.

use stilt_db::{Database, Program, SourceFile};
use stilt_diag::LineIndex;
use stilt_mir::{Code, FnRef};

use super::Function;
use super::modes::Modes;
use super::views::Views;
use crate::text;

/// The functions that a file's module declares, in the order of their bodies, their facts not
/// yet inferred.
pub fn declared(db: &Database, program: Program, file: SourceFile) -> Vec<Function> {
    let module = stilt_hir::module_hir(db, program, file).name;
    let mut found: Vec<(u32, FnRef)> = stilt_mir::bodies(db, program)
        .code
        .iter()
        .filter_map(|(f, code)| match code {
            Code::Body(of, index) if *of == file && address(&module, f).is_some() => {
                Some((*index, f.clone()))
            }
            _ => None,
        })
        .collect();
    found.sort_by_key(|(index, _)| *index);
    let text = text(db, file);
    let lines = LineIndex::new(&text);
    let starts = stilt_hir::body_starts(db, program, file);
    let exported = exported_names(db, file);
    found
        .into_iter()
        .filter_map(|(index, code)| {
            Some(Function {
                exported: matches!(&code, FnRef::Function(item) if exported.iter().any(|n| n == item.name.as_str())),
                address: address(&module, &code)?,
                file,
                tier: stilt_types::facts::tier(db, program, file),
                index,
                line: lines.position(&text, starts[index as usize]).line,
                name_at: usize::from(starts[index as usize]),
                code,
                broken: false,
                consumes: Vec::new(),
                lost_reuse: Vec::new(),
                modes: Modes::default(),
                views: Views::default(),
                in_place: Vec::new(),
                panic: Vec::new(),
                overflow: Vec::new(),
                alloc: Vec::new(),
                div: Vec::new(),
                copy: Vec::new(),
                locks: Vec::new(),
                capabilities: Default::default(),
                atomic: Vec::new(),
                unsafe_blocks: Vec::new(),
                foreign: Vec::new(),
                proved: Vec::new(),
                locals: Vec::new(),
                reflects: Vec::new(),
            })
        })
        .collect()
}

/// The names of the functions that a file exports to C, written `pub extern fn`
/// (c.exported-functions).
fn exported_names(db: &Database, file: SourceFile) -> Vec<String> {
    stilt_db::parse(db, file)
        .tree()
        .items()
        .filter_map(|item| match item {
            stilt_syntax::ast::Item::Fn(f) if f.is_exported() => f.name().map(|n| n.text()),
            _ => None,
        })
        .collect()
}

/// How `show` addresses a function of `module`, if it is one that the source declares.
fn address(module: &str, f: &FnRef) -> Option<String> {
    match f {
        FnRef::Function(item) => Some(format!("{module}.{}", item.name)),
        FnRef::Member(owner, name) => Some(format!("{module}.{}.{name}", owner.name)),
        FnRef::ImplMethod(tr, owner, name) => {
            Some(format!("{module}.{}.{}.{name}", owner.name, tr.name))
        }
        FnRef::DefaultMethod(t, name) => Some(format!("{module}.{}.{name}", t.name)),
        _ => None,
    }
}
