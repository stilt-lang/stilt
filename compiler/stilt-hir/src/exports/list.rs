//! The functions that a library of the program exports (c.exported-functions, c.exported-signatures
//! and c.static-library): those of its root package's modules written `pub extern fn`, with the C
//! types of their signatures.

use stilt_db::{Db, Program, SourceFile};
use stilt_syntax::ast::{self, DocLine};

use crate::hir::{Item, Name};
use crate::lower::module_hir;
use crate::scope::local_path;

/// A type that C takes (c.exported-signatures), as C passes it, and the address of c.types-c-takes,
/// which a foreign function takes and gives as a `c.Ptr` or a `c.Str`.
#[derive(
    Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, serde::Serialize, serde::Deserialize,
)]
pub enum CType {
    /// `i8`, C's `int8_t`.
    I8,
    /// `i16`, C's `int16_t`.
    I16,
    /// `i32`, C's `int32_t`.
    I32,
    /// `i64`, C's `int64_t`.
    I64,
    /// `u8`, C's `uint8_t`.
    U8,
    /// `u16`, C's `uint16_t`.
    U16,
    /// `u32`, C's `uint32_t`.
    U32,
    /// `u64`, C's `uint64_t`.
    U64,
    /// `f32`, C's `float`.
    F32,
    /// `f64`, C's `double`.
    F64,
    /// `bool`, C's `bool`.
    Bool,
    /// An address, which only a foreign function takes or gives.
    Ptr,
}

impl CType {
    /// The type of Stilt's name `name`, if C takes it.
    #[must_use]
    pub fn of(name: &str) -> Option<Self> {
        Some(match name {
            "i8" => Self::I8,
            "i16" => Self::I16,
            "i32" => Self::I32,
            "i64" => Self::I64,
            "u8" => Self::U8,
            "u16" => Self::U16,
            "u32" => Self::U32,
            "u64" => Self::U64,
            "f32" => Self::F32,
            "f64" => Self::F64,
            "bool" => Self::Bool,
            _ => return None,
        })
    }

    /// Its name in C, as `<stdint.h>` and `<stdbool.h>` give it.
    #[must_use]
    pub fn c_name(self) -> &'static str {
        match self {
            Self::I8 => "int8_t",
            Self::I16 => "int16_t",
            Self::I32 => "int32_t",
            Self::I64 => "int64_t",
            Self::U8 => "uint8_t",
            Self::U16 => "uint16_t",
            Self::U32 => "uint32_t",
            Self::U64 => "uint64_t",
            Self::F32 => "float",
            Self::F64 => "double",
            Self::Bool => "bool",
            Self::Ptr => "void *",
        }
    }

    /// The number of bits C passes it in.
    #[must_use]
    pub fn bits(self) -> u32 {
        match self {
            Self::I8 | Self::U8 | Self::Bool => 8,
            Self::I16 | Self::U16 => 16,
            Self::I32 | Self::U32 | Self::F32 => 32,
            Self::I64 | Self::U64 | Self::F64 | Self::Ptr => 64,
        }
    }

    /// Whether it is a signed integer, which a word holds sign-extended.
    #[must_use]
    pub fn signed(self) -> bool {
        matches!(self, Self::I8 | Self::I16 | Self::I32 | Self::I64)
    }

    /// Whether it is a float.
    #[must_use]
    pub fn float(self) -> bool {
        matches!(self, Self::F32 | Self::F64)
    }
}

/// A function that a library exports.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Export {
    /// The function, in its module.
    pub item: Item,
    /// Its C symbol, its name as written (c.exported-names).
    pub symbol: String,
    /// The first paragraph of its doc comment, a line each, which the header writes
    /// (c.library-header).
    pub doc: Vec<String>,
    /// Its parameters' types.
    pub params: Vec<CType>,
    /// Its parameters' names, as written.
    pub names: Vec<String>,
    /// Its result, or none for `()`.
    pub result: Option<CType>,
}

/// The functions that a library of the program exports, in the order of c.library-header: by their
/// modules' paths, compared as bytes, then in their modules' order. Only the root package's are
/// exported (c.exported-functions). A program with errors may give a signature C can't take, whose
/// parts are left out: such a program is never built.
#[salsa::tracked(returns(ref))]
pub fn exported(db: &dyn Db, program: Program) -> Vec<Export> {
    let mut modules: Vec<(Name, Vec<Export>)> = Vec::new();
    for &file in program.files(db) {
        if stilt_db::package_of(db, program, file) != 0 {
            continue;
        }
        let exports = file_exported(db, program, file).clone();
        modules.push((local_path(db, program, file), exports));
    }
    modules.sort_by(|a, b| a.0.as_str().cmp(b.0.as_str()));
    modules
        .into_iter()
        .flat_map(|(_, exports)| exports)
        .collect()
}

/// The functions of a file that a library exports, in its order, a query of its own so that a
/// build after an edit parses only the files that changed (goal bounded-cache).
#[salsa::tracked(returns(ref))]
fn file_exported(db: &dyn Db, program: Program, file: SourceFile) -> Vec<Export> {
    let home = module_hir(db, program, file).name;
    (stilt_db::parse(db, file).tree().items())
        .filter_map(|item| match item {
            ast::Item::Fn(f) if f.is_exported() => export(&f, home),
            _ => None,
        })
        .collect()
}

fn export(f: &ast::Fn, home: Name) -> Option<Export> {
    let symbol = f.name()?.text();
    let written: Vec<ast::Param> = f
        .param_list()
        .iter()
        .flat_map(ast::ParamList::params)
        .collect();
    let params = (written.iter())
        .map(|p| p.ty().and_then(|t| c_type(&t)))
        .collect::<Option<Vec<_>>>()?;
    let names = (written.iter())
        .map(|p| p.name().map(|n| n.text()).unwrap_or_default())
        .collect();
    let result = f.ret_type().and_then(|r| r.ty()).and_then(|t| c_type(&t));
    Some(Export {
        item: Item {
            home,
            name: Name::from(symbol.as_str()),
        },
        symbol,
        doc: f
            .docs()
            .map(|d| first_paragraph(&d.lines()))
            .unwrap_or_default(),
        params,
        names,
        result,
    })
}

/// The C type of a type that C takes, through any parentheses around it.
fn c_type(ty: &ast::Type) -> Option<CType> {
    match ty {
        ast::Type::ParenType(p) => c_type(&p.ty()?),
        ast::Type::NamedType(named) => {
            let path = named.path()?;
            let mut segments = path.segments();
            let first = segments.next()?;
            (segments.next().is_none() && named.args().next().is_none())
                .then(|| CType::of(first.text()))
                .flatten()
        }
        _ => None,
    }
}

/// The lines of a doc comment's first paragraph: its text up to its first empty line or
/// example.
fn first_paragraph(lines: &[DocLine]) -> Vec<String> {
    lines
        .iter()
        .map_while(|line| match line {
            DocLine::Text(text) if !text.trim().is_empty() => Some(text.clone()),
            _ => None,
        })
        .collect()
}
