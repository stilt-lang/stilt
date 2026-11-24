//! What the later phases know of a function's signature beyond its typed body: the names of its
//! row variables and parameters, and the fixes that edit it (goal one-diagnostic-shape).

use stilt_diag::{Edit, Fix};
use stilt_hir::hir::{GenericId, Name, SignatureSpans};
use stilt_syntax::TextRange;

use crate::ty::{RowParam, Table, Ty};

/// A function's signature, for the messages and fixes of the later phases. Other bodies have no
/// parameters and no spans.
pub(crate) struct SigInfo<'a> {
    /// The names of type parameters and written row variables.
    pub(crate) names: &'a dyn Fn(&GenericId) -> Name,
    /// The function's parameters, its receiver's first: each one's name and where it is.
    pub(crate) params: Vec<(Name, TextRange)>,
    /// Where fixes may edit the signature: none for a method whose trait's signature binds it.
    pub(crate) spans: Option<&'a SignatureSpans>,
    /// The module's dotted name, and the modules it imports, by which a fix writes a type.
    pub(crate) module: &'a str,
    pub(crate) imports: &'a [Name],
    /// Whether the function's declared error type had an error, and is the error type, from
    /// which no diagnostic arises (errors.error-type).
    pub(crate) raise_broken: bool,
    /// The body's text from its start, which a fix may copy, read only when one does.
    pub(crate) text: &'a dyn Fn() -> Option<String>,
    /// The line, counted from 1, of an offset relative to the body's start, which E0204 names
    /// (facts.closest-rule).
    pub(crate) line: &'a dyn Fn(stilt_syntax::TextSize) -> u32,
    /// Where a function's block ends, after its closing brace.
    pub(crate) block_end: Option<stilt_syntax::TextSize>,
    /// Whether the function is a projection, whose body yields exactly once
    /// (projections.once-on-every-path).
    pub(crate) projection: bool,
    /// The errors of the analyses that resolution found where the body writes types
    /// (views.viewable-types and views.view-types), which the analyses report.
    pub(crate) analysed: &'a [stilt_diag::Diagnostic],
}

impl SigInfo<'_> {
    /// Where the body's block ends: after a function's closing brace, and otherwise after its
    /// last statement.
    pub(crate) fn end(&self, block: &crate::tast::Block) -> stilt_syntax::TextSize {
        self.block_end
            .unwrap_or_else(|| block.last().map_or_else(Default::default, |s| s.at.end()))
    }
}

impl SigInfo<'_> {
    /// A row variable's name: a written one's own, and an implicit one's parameter's.
    pub(crate) fn row_param_name(&self, p: &RowParam) -> Name {
        match p {
            RowParam::Written(g) => (self.names)(g),
            RowParam::Passed { index, .. } => self
                .params
                .get(*index as usize)
                .map_or_else(|| Name::from("_"), |(n, _)| *n),
        }
    }

    /// The parameter whose implicit row variable `p` is, by its place among the parameters.
    pub(crate) fn passed_index(p: &RowParam) -> Option<usize> {
        match p {
            RowParam::Passed { index, .. } => Some(*index as usize),
            RowParam::Written(_) => None,
        }
    }

    /// A type as the module writes it, if it is built from named types, type parameters and
    /// tuples whose names it can write without a new `use`.
    pub(crate) fn written(&self, t: &Ty) -> Option<String> {
        let list = |ts: &[Ty]| -> Option<String> {
            let parts: Option<Vec<String>> = ts.iter().map(|t| self.written(t)).collect();
            parts.map(|p| p.join(", "))
        };
        let spelled = |item: &stilt_hir::hir::Item| -> Option<String> {
            if *item.home == *self.module || &*item.home == "std.prelude" {
                return Some(item.name.to_string());
            }
            let module = self.imports.iter().find(|m| **m == item.home)?;
            let bound = module.rsplit('.').next().unwrap_or(module);
            Some(format!("{bound}.{}", item.name))
        };
        match t {
            Ty::Con(item, args) if args.is_empty() => spelled(item),
            Ty::Con(item, args) => Some(format!("{}<{}>", spelled(item)?, list(args)?)),
            Ty::Param(p) => Some((self.names)(p).to_string()),
            Ty::Tuple(ts) if ts.len() == 1 => Some(format!("({},)", self.written(&ts[0])?)),
            Ty::Tuple(ts) => Some(format!("({})", list(ts)?)),
            Ty::Spread(s) => Some(format!("..{}", self.written(&s.elem)?)),
            Ty::Handler(_)
            | Ty::SelfTy
            | Ty::App(..)
            | Ty::Fn(_)
            | Ty::Var(_)
            | Ty::Value(_)
            | Ty::Error => None,
        }
    }

    /// A type for a message, as a program would write it.
    pub(crate) fn show(&self, t: &Ty) -> String {
        Table::default().show(t, self.names)
    }

    /// The edits that write `raise<{error}>` in the row of the function type of the parameter
    /// at `index`. None if no fix may edit the signature.
    pub(crate) fn raise_in_param(&self, index: usize, error: &str) -> Option<Vec<Edit>> {
        self.in_param_row(index, &format!("raise<{error}>"))
    }

    /// The edits that write the row element `element` in the row of the function type of the
    /// parameter at `index`. None if no fix may edit the signature.
    pub(crate) fn in_param_row(&self, index: usize, element: &str) -> Option<Vec<Edit>> {
        let row = self.spans?.params.get(index)?.as_ref()?;
        Some(row.written(element, false))
    }

    /// A name for a new type parameter that no generic of the function has, and the edit that
    /// declares it. None if no fix may edit the signature.
    pub(crate) fn new_type_param(&self) -> Option<(String, Edit)> {
        let s = self.spans?;
        let taken = |n: &str| s.generics.iter().any(|(g, _, _)| &**g == n);
        let name = std::iter::once("E".to_owned())
            .chain((2..=s.generics.len() + 1).map(|i| format!("E{i}")))
            .find(|n| !taken(n))?;
        let edit = match s.generics.last() {
            Some(&(_, end, _)) => Edit::insert(end, format!(", {name}")),
            None => Edit::insert(s.generics_at, format!("<{name}>")),
        };
        Some((name, edit))
    }

    /// The fix that writes `escaping` before the parameter at `index`. None if no fix may edit
    /// the signature.
    pub(crate) fn escaping_fix(&self, index: usize) -> Option<Fix> {
        self.spans?;
        let (name, at) = self.params.get(index)?;
        Some(Fix::new(
            format!("mark `{name}` `escaping`, so its row is exactly the one written"),
            vec![Edit::insert(at.start(), "escaping ")],
        ))
    }
}
