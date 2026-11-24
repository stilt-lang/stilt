//! The implicit row variables of non-escaping parameters (effects.non-escaping-parameters).

use stilt_hir::decls::FnSig;
use stilt_hir::hir::Mode;

use super::{Row, RowParam, Ty};

/// A signature as type checking reads it: its parameters' types and its own row, where each
/// non-escaping parameter's type `fn(A) -> B / R` is `fn(A) -> B / {R, ρ}`, with `ρ` its own
/// implicit row variable, and the own row holds every such `ρ`. `Self` means `self_ty` if it is
/// given.
#[derive(Clone, Debug)]
pub struct Passing {
    /// Each parameter's mode and type.
    pub params: Vec<(Mode, Ty)>,
    /// Its own row.
    pub row: Row,
    /// The implicit row variables, in the order of their parameters.
    pub implicit: Vec<RowParam>,
}

impl Passing {
    /// The signature `s` as type checking reads it.
    #[must_use]
    pub fn of(s: &FnSig, self_ty: Option<&Ty>) -> Self {
        let mut row = Row::from_hir(&s.row, self_ty);
        let mut implicit = Vec::new();
        let params = (0..)
            .zip(&s.params)
            .map(|(index, (mode, t))| {
                let mut t = Ty::from_hir(t, self_ty);
                // A parameter of handler type passes its effects through too
                // (handlers.handler-types).
                let passes = s.passing.get(index as usize).copied().unwrap_or(false);
                let own = match &mut t {
                    Ty::Fn(f) if passes => Some(&mut f.row),
                    Ty::Handler(h) if passes => Some(&mut h.row),
                    _ => None,
                };
                if let Some(own) = own {
                    let p = RowParam::Passed {
                        owner: s.owner.clone(),
                        index,
                    };
                    *own = own.clone().with_param(p.clone());
                    row = row.clone().with_param(p.clone());
                    implicit.push(p);
                }
                (*mode, t)
            })
            .collect();
        Self {
            params,
            row,
            implicit,
        }
    }
}

/// A signature's own row, with the implicit row variables of its non-escaping parameters, as
/// the code that calls it reads it.
#[must_use]
pub fn own_row(s: &FnSig) -> Row {
    Passing::of(s, None).row
}
