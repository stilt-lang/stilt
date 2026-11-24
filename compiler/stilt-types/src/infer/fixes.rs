//! The fixes that type errors offer (goal one-diagnostic-shape): the names closest to one that a
//! lookup didn't find (closest-candidates), and edits of the function's signature, which its body's
//! spans place. A fix writes names as the module does, so that it needs no new `use`.

use stilt_diag::{Alternative, AlternativeKind, Code, Diagnostic, Edit, Fix, MAX_FIXES, codes};
use stilt_hir::hir::{self, Ident, Item};
use stilt_syntax::TextRange;

use super::{State, synonyms};
use crate::ty::Ty;

impl State<'_> {
    /// The text of a callee that names a member, as `T.ZERO`, for messages.
    pub(super) fn callee_text(&self, callee: &hir::Expr) -> String {
        match &callee.kind {
            hir::ExprKind::Member(hir::MemberOwner::Type(t), n) => {
                format!("{}.{}", self.show(&Ty::from_hir(&t.ty, None)), n.name)
            }
            hir::ExprKind::Member(hir::MemberOwner::Trait(t), n) => {
                format!("{}.{}", t.name, n.name)
            }
            _ => "it".to_owned(),
        }
    }

    /// An error, with its fixes.
    pub(super) fn error_fixed(
        &mut self,
        code: Code,
        at: TextRange,
        message: String,
        fixes: Vec<Fix>,
    ) {
        let d = fixes
            .into_iter()
            .fold(Diagnostic::new(code, at, message), Diagnostic::with_fix);
        self.errors.push(d);
    }

    /// An error at a name that a lookup didn't find, with a fix for each of the `candidates`
    /// closest to it (goal closest-candidates), and each one close to it as an alternative: a field
    /// for E0313, a method or member otherwise (admissible-alternatives). A member's name that
    /// another language gives the one Stilt names otherwise, as `length` for `len`, puts that
    /// one first, and a loop's name, as `forEach`, says that `for` writes it.
    pub(super) fn not_found<'c>(
        &mut self,
        code: Code,
        name: &Ident,
        mut message: String,
        candidates: impl IntoIterator<Item = &'c str>,
    ) {
        let kind = if code == codes::E0313 {
            AlternativeKind::Field
        } else {
            AlternativeKind::Method
        };
        let candidates: Vec<&str> = candidates.into_iter().collect();
        let member = code == codes::E0314;
        let synonym = synonyms::synonym(&name.name, &candidates).filter(|_| member);
        if let Some(s) = synonym {
            message = format!("{message}; Stilt calls it `{s}`");
        }
        let looping = member && synonym.is_none() && synonyms::is_loop(&name.name);
        if looping {
            message.push_str("; a `for` loop goes through the elements");
        }
        let iterating = member && synonym.is_none() && synonyms::is_iterator(&name.name);
        if iterating {
            message.push_str("; a collection's own methods, as `map`, take it directly");
        }
        let first = synonym.map(|s| Alternative::new(kind, s));
        let others = candidates.into_iter().filter(|c| Some(*c) != synonym);
        let mut d = Diagnostic::new(code, name.at, message)
            .with_alternatives(first)
            .with_closest(kind, name.at, &name.name, others);
        if let Some(s) = synonym {
            let fix = Fix::new(format!("write `{s}`"), vec![Edit::replace(name.at, s)]);
            d.fixes.insert(0, fix);
            d.fixes.truncate(MAX_FIXES);
        }
        if looping {
            d = d.with_help(
                "Stilt writes a loop over a collection as `for x in xs { … }`, and `map` and \
                 `filter` make new lists.",
            );
        }
        if iterating {
            d = d.with_help(
                "Lists, maps and sets have `map`, `filter`, `fold` and the rest as methods of \
                 their own, and `view.Iter.of(xs)` gives a lazy iterator.",
            );
        }
        self.errors.push(d);
    }

    /// How the module writes an item's name without a new `use`: bare for its own items and the
    /// prelude's (program.prelude-names), and after the last part of its module's name for those of
    /// a module it imports (program.what-use-binds).
    pub(super) fn spelled(&self, item: &Item) -> Option<String> {
        if item.home == self.env.module || &*item.home == "std.prelude" {
            return Some(item.name.to_string());
        }
        let module = self.env.imports.iter().find(|m| **m == item.home)?;
        let bound = module.rsplit('.').next().unwrap_or(module);
        Some(format!("{bound}.{}", item.name))
    }

    /// A type as the module writes it, if it is built from named types, type parameters and
    /// tuples.
    pub(super) fn written(&self, t: &Ty) -> Option<String> {
        let list = |ts: &[Ty]| -> Option<String> {
            let parts: Option<Vec<String>> = ts.iter().map(|t| self.written(t)).collect();
            parts.map(|p| p.join(", "))
        };
        match &self.table.shape(t) {
            Ty::Con(item, args) if args.is_empty() => self.spelled(item),
            Ty::Con(item, args) => Some(format!("{}<{}>", self.spelled(item)?, list(args)?)),
            Ty::Param(p) => Some((self.env.names)(p).to_string()),
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

    /// The fix that declares `effect` in the function's row: first in it, or last, as a
    /// `raise` is written. None if no fix may edit the signature.
    pub(super) fn row_fix(&self, effect: &str, first: bool) -> Option<Fix> {
        let s = self.env.signature?;
        Some(Fix::new(
            format!("declare `{effect}` in the signature"),
            s.row.written(effect, first),
        ))
    }

    /// The fix that declares `effect`, a `raise`, in the function's row, and marks the call at
    /// `at` with `try` unless a `try` marks it already (effects.marking), so that the call is
    /// then checked as raising.
    pub(super) fn raise_fix(&self, effect: &str, at: TextRange) -> Option<Fix> {
        let mut fix = self.row_fix(effect, false)?;
        if self.unmarked.contains(&at) {
            fix.title =
                format!("declare `{effect}` in the signature, and mark the call with `try`");
            fix.edits.push(Edit::insert(at.start(), "try "));
        }
        Some(fix)
    }

    /// The fix that bounds the function's own type parameter `param` by `traits`. None if no
    /// fix may edit the signature, or a trait's name can't be written here.
    pub(super) fn bound_fix(&self, param: &Ty, traits: &[Item]) -> Option<Fix> {
        let s = self.env.signature?;
        let Ty::Param(p) = self.table.resolve(param) else {
            return None;
        };
        let name = (self.env.names)(p);
        let &(_, at, bounded) = s.generics.iter().find(|(n, _, _)| *n == name)?;
        let written: Option<Vec<String>> = traits.iter().map(|t| self.spelled(t)).collect();
        let bounds = written?.join(" + ");
        let text = if bounded {
            format!(" + {bounds}")
        } else {
            format!(": {bounds}")
        };
        Some(Fix::new(
            format!("require `{bounds}` of `{name}`"),
            vec![Edit::insert(at, text)],
        ))
    }
}
