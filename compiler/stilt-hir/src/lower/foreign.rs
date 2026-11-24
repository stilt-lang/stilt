//! Names that other languages write where Stilt writes something else. Such a name that
//! doesn't resolve is still an unknown name (E0211), or a type where a value stands (E0212),
//! but its diagnostic says what Stilt writes, with the fix when one edit writes it
//! (reference/messages.md).

mod calls;
mod macros;
mod table;

use stilt_diag::{AlternativeKind, Diagnostic, Edit, Fix, codes};
use stilt_syntax::TextRange;

use super::{Ctx, Resolver, SelfKind};
use crate::hir::{Ident, Ty};
use crate::scope::Namespace;
use stilt_syntax::ast;
use table::{Entry, TYPES, VALUES, find};

/// Where a fix for a name of the table goes, if one edit writes the Stilt form.
struct Found {
    entry: &'static Entry,
    /// The span of the names that the entry is written by.
    at: TextRange,
    /// Whether writing the entry's Stilt form there is the fix: not for a type before more
    /// names, whose members may differ.
    fixed: bool,
}

impl Resolver<'_> {
    /// The diagnostic of `path`, whose first name doesn't resolve in `namespace` or in the other
    /// one: the Stilt form, if another language writes it so, else an unknown name with the
    /// closest names as its fixes. Either way, the closest names are its alternatives.
    pub(super) fn unknown_first(
        &self,
        ctx: &Ctx,
        namespace: Namespace,
        locals: bool,
        path: &[Ident],
    ) -> Diagnostic {
        let first = &path[0];
        let mut known = self.names_here(ctx, namespace, locals);
        if path.len() > 1 {
            known.extend(self.names_here(ctx, Namespace::Values, locals));
        }
        let names = known.iter().map(|n| &**n);
        let message = format!("unknown name `{}`", first.name);
        let d = Diagnostic::new(codes::E0211, first.at, message);
        let d = d.with_closest(AlternativeKind::Name, first.at, &first.name, names);
        match foreign(namespace, path) {
            Some(found) => self.translated(d, &found, path),
            None if namespace == Namespace::Values && path.len() == 1 => {
                self.own_field(ctx, d, first)
            }
            None => d,
        }
    }

    /// `d`, for `name` written in a method where its receiver's record type, declared in this
    /// module, has a field of that name, as Python's and C++'s methods read their fields: the
    /// fix reads it through `self` (records.field-access).
    fn own_field(&self, ctx: &Ctx, d: Diagnostic, name: &Ident) -> Diagnostic {
        let SelfKind::Impl(Ty::Con(item, _)) = &ctx.self_kind else {
            return d;
        };
        if !self.has_self()
            || item.home != self.module.name
            || !self.declares_field(&item.name, &name.name)
        {
            return d;
        }
        let message = format!(
            "`{0}` is a field, which a method reads as `self.{0}`",
            name.name
        );
        let mut d =
            d.with_help("A method reaches its receiver's fields through `self`, as `self.x`.");
        d.message = message;
        d.fixes.clear();
        let fix = Fix::new(
            format!("write `self.{}`", name.name),
            vec![Edit::insert(name.at.start(), "self.")],
        );
        d.with_fix(fix)
    }

    /// Whether this module's record type `ty` has a field `field`, as its declaration writes it.
    fn declares_field(&self, ty: &str, field: &str) -> bool {
        let tree = stilt_db::parse(self.db, self.module.file).tree();
        tree.items().any(|item| {
            let ast::Item::TypeDecl(t) = item else {
                return false;
            };
            let named = t
                .name()
                .and_then(|n| n.ident())
                .is_some_and(|n| n.text() == ty);
            let Some(ast::TypeDef::RecordDef(r)) = t.def().filter(|_| named) else {
                return false;
            };
            r.fields().any(|f| {
                f.name()
                    .and_then(|n| n.ident())
                    .is_some_and(|n| n.text() == field)
            })
        })
    }

    /// `d`, said as what Stilt writes for the entry found, with its fix. `this` is replaced
    /// only where `self` is in scope.
    fn translated(&self, mut d: Diagnostic, found: &Found, path: &[Ident]) -> Diagnostic {
        let written: Vec<&str> = path.iter().map(|n| &*n.name).collect();
        let written = if found.at == path[0].at {
            written[0].to_owned()
        } else {
            written.join(".")
        };
        d.fixes.clear();
        d.range = found.at;
        let (message, stilt) = if &*path[0].name == "this" && !self.has_self() {
            let message = "Stilt names the receiver `self`, and only a method that takes `self` \
                           has one";
            (message, None)
        } else {
            (
                found.entry.message,
                found.entry.stilt.filter(|_| found.fixed),
            )
        };
        d.message = message.replace('$', &written);
        let d = d.with_help(found.entry.help);
        match stilt {
            Some(c) => d.with_fix(Fix::new(
                format!("write `{c}`"),
                vec![Edit::replace(found.at, c)],
            )),
            None => d,
        }
    }

    /// Whether `self` is in scope, as a method's receiver.
    fn has_self(&self) -> bool {
        self.scope
            .iter()
            .rev()
            .any(|(n, v)| &**n == "self" && v.is_some())
    }
}

/// The entry of the table that `path` is written by: the whole path, when another language
/// writes it all, as `console.log`, or else its first name, in the namespace where it is read.
fn foreign(namespace: Namespace, path: &[Ident]) -> Option<Found> {
    let first = &path[0];
    if path.len() > 1 {
        let written: Vec<&str> = path.iter().map(|n| &*n.name).collect();
        if let Some(entry) = find(VALUES, &written.join(".")) {
            let at = first.at.cover(path[path.len() - 1].at);
            return Some(Found {
                entry,
                at,
                fixed: true,
            });
        }
    }
    let (entry, fixed) = match (namespace, path.len()) {
        (Namespace::Types, 1) => (find(TYPES, &first.name)?, true),
        (_, 1) => (find(VALUES, &first.name)?, true),
        _ => match find(TYPES, &first.name) {
            Some(entry) => (entry, false),
            None => (find(VALUES, &first.name)?, true),
        },
    };
    Some(Found {
        entry,
        at: first.at,
        fixed,
    })
}
