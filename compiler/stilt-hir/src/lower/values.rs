//! Value parameters and value arguments (generics.value-parameters, generics.value-arguments and
//! generics.array-sizes).
//!
//! Whether a type's argument stands for a type or a value is read from its constructor's
//! declaration, through the value parameters its module's scope records, before the argument
//! is resolved; an argument for a type parameter is then resolved as every type is, and one for
//! a value parameter as a literal, a constant or a value parameter in scope.

mod args;

use stilt_diag::{Diagnostic, Edit, Fix, codes};
use stilt_syntax::TextRange;
use stilt_syntax::ast::{self, AstNode};

use super::{Ctx, Meaning, Resolver};
use crate::hir::{GenericId, Ident, Item, Name, Ty};
use crate::scope::{Kind, Namespace, PRELUDE, is_primitive};

/// The integer type names and `bool`, the types a value parameter may have
/// (generics.value-parameters).
pub(crate) fn is_value_type(name: &str) -> bool {
    crate::values::int_range(name).is_some() || name == "bool"
}

/// A named type's constructor, as its arguments are read: its item, its number of parameters
/// and its value parameters, each by its place with the primitive type name written for it.
pub(super) struct Constructor {
    pub(super) item: Item,
    pub(super) arity: u32,
    pub(super) values: crate::items::ValueParams,
}

impl Constructor {
    /// The type written for the value parameter at `index`, if the constructor has one there.
    pub(super) fn value_at(&self, index: u32) -> Option<Name> {
        self.values
            .iter()
            .find(|(i, _)| *i == index)
            .map(|(_, t)| *t)
    }

    /// Whether this is `std.array`'s `Array`, whose size, its second argument, is never
    /// negative (generics.array-sizes).
    pub(super) fn is_array_size(&self, index: u32) -> bool {
        &*self.item.home == "std.array" && &*self.item.name == "Array" && index == 1
    }
}

/// What a name means where an argument is written, without reporting anything.
#[derive(Clone, Debug)]
pub(super) enum Found {
    /// A value parameter in scope, with its type.
    ValueParam(GenericId, Ty),
    /// A constant of a module, or a member constant of a type.
    Const(Item, Option<Name>),
    /// A type: a primitive type name, a declared type or a type parameter.
    Type,
    /// A local, or any other item of the value namespace, as a function, or a module.
    OtherValue,
    Nothing,
}

impl Resolver<'_> {
    /// Declares the value parameter `p` at `id` (generics.value-parameters), with its type, which
    /// is an integer type or `bool`, or E0345 at the type and the error type. Its name is unique
    /// among the generics of its list and of its impl block's (E0208), and no primitive type name
    /// (lexical.primitive-type-names).
    pub(super) fn value_param(
        &mut self,
        ctx: &mut Ctx,
        p: &ast::ValueParam,
        id: GenericId,
    ) -> (Ident, Ty) {
        let n = self.name(p.name(), p.syntax());
        self.check_not_primitive(&n);
        let written = self.ty(ctx, p.ty());
        let t = match &written {
            Ty::Con(item, args)
                if args.is_empty() && &*item.home == PRELUDE && is_value_type(&item.name) =>
            {
                written
            }
            Ty::Error => Ty::Error,
            _ => {
                self.uncompared(p, &written, n.at);
                Ty::Error
            }
        };
        let taken = ctx.value_params.iter().any(|(name, ..)| *name == n.name)
            || ctx.row_vars.iter().any(|(name, _)| *name == n.name);
        if taken {
            let message = format!("`{}` is already a generic here", n.name);
            self.error(codes::E0208, n.at, message);
        } else {
            ctx.value_params.push((n.name, id, t.clone()));
        }
        (n, t)
    }

    /// E0345 at the type `written` of the value parameter `p`, with a fix that writes `i64`
    /// for a float type, the integer type that holds the most of its whole values.
    fn uncompared(&mut self, p: &ast::ValueParam, written: &Ty, name_at: TextRange) {
        let at = p.ty().map_or(name_at, |t| self.at(t.syntax()));
        let text = p
            .ty()
            .map(|t| t.syntax().text().to_string())
            .unwrap_or_default();
        let message = format!(
            "a value parameter's type is an integer type or `bool`, whose values compare \
             exactly, so two types with equal arguments are one type, and `{text}` isn't one"
        );
        let mut d = Diagnostic::new(codes::E0345, at, message);
        let float = matches!(written, Ty::Con(item, args)
            if args.is_empty() && &*item.home == PRELUDE && matches!(&*item.name, "f32" | "f64"));
        if float {
            let edits = vec![Edit::replace(at, "i64")];
            d = d.with_fix(Fix::new("use `i64`, whose values compare exactly", edits));
        }
        self.diagnostics.push(d);
    }

    /// The value parameter `n` in scope, if there is one, where the program wrote it.
    pub(super) fn value_param_named(&self, ctx: &Ctx, n: &Ident) -> Option<Meaning> {
        if self.mark_of(n.at) != 0 {
            return None;
        }
        let (_, g, t) = ctx.value_params.iter().rev().find(|(p, ..)| *p == n.name)?;
        Some(Meaning::Value(g.clone(), t.clone()))
    }

    /// generics.value-parameters-in-body: no binding in the scope of a value parameter takes its
    /// name, since a type written after it would still name the parameter.
    pub(super) fn check_binding(&mut self, n: &Ident) {
        if self.values_in_scope.contains(&n.name) {
            let message = format!(
                "`{0}` is a value parameter here, and a type written after this binding would \
                 still name the parameter, so no binding takes its name: rename this one",
                n.name
            );
            self.error(codes::E0348, n.at, message);
        }
    }

    /// The constructor that a named type's path names, if it is a declared type, found without
    /// reporting anything: its arguments are read by its parameters' kinds before it is
    /// resolved and reported as it always is.
    pub(super) fn constructor(&self, ctx: &Ctx, path: &[Ident]) -> Option<Constructor> {
        let (first, rest) = path.split_first()?;
        let found = if rest.is_empty() {
            self.lookup(ctx, Namespace::Types, false, first)
        } else {
            let (ns, last) = self.quiet_namespace(ctx, path)?;
            let entry = self.find(Namespace::Types, &ns, &last.name)?;
            let item = Item {
                home: Name::from(ns.as_str()),
                name: last.name,
            };
            Some(Meaning::Item(item, entry))
        };
        match found? {
            Meaning::Item(item, entry) if entry.kind == Kind::Type => {
                let values = self
                    .named_in(&item.home, &item.name)
                    .and_then(|named| named.value_params.clone())
                    .unwrap_or_default();
                Some(Constructor {
                    item,
                    arity: entry.arity,
                    values,
                })
            }
            _ => None,
        }
    }

    /// The module that the names of `path` but its last name, as `m.n.T`, lead to, without
    /// reporting anything, and that last name.
    fn quiet_namespace<'p>(&self, ctx: &Ctx, path: &'p [Ident]) -> Option<(String, &'p Ident)> {
        let (last, front) = path.split_last()?;
        let (first, middle) = front.split_first()?;
        let Some(Meaning::Namespace(ns)) = self.lookup(ctx, Namespace::Values, false, first) else {
            return None;
        };
        let mut ns = ns.to_string();
        for s in middle {
            let child = format!("{ns}.{}", s.name);
            if !self.map.is_namespace(&child) {
                return None;
            }
            ns = child;
        }
        Some((ns, last))
    }

    /// What `path`, written as an argument, means, without reporting anything.
    pub(super) fn found(&self, ctx: &Ctx, path: &[Ident]) -> Found {
        match path {
            [] => Found::Nothing,
            [one] => self.found_one(ctx, one),
            [ty, member] if self.names_type(ctx, ty) => {
                let item = match self.lookup(ctx, Namespace::Types, false, ty) {
                    Some(Meaning::Item(item, _)) => item,
                    _ => Item {
                        home: Name::from(PRELUDE),
                        name: ty.name,
                    },
                };
                Found::Const(item, Some(member.name))
            }
            _ => {
                let Some((ns, last)) = self.quiet_namespace(ctx, path) else {
                    return Found::Nothing;
                };
                let item = Item {
                    home: Name::from(ns.as_str()),
                    name: last.name,
                };
                match self.find(Namespace::Values, &ns, &last.name) {
                    Some(e) if e.kind == Kind::Const => Found::Const(item, None),
                    Some(_) => Found::OtherValue,
                    None if self.find(Namespace::Types, &ns, &last.name).is_some() => Found::Type,
                    None => Found::Nothing,
                }
            }
        }
    }

    /// Whether a name, the first of a path of two, names a type whose member constant the
    /// second may be: a primitive type name, or a declared type.
    fn names_type(&self, ctx: &Ctx, n: &Ident) -> bool {
        is_primitive(&n.name)
            || matches!(
                self.lookup(ctx, Namespace::Types, false, n),
                Some(Meaning::Item(_, e)) if e.kind == Kind::Type
            )
    }

    fn found_one(&self, ctx: &Ctx, n: &Ident) -> Found {
        if is_primitive(&n.name) {
            return Found::Type;
        }
        if let Some(Meaning::Value(g, t)) = self.value_param_named(ctx, n) {
            return Found::ValueParam(g, t);
        }
        match self.lookup(ctx, Namespace::Values, true, n) {
            Some(Meaning::Item(item, e)) if e.kind == Kind::Const => {
                return Found::Const(item, None);
            }
            Some(Meaning::Broken) => return Found::Nothing,
            Some(_) => return Found::OtherValue,
            None => {}
        }
        match self.lookup(ctx, Namespace::Types, false, n) {
            Some(Meaning::Broken) | None => Found::Nothing,
            Some(_) => Found::Type,
        }
    }
}
