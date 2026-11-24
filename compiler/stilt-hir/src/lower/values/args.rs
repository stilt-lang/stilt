//! The arguments of a named type, each read by the kind of its constructor's parameter at its
//! place (generics.value-arguments).

use stilt_diag::codes;
use stilt_syntax::SyntaxKind;
use stilt_syntax::TextRange;
use stilt_syntax::ast::{self, AstNode};
use stilt_syntax::text::number_text;

use super::super::poly::Spot;
use super::super::{Ctx, Meaning, Resolver, bare, dotted};
use super::{Constructor, Found};
use crate::hir::{Ident, Name, Ty, Value};
use crate::scope::Namespace;
use crate::values::{ConstValue, const_value, int_literal, int_range};

impl Resolver<'_> {
    /// The argument `a` at `index` of a named type whose constructor is `ctor`, if it is a
    /// declared type: a value argument where it has a value parameter, and a type elsewhere.
    /// The arguments of a head that is `broken` are read as either, so that only those that
    /// are neither report errors.
    pub(in super::super) fn type_arg(
        &mut self,
        ctx: &Ctx,
        a: ast::Type,
        (ctor, broken): (Option<&Constructor>, bool),
        index: u32,
    ) -> Ty {
        let at = self.at(bare(&a).syntax());
        match ctor.map(|c| (c, c.value_at(index))) {
            Some((c, Some(param))) => self.value_arg(ctx, &bare(&a), (c, index, param), at),
            Some((c, None)) if index < c.arity => self.arg_for_type(ctx, a, c, at),
            // An argument past the constructor's parameters, which E0300 reports, or one of a
            // constructor that isn't a declared type: a value there is no type.
            _ => match bare(&a) {
                ast::Type::ValueArg(_) => Ty::Error,
                ast::Type::NamedType(n) if broken && self.names_value(ctx, &n) => Ty::Error,
                _ => self.ty_in(ctx, Some(a), Spot::TypeArg),
            },
        }
    }

    /// Whether a named type without arguments names a value parameter or a constant, and no
    /// type, where it is written.
    fn names_value(&mut self, ctx: &Ctx, n: &ast::NamedType) -> bool {
        if n.args().next().is_some() {
            return false;
        }
        let path = self.path(n.path());
        matches!(
            self.found(ctx, &path),
            Found::ValueParam(..) | Found::Const(..)
        ) && !self.names_type_here(ctx, &path)
    }

    /// An argument given for a type parameter: a literal, a constant, a value parameter or any
    /// other name that names no type there is E0347 (generics.value-arguments).
    fn arg_for_type(&mut self, ctx: &Ctx, a: ast::Type, c: &Constructor, at: TextRange) -> Ty {
        let value = match bare(&a) {
            ast::Type::ValueArg(v) => Some(v.syntax().text().to_string()),
            ast::Type::NamedType(n) if n.args().next().is_none() => {
                let path = self.path(n.path());
                match self.found(ctx, &path) {
                    // `T.Item` names a member constant only when the type declares one, and
                    // is otherwise a member type, as it always was (traits.member-types).
                    Found::Const(item, Some(member))
                        if *const_value(self.db, self.program, item.clone(), Some(member))
                            == ConstValue::Missing =>
                    {
                        None
                    }
                    // A function, a local or a module names no type either.
                    Found::ValueParam(..) | Found::Const(..) | Found::OtherValue
                        if !self.names_type_here(ctx, &path) =>
                    {
                        Some(dotted(&path))
                    }
                    _ => None,
                }
            }
            _ => None,
        };
        let Some(value) = value else {
            return self.ty_in(ctx, Some(a), Spot::TypeArg);
        };
        let message = format!(
            "`{}` takes a type here, and `{value}` is a value: write a type",
            c.item.name
        );
        self.error(codes::E0347, at, message);
        Ty::Error
    }

    /// Whether a path names a type where the context is, as a type argument reads it first.
    fn names_type_here(&self, ctx: &Ctx, path: &[Ident]) -> bool {
        match path {
            [one] => self.lookup(ctx, Namespace::Types, false, one).is_some(),
            _ => self.constructor(ctx, path).is_some(),
        }
    }

    /// A value argument for the value parameter at `index` of `c`, of the primitive type `param`,
    /// which is empty when the parameter's own type is an error (generics.value-arguments and
    /// generics.constant-arguments and generics.array-sizes).
    fn value_arg(
        &mut self,
        ctx: &Ctx,
        a: &ast::Type,
        (c, index, param): (&Constructor, u32, Name),
        at: TextRange,
    ) -> Ty {
        match a {
            ast::Type::ValueArg(v) => self.literal_arg(v, (c, index, param), at),
            ast::Type::NamedType(n) if n.args().next().is_none() => {
                let path = self.path(n.path());
                self.named_arg(ctx, &path, (c, index, param), at)
            }
            _ => {
                let text = a.syntax().text().to_string();
                self.not_a_value(c, param, &format!("`{text}` is a type"), at)
            }
        }
    }

    /// E0347 for an argument that isn't a value, given for a value parameter of type `param`.
    fn not_a_value(&mut self, c: &Constructor, param: Name, what: &str, at: TextRange) -> Ty {
        let message = format!(
            "`{}` takes a value of type `{param}` here, and {what}: write a literal, a constant \
             or a value parameter",
            c.item.name
        );
        self.error(codes::E0347, at, message);
        Ty::Error
    }

    /// A literal value argument: an integer in the parameter's range (E0320), or a `bool` for
    /// a `bool` parameter (E0311).
    fn literal_arg(
        &mut self,
        v: &ast::ValueArg,
        (c, index, param): (&Constructor, u32, Name),
        at: TextRange,
    ) -> Ty {
        let Some(token) = v.literal() else {
            return Ty::Error;
        };
        let text = v.syntax().text().to_string();
        if param.is_empty() {
            return Ty::Error;
        }
        let value = match (token.kind(), &*param) {
            (SyntaxKind::TRUE_KW, "bool") => Value::Bool(true),
            (SyntaxKind::FALSE_KW, "bool") => Value::Bool(false),
            (SyntaxKind::INT, ty) if ty != "bool" => {
                let n = int_literal(&number_text(&token), v.is_negative());
                match (n, int_range(ty)) {
                    (Some(n), Some((lo, hi))) if lo <= n && n <= hi => Value::Int(n),
                    _ => {
                        let message = format!("`{text}` is out of range for `{param}`");
                        self.error(codes::E0320, at, message);
                        return Ty::Error;
                    }
                }
            }
            _ => {
                let message = format!(
                    "`{}` takes a value of type `{param}` here, not `{text}`",
                    c.item.name
                );
                self.error(codes::E0311, at, message);
                return Ty::Error;
            }
        };
        self.checked_size(c, index, value, &text, at)
    }

    /// The value argument `value`, unless it is a negative size of an `Array`
    /// (generics.array-sizes).
    fn checked_size(
        &mut self,
        c: &Constructor,
        index: u32,
        value: Value,
        text: &str,
        at: TextRange,
    ) -> Ty {
        if c.is_array_size(index) && matches!(value, Value::Int(n) if n < 0) {
            // A literal shows its value itself; a constant is named with it.
            let literal = text
                .trim_start_matches('-')
                .starts_with(|c: char| c.is_ascii_digit());
            let this = if literal {
                String::new()
            } else {
                format!(", and `{text}` is {value}")
            };
            let message =
                format!("an array's size is never negative{this}: give a size of 0 or more");
            self.error(codes::E0347, at, message);
            return Ty::Error;
        }
        Ty::Value(value)
    }

    /// A name given for a value parameter: a value parameter in scope or a constant, of the
    /// parameter's type (E0311), and E0347 for anything else found, E0211 for nothing.
    fn named_arg(
        &mut self,
        ctx: &Ctx,
        path: &[Ident],
        (c, index, param): (&Constructor, u32, Name),
        at: TextRange,
    ) -> Ty {
        let written = dotted(path);
        match self.found(ctx, path) {
            // A value parameter whose type is an error, which was reported where it is
            // written, stands nowhere as a value (errors.error-type).
            Found::ValueParam(_, Ty::Error) => Ty::Error,
            Found::ValueParam(g, t) => {
                let of = prim_name(&t);
                if !param.is_empty() && !of.is_empty() && of != param {
                    let message = format!(
                        "`{}` takes a value of type `{param}` here, and `{written}` is a `{of}`",
                        c.item.name
                    );
                    self.error(codes::E0311, at, message);
                    return Ty::Error;
                }
                Ty::Param(g)
            }
            Found::Const(..) => self.const_arg(ctx, path, (c, index, param), at),
            Found::Type => self.not_a_value(c, param, &format!("`{written}` is a type"), at),
            Found::OtherValue => self.not_a_value(
                c,
                param,
                &format!("`{written}` isn't known while the program is checked"),
                at,
            ),
            Found::Nothing => {
                self.walk_to_end(ctx, Namespace::Values, "a constant", path);
                Ty::Error
            }
        }
    }

    /// A constant given for a value parameter, computed while the program is checked
    /// (generics.constant-arguments): of the parameter's type (E0311), and E0347 when its
    /// computation panics.
    fn const_arg(
        &mut self,
        ctx: &Ctx,
        path: &[Ident],
        (c, index, param): (&Constructor, u32, Name),
        at: TextRange,
    ) -> Ty {
        let written = dotted(path);
        // A member constant of a type, `T.C`, or a constant that a path names through modules,
        // which records the references and the privacy that every path does.
        let (item, member) = match self.found(ctx, path) {
            Found::Const(item, Some(member)) => (item, Some(member)),
            _ => match self.walk_to_end(ctx, Namespace::Values, "a constant", path) {
                (Meaning::Item(item, _), _) => (item, None),
                _ => return Ty::Error,
            },
        };
        match const_value(self.db, self.program, item, member).clone() {
            ConstValue::Value(ty, value) if param.is_empty() || ty == param => {
                self.checked_size(c, index, value, &written, at)
            }
            ConstValue::Value(ty, _) | ConstValue::Panics(ty)
                if ty != param && !param.is_empty() =>
            {
                let message = format!(
                    "`{}` takes a value of type `{param}` here, and `{written}` is a `{ty}`",
                    c.item.name
                );
                self.error(codes::E0311, at, message);
                Ty::Error
            }
            ConstValue::Panics(_) => {
                let message = format!(
                    "computing `{written}` panics, as a unary `-` that overflows does, so it gives \
                     no value here"
                );
                self.error(codes::E0347, at, message);
                Ty::Error
            }
            ConstValue::Value(..) | ConstValue::Unknown => Ty::Error,
            ConstValue::Missing => {
                self.walk_to_end(ctx, Namespace::Values, "a constant", path);
                Ty::Error
            }
        }
    }
}

/// The name of a primitive type, as a value parameter's is, or the empty name.
fn prim_name(t: &Ty) -> Name {
    match t {
        Ty::Con(item, args) if args.is_empty() => item.name,
        _ => Name::default(),
    }
}
