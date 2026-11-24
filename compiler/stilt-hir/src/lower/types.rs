//! Types, rows and generics, in signatures and in bodies (declarations.type-parameters;
//! effects.rows; traits.bounded-blocks).

use stilt_diag::{AlternativeKind, Diagnostic, Edit, Fix, codes};
use stilt_syntax::TextRange;
use stilt_syntax::ast::{self, AstNode};

use super::poly::Spot;
use super::{Ctx, Meaning, Resolver, SelfKind, bare, dotted};
use crate::hir::{GenericId, Ident, Item, Name, Row, TraitRef, Ty, TypeRef};
use crate::scope::{Entry, Kind, Namespace};

/// The effects that are inferred and never written (facts.implicit-effects, and effects.rows).
const IMPLICIT_EFFECTS: [&str; 2] = ["panic", "alloc"];

impl Resolver<'_> {
    /// program.private-in-signatures: a private item can't appear in a signature that other modules
    /// see.
    pub(super) fn check_public(&mut self, ctx: &Ctx, at: TextRange, item: &Item, entry: Entry) {
        if ctx.public && item.home == self.module.name && !entry.is_pub {
            let message = format!(
                "`{}` is private, but appears in a signature that other modules see",
                item.name
            );
            let public = self.declared.get(&item.name).map(|&start| {
                let title = format!("make `{}` public", item.name);
                Fix::new(title, vec![Edit::insert(start, "pub ")])
            });
            let d = Diagnostic::new(codes::E0214, at, message);
            self.diagnostics
                .push(public.into_iter().fold(d, Diagnostic::with_fix));
        }
    }

    pub(super) fn trait_ref(&mut self, ctx: &Ctx, path: &[Ident]) -> TraitRef {
        let Some(first) = path.first() else {
            return TraitRef::Error;
        };
        match self.walk_to_end(ctx, Namespace::Types, "a trait", path) {
            (Meaning::Broken, _) => TraitRef::Error,
            (Meaning::Item(item, entry), _) if entry.kind == Kind::Trait => {
                self.check_public(ctx, first.at, &item, entry);
                TraitRef::Trait(item, Vec::new())
            }
            (m, last) => {
                self.wrong_kind(&path[last], &m, "a trait");
                TraitRef::Error
            }
        }
    }

    /// A type constructor of `arity` parameters applied to `args`, or E0300 for another number
    /// of them (declarations.type-arguments).
    fn with_args(
        &mut self,
        ty: Ty,
        (arity, args): (u32, Vec<Ty>),
        path: &[Ident],
        at: TextRange,
    ) -> Ty {
        let given = u32::try_from(args.len()).unwrap_or(u32::MAX);
        if given != arity {
            let message = format!(
                "`{}` takes {arity} type argument{}, not {given}",
                dotted(path),
                if arity == 1 { "" } else { "s" }
            );
            self.error(codes::E0300, at, message);
            return Ty::Error;
        }
        match ty {
            Ty::Con(item, _) => Ty::Con(item, args),
            ty => ty,
        }
    }

    /// A type constructor whose last parameter is a pack, of `arity` parameters, applied to
    /// `args`: those after the others are the pack's, given as a tuple of them, and fewer than
    /// the others are E0300 (variadics.packs).
    fn with_pack(
        &mut self,
        item: Item,
        (arity, mut args): (u32, Vec<Ty>),
        path: &[Ident],
        at: TextRange,
    ) -> Ty {
        let others = arity.saturating_sub(1) as usize;
        if args.is_empty() {
            return Ty::Con(item, Vec::new());
        }
        if args.len() < others {
            let message = format!(
                "`{}` takes at least {others} type argument{}, then its pack's",
                dotted(path),
                if others == 1 { "" } else { "s" }
            );
            self.error(codes::E0300, at, message);
            return Ty::Error;
        }
        let pack = args.split_off(others);
        args.push(Ty::Tuple(pack));
        Ty::Con(item, args)
    }

    /// A type written where a polymorphic function type may not stand (polymorphism.placement).
    pub(super) fn ty(&mut self, ctx: &Ctx, t: Option<ast::Type>) -> Ty {
        self.ty_in(ctx, t, Spot::Other)
    }

    /// The arguments of a named type, each read by the kind of its constructor's parameter at
    /// its place (generics.value-arguments).
    fn type_args(&mut self, ctx: &Ctx, named: &ast::NamedType, path: &[Ident]) -> Vec<Ty> {
        let ctor = self.constructor(ctx, path);
        let broken = ctor.is_none() && self.head_broken(ctx, path);
        (0..)
            .zip(named.args())
            .map(|(i, a)| self.type_arg(ctx, a, (ctor.as_ref(), broken), i))
            .collect()
    }

    /// Whether the head of a named type fails to resolve or names a declaration with an error,
    /// whose arguments are then read as either a type or a value (generics.value-arguments;
    /// errors.error-type and errors.root-causes, errors.syntax-errors, errors.parts,
    /// errors.invalid-source-text, errors.breaks, errors.resuming, errors.part-reports,
    /// errors.broken-parts, errors.broken-blocks, errors.declarations-with-errors,
    /// errors.error-type-raises, errors.unknown-names, errors.phases, errors.phase-by-form and
    /// errors.warnings-with-errors).
    fn head_broken(&self, ctx: &Ctx, path: &[Ident]) -> bool {
        match path {
            [one] => {
                &*one.name != "Self"
                    && matches!(
                        self.lookup(ctx, Namespace::Types, false, one),
                        None | Some(Meaning::Broken)
                    )
            }
            _ => !self.is_member_path(ctx, path),
        }
    }

    /// A type written at `spot`, which only [`Spot::Param`] lets be a polymorphic function
    /// type (polymorphism.placement).
    pub(super) fn ty_in(&mut self, ctx: &Ctx, t: Option<ast::Type>, spot: Spot) -> Ty {
        match t {
            // A splice stands only in a quote, whose contents [`Resolver::quote`] reads.
            None | Some(ast::Type::SpliceType(_)) => Ty::Error,
            Some(ast::Type::NamedType(named)) => {
                let path = self.path(named.path());
                let args = self.type_args(ctx, &named, &path);
                let Some(first) = path.first() else {
                    return Ty::Error;
                };
                let at = self.at(named.syntax());
                if self.is_member_path(ctx, &path) {
                    return self.member_type(ctx, &path, at);
                }
                let (ty, arity) = match self.walk_to_end(ctx, Namespace::Types, "a type", &path) {
                    (Meaning::Broken, _) => return Ty::Error,
                    (Meaning::Param(v), _)
                        if ctx.packs.contains(&v) || self.misplaced.contains(&v) =>
                    {
                        return self.pack_use(v, &first.name, at);
                    }
                    (Meaning::Param(v), _) => {
                        if let Some(&(_, n)) = ctx.constructors.iter().find(|(c, _)| *c == v) {
                            return self.applied(Ty::Param(v), args, n, &path, at);
                        }
                        (Ty::Param(v), 0)
                    }
                    (Meaning::SelfType(Ty::SelfTy), _) if self_arity(ctx) > 0 => {
                        return self.applied(Ty::SelfTy, args, self_arity(ctx), &path, at);
                    }
                    // `Self` is the impl block's type, with its arguments.
                    (Meaning::SelfType(t), _) if args.is_empty() => return t,
                    (Meaning::SelfType(t), _) => (t, 0),
                    (Meaning::Item(item, entry), _) if entry.kind == Kind::Type => {
                        self.check_public(ctx, first.at, &item, entry);
                        if entry.pack {
                            return self.with_pack(item, (entry.arity, args), &path, at);
                        }
                        (Ty::Con(item, Vec::new()), entry.arity)
                    }
                    (m, last) => return self.not_a_type(&path[last], &m, spot, at),
                };
                self.with_args(ty, (arity, args), &path, at)
            }
            Some(ast::Type::TupleType(t)) => self.tuple_type(ctx, &t),
            Some(ast::Type::ParenType(t)) => self.ty_in(ctx, t.ty(), spot),
            Some(ast::Type::RecordType(r)) => self.record_type(ctx, &r, spot),
            Some(ast::Type::SpreadType(s)) => self.spread_type(ctx, &s),
            Some(ast::Type::FnType(f)) => self.fn_type(ctx, &f, spot),
            Some(ast::Type::HandlerType(h)) => self.handler_type(ctx, &h),
            Some(ast::Type::MacroType(m)) => self.macro_type(ctx, &m, spot),
            // A value written where no constructor's value parameter reads it.
            Some(ast::Type::ValueArg(v)) => {
                let message = format!("`{}` is a value, not a type", v.syntax().text());
                self.error(codes::E0347, self.at(v.syntax()), message);
                Ty::Error
            }
        }
    }

    /// A name that names no type where one is written: E0347 where it is a type parameter's
    /// argument (generics.value-arguments), and E0212 elsewhere.
    fn not_a_type(&mut self, name: &Ident, m: &Meaning, spot: Spot, at: TextRange) -> Ty {
        if spot == Spot::TypeArg {
            let what = m.describe();
            let message = format!(
                "`{}` is {what}, but a type parameter takes a type",
                name.name
            );
            self.error(codes::E0347, at, message);
        } else {
            self.wrong_kind(name, m, "a type");
        }
        Ty::Error
    }

    /// A tuple type. A spread in it whose type is an error leaves the tuple's length unknown, so
    /// the tuple is the error type, and nothing that uses it is reported (errors.error-type).
    fn tuple_type(&mut self, ctx: &Ctx, t: &ast::TupleType) -> Ty {
        let mut lost = false;
        let elems = t
            .types()
            .map(|t| {
                let spread = matches!(t, ast::Type::SpreadType(_));
                let ty = self.ty_in(ctx, Some(t), Spot::Tuple);
                lost |= spread && ty == Ty::Error;
                ty
            })
            .collect();
        if lost { Ty::Error } else { Ty::Tuple(elems) }
    }

    /// Whether a path of a type is a member type, `C.Item`, or a name that could be one if it
    /// named a type parameter, as `Point.Item` (traits.member-types), rather than a path through
    /// modules.
    fn is_member_path(&self, ctx: &Ctx, path: &[Ident]) -> bool {
        let [base, _] = path else { return false };
        &*base.name == "Self"
            || matches!(
                self.lookup(ctx, Namespace::Types, false, base),
                Some(Meaning::Param(_) | Meaning::SelfType(_) | Meaning::Item(..))
            )
    }

    /// A constructor parameter, or a constructor trait's `Self`, applied to `args`, which must
    /// be as many as its arity `n` (traits.constructor-traits and traits.constructor-parameters).
    fn applied(&mut self, head: Ty, args: Vec<Ty>, n: u32, path: &[Ident], at: TextRange) -> Ty {
        let given = u32::try_from(args.len()).unwrap_or(u32::MAX);
        if given == n {
            return Ty::App(Box::new(head), args);
        }
        let plural = if n == 1 { "" } else { "s" };
        let message = if given == 0 {
            format!(
                "`{}` is a constructor of {n} type argument{plural}, so it is written with them,                  as `{}<…>`",
                dotted(path),
                dotted(path)
            )
        } else {
            format!(
                "`{}` is a constructor of {n} type argument{plural}, not {given}",
                dotted(path)
            )
        };
        self.error(codes::E0337, at, message);
        Ty::Error
    }

    /// A type that a body writes, a local's or a closure parameter's, at `spot`, which may be a
    /// view's (views.view-types).
    pub(super) fn type_ref(&mut self, ctx: &Ctx, t: ast::Type, spot: Spot) -> TypeRef {
        let at = self.at(bare(&t).syntax());
        let written = t.clone();
        let ty = self.ty_in(ctx, Some(t), spot);
        self.check_written_view(&ty, &written);
        TypeRef { ty, at }
    }

    /// effects.rows, and facts.implicit-effects. An element with an error is deleted by its fix
    /// with the separator before it, or the one after it if it is first, and with the whole row if
    /// it is alone.
    pub(super) fn row(&mut self, ctx: &Ctx, row: Option<ast::Row>) -> Row {
        let mut r = Row::default();
        let whole = row.as_ref().map(|row| self.whole_row(row));
        let elements: Vec<ast::RowElem> = row.into_iter().flat_map(|row| row.elements()).collect();
        let spans: Vec<TextRange> = elements.iter().map(|e| self.at(e.syntax())).collect();
        for (i, element) in elements.into_iter().enumerate() {
            let at = spans[i];
            let deleted = match (i.checked_sub(1).map(|j| spans[j]), spans.get(i + 1)) {
                (Some(before), _) => TextRange::new(before.end(), at.end()),
                (None, Some(after)) => TextRange::new(at.start(), after.start()),
                (None, None) => whole.unwrap_or(at),
            };
            match element {
                ast::RowElem::RowIo(_) => {
                    if r.io {
                        let d = Diagnostic::new(codes::E0500, at, "`io` is already in this row");
                        let fix = Fix::new("delete the repeated `io`", vec![Edit::delete(deleted)]);
                        self.diagnostics.push(d.with_fix(fix));
                    }
                    r.io = true;
                }
                ast::RowElem::RowRaise(raise) => {
                    let t = self.ty_in(ctx, raise.ty(), Spot::Error);
                    if let Some(first) = &r.raise {
                        let message = "a row holds at most one `raise` label";
                        let d = Diagnostic::new(codes::E0500, at, message);
                        // Only a repeated label is deleted: another error type is the user's
                        // to map (effects.repeated-elements).
                        let fix = (**first == t).then(|| {
                            Fix::new("delete the repeated `raise`", vec![Edit::delete(deleted)])
                        });
                        self.diagnostics
                            .push(fix.into_iter().fold(d, Diagnostic::with_fix));
                    } else {
                        r.raise = Some(Box::new(t));
                    }
                }
                ast::RowElem::RowVar(var) => {
                    if let Some(token) = var.ident() {
                        let n = self.ident(&token);
                        self.row_var(ctx, &mut r, &n, deleted);
                    }
                }
                ast::RowElem::RowEffect(e) => self.row_effect(ctx, &mut r, &e),
                ast::RowElem::RowAsync(a) => self.row_async(&mut r, &a),
            }
        }
        r
    }

    /// A projection's row, which holds no `raise<E>`, since a call that is a place can't sit in the
    /// operand of a `try` (projections.cannot-raise): one written is E0427, at the element, and
    /// then no part of the row (errors.error-type).
    pub(super) fn projection_row(&mut self, mut row: Row, written: Option<ast::Row>) -> Row {
        for element in written.into_iter().flat_map(|r| r.elements()) {
            if let ast::RowElem::RowRaise(raise) = element {
                let at = self.at(raise.syntax());
                let message = "a projection's call is a place, which can't sit in a `try`, so \
                               its row can't hold `raise`; panic instead, or have the caller \
                               check first";
                self.error(codes::E0427, at, message.to_owned());
            }
        }
        row.raise = None;
        row
    }

    /// The row variable `n` of the row `r`, which `deleted` deletes.
    fn row_var(&mut self, ctx: &Ctx, r: &mut Row, n: &Ident, deleted: TextRange) {
        let declared = ctx.row_vars.iter().rev().find(|(name, _)| *name == n.name);
        match (declared, &r.var) {
            (Some(_), Some(_)) => {
                let message = "a row holds at most one row variable".to_owned();
                self.error(codes::E0500, n.at, message);
            }
            (Some((_, v)), None) => r.var = Some(v.clone()),
            (None, _) if IMPLICIT_EFFECTS.contains(&&*n.name) => {
                let message = format!("`{}` is an implicit effect, which is never written", n.name);
                let d = Diagnostic::new(codes::E0501, n.at, message);
                let fix = Fix::new("delete it", vec![Edit::delete(deleted)]);
                self.diagnostics.push(d.with_fix(fix));
            }
            (None, _) => {
                let message = format!("unknown row variable `{}`", n.name);
                let known = ctx.row_vars.iter().map(|(name, _)| &**name);
                let d = Diagnostic::new(codes::E0211, n.at, message);
                let d = d.with_closest(AlternativeKind::Effect, n.at, &n.name, known.chain(["io"]));
                self.unknown_name(n.name.to_string(), d);
            }
        }
    }

    /// A row with the blanks before it, which go with it when it is deleted.
    pub(super) fn whole_row(&self, row: &ast::Row) -> TextRange {
        let at = self.at(row.syntax());
        match row.syntax().prev_sibling_or_token() {
            Some(rowan::NodeOrToken::Token(t)) if t.kind().is_trivia() => {
                self.at_token(&t).cover(at)
            }
            _ => at,
        }
    }

    /// Declares a generic in `scope`, at its place `id` in its list. Of two with the same name,
    /// the first stays declared, and a function's generics can't reuse the names of its impl
    /// block's (traits.impl-blocks).
    pub(super) fn declare(
        &mut self,
        scope: &mut Vec<(Name, GenericId)>,
        what: &str,
        n: &Ident,
        id: GenericId,
    ) {
        if scope.iter().any(|(name, _)| *name == n.name) {
            let message = format!("`{}` is already {what} here", n.name);
            self.error(codes::E0208, n.at, message);
        } else {
            scope.push((n.name, id));
        }
    }
}

/// The number of type arguments `Self` takes where `ctx` is: a constructor trait's arity in its
/// members, and 0 elsewhere (traits.constructor-traits).
fn self_arity(ctx: &Ctx) -> u32 {
    match ctx.self_kind {
        SelfKind::Trait(n) => n,
        SelfKind::Impl(_) | SelfKind::None => 0,
    }
}
