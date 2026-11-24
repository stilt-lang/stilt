//! Function types, and the polymorphic ones that declare type parameters
//! (polymorphism.function-types and polymorphism.placement): each parameter is in scope in its type
//! alone, hides no type parameter in scope (E0208), is bounded by traits given all their arguments
//! (E0300) and over types (E0337), and appears in its parameters' types or its result (E0339); and
//! the type stands only as the type of a parameter, of a record field or of a variant's payload
//! field (E0340).

use stilt_diag::{Diagnostic, Edit, Fix, codes};
use stilt_syntax::TextRange;
use stilt_syntax::ast::{self, AstNode};

use super::{Ctx, Resolver};
use crate::hir::{FnTy, GenericId, Ident, Owner, TraitRef, Ty};

/// Where a type is written, which decides whether it may be a polymorphic function type: only
/// [`Spot::Param`] allows one.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Spot {
    /// A parameter of a function type, a record field or a variant's payload field.
    Param,
    /// A function's own parameter, whose type may also be an open record type
    /// (records.open-parameter-types).
    OwnParam,
    TypeArg,
    Result,
    Local,
    /// A closure parameter's annotation.
    Closure,
    Constant,
    Tuple,
    Error,
    /// Anywhere else, such as a bound's argument or a receiver's type.
    Other,
}

impl Spot {
    fn phrase(self) -> &'static str {
        match self {
            Self::Param | Self::OwnParam => "be a parameter's type",
            Self::TypeArg => "be a type argument",
            Self::Result => "be a result",
            Self::Local => "be a local's type",
            Self::Closure => "be a closure parameter's type",
            Self::Constant => "be a constant's type",
            Self::Tuple => "be a tuple's element",
            Self::Error => "be an error type",
            Self::Other => "stand here",
        }
    }
}

impl Resolver<'_> {
    /// Starts the types of the declaration `owner`, which owns the type parameters of the
    /// polymorphic function types they write.
    pub(super) fn own_polys(&mut self, owner: &Owner) {
        self.poly_owner = Some(owner.clone());
        self.next_poly = 0;
    }

    /// A new type parameter of a polymorphic function type, named `n`, unique in its
    /// declaration.
    fn poly_param(&mut self, n: &Ident) -> GenericId {
        let owner = self.poly_owner.clone().unwrap_or(Owner {
            decl: crate::hir::DeclId {
                module: self.module.name,
                index: u32::MAX,
            },
            member: None,
        });
        let id = GenericId {
            owner,
            index: GenericId::POLY + self.next_poly % GenericId::POLY_SPAN,
        };
        self.next_poly += 1;
        self.poly_names.push((id.clone(), n.name));
        id
    }

    /// A function type written at `spot`.
    pub(super) fn fn_type(&mut self, ctx: &Ctx, f: &ast::FnType, spot: Spot) -> Ty {
        let Some(list) = f.generic_list() else {
            let fty = self.fn_parts(ctx, f, Vec::new());
            return if lost_spread(f, &fty) {
                Ty::Error
            } else {
                Ty::Fn(Box::new(fty))
            };
        };
        let (inner, declared) = self.poly_generics(ctx, &list);
        let generics: Vec<(GenericId, Vec<TraitRef>)> = declared
            .iter()
            .map(|(id, _, p)| {
                let bounds = p.bounds().map(|b| self.poly_bound(&inner, &b)).collect();
                (id.clone(), bounds)
            })
            .collect();
        let mut fty = self.fn_parts(&inner, f, generics);
        let spans: Vec<TextRange> = declared.iter().map(|(.., p)| self.at(p.syntax())).collect();
        let whole = self.at(list.syntax());
        let mut index = 0;
        let mut unused = false;
        fty.generics.retain(|(id, _)| {
            let used = fty.params.iter().any(|(_, t)| mentions(t, id))
                || fty.ret.as_ref().is_some_and(|t| mentions(t, id));
            if !used && let Some((_, n, _)) = declared.get(index) {
                let message = format!(
                    "`{}` appears in neither the parameters nor the result, so no call can tell \
                     what it is",
                    n.name
                );
                let d = Diagnostic::new(codes::E0339, n.at, message);
                let fix = Fix::new(
                    format!("delete `{}`", n.name),
                    vec![Edit::delete(deleted(&spans, index, whole))],
                );
                self.diagnostics.push(d.with_fix(fix));
            }
            index += 1;
            unused |= !used;
            used
        });
        if !matches!(spot, Spot::Param | Spot::OwnParam) {
            let message = format!(
                "a polymorphic function type can't {}; only a parameter, a field or a payload \
                 can have one",
                spot.phrase()
            );
            self.error(codes::E0340, self.at(f.syntax()), message);
            return Ty::Error;
        }
        // A part of a signature with an error is the error type (errors.error-type).
        if unused || lost_spread(f, &fty) {
            return Ty::Error;
        }
        Ty::Fn(Box::new(fty))
    }

    /// The type parameters a polymorphic function type declares, and the context of its
    /// parameters and result, where they are in scope.
    fn poly_generics(
        &mut self,
        ctx: &Ctx,
        list: &ast::GenericList,
    ) -> (Ctx, Vec<(GenericId, Ident, ast::TypeParam)>) {
        let mut inner = ctx.clone();
        let mut declared = Vec::new();
        for g in list.generics() {
            let ast::Generic::TypeParam(p) = g else {
                continue;
            };
            let n = self.name(p.name(), p.syntax());
            let id = self.poly_param(&n);
            // Once reported, it stands for its element wherever it is written, so that its uses
            // report nothing more (errors.root-causes).
            if p.is_pack() {
                let message = "a polymorphic function type's parameters are never packs";
                self.error(codes::E0344, self.at(p.syntax()), message.to_owned());
                inner.packs.push(id.clone());
                self.misplaced.push(id.clone());
            }
            // It hides no type parameter in scope, and stands for itself in its type all the
            // same, so that its uses report nothing more (errors.root-causes).
            if ctx.type_params.iter().any(|(name, _)| *name == n.name) {
                let message = format!("`{}` is already a type parameter here", n.name);
                self.error(codes::E0208, n.at, message);
                inner.type_params.push((n.name, id.clone()));
            } else {
                self.declare(&mut inner.type_params, "a type parameter", &n, id.clone());
            }
            declared.push((id, n, p));
        }
        (inner, declared)
    }

    /// The parameters, result and row of a function type, with its type parameters `generics`
    /// in scope in `ctx`. Its parameters may be polymorphic function types, and its result
    /// and error type may not (polymorphism.placement).
    fn fn_parts(
        &mut self,
        ctx: &Ctx,
        f: &ast::FnType,
        generics: Vec<(GenericId, Vec<TraitRef>)>,
    ) -> FnTy {
        let params = f
            .params()
            .map(|p| (p.mode(), self.ty_in(ctx, p.ty(), Spot::Param)))
            .collect();
        let ret = f.ret_type().map(|r| self.ty_in(ctx, r.ty(), Spot::Result));
        let row = self.row(ctx, f.row());
        FnTy {
            generics,
            params,
            ret,
            row,
        }
    }

    /// A bound of a polymorphic function type's parameter: a trait over types, given all its
    /// arguments, since such a type declares no member types (polymorphism.function-types). A wrong
    /// one is the error bound, which every type meets.
    fn poly_bound(&mut self, ctx: &Ctx, b: &ast::Bound) -> TraitRef {
        let path = self.path(b.path());
        let args: Vec<Ty> = b.args().map(|a| self.ty(ctx, Some(a))).collect();
        let TraitRef::Trait(item, _) = self.trait_ref(ctx, &path) else {
            return TraitRef::Error;
        };
        let shape = self.shape_of(&item);
        let at = self.at(b.syntax());
        if shape.arity > 0 {
            let message = format!(
                "`{}` is a constructor trait, which bounds no type parameter of a function type",
                item.name
            );
            self.error(codes::E0337, at, message);
            return TraitRef::Error;
        }
        if args.len() != shape.params.len() {
            if b.has_args() {
                self.wrong_trait_args(at, &item, &shape, args.len());
            } else {
                let n = shape.params.len();
                let message = format!(
                    "`{}` takes {n} type argument{} here, since a function type declares no \
                     member types",
                    item.name,
                    if n == 1 { "" } else { "s" }
                );
                self.error(codes::E0300, at, message);
            }
            return TraitRef::Error;
        }
        TraitRef::Trait(item, args)
    }
}

/// What deleting the type parameter `index` of a list deletes, its spans `spans` and its own
/// `whole`: the parameter with the separator before it, or after it if it is first, and the
/// whole list if it is alone.
fn deleted(spans: &[TextRange], index: usize, whole: TextRange) -> TextRange {
    let at = spans[index];
    match (index.checked_sub(1).map(|j| spans[j]), spans.get(index + 1)) {
        (Some(before), _) => TextRange::new(before.end(), at.end()),
        (None, Some(after)) => TextRange::new(at.start(), after.start()),
        (None, None) => whole,
    }
}

/// Whether a type names the type parameter `id`.
fn mentions(t: &Ty, id: &GenericId) -> bool {
    match t {
        Ty::Param(p) => p == id,
        Ty::Con(_, ts) | Ty::Tuple(ts) => ts.iter().any(|t| mentions(t, id)),
        Ty::App(head, ts) => mentions(head, id) || ts.iter().any(|t| mentions(t, id)),
        Ty::Fn(f) => {
            f.params.iter().any(|(_, t)| mentions(t, id))
                || f.ret.as_ref().is_some_and(|t| mentions(t, id))
                || f.row.raise.as_deref().is_some_and(|t| mentions(t, id))
        }
        Ty::Spread(p, t) => p == id || mentions(t, id),
        Ty::Handler(h) => {
            h.effect.args.iter().any(|t| mentions(t, id))
                || h.answer.as_ref().is_some_and(|t| mentions(t, id))
        }
        Ty::SelfTy | Ty::Value(_) | Ty::Error => false,
    }
}

/// Whether a parameter of a function type spreads a type with an error, which leaves its number
/// of parameters unknown, so the function type is the error type, as such a tuple's is
/// (errors.error-type; variadics.type-spreads).
fn lost_spread(f: &ast::FnType, fty: &FnTy) -> bool {
    f.params()
        .zip(&fty.params)
        .any(|(p, (_, t))| matches!(p.ty(), Some(ast::Type::SpreadType(_))) && *t == Ty::Error)
}
