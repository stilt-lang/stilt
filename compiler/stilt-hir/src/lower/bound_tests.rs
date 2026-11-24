//! Bound tests, `if T: B + …` (meta.bound-tests): the type parameter tested, which must be one in
//! scope, and its bounds, each written as a generic writes it (traits.bounds;
//! traits.bound-arguments).

use stilt_syntax::ast::{self, AstNode};

use super::{Ctx, Meaning, Resolver};
use crate::hir::{BoundTest, TraitRef, Ty};
use crate::scope::Namespace;

impl Resolver<'_> {
    /// A bound test. A name that is no type parameter in scope is E0212, and one that names
    /// nothing E0211, as a path that names nothing is.
    pub(super) fn bound_test(&mut self, ctx: &Ctx, test: &ast::BoundTest) -> BoundTest {
        let name = self.name(test.name(), test.syntax());
        let param = match self.lookup(ctx, Namespace::Types, false, &name) {
            Some(Meaning::Param(g)) => Some(g),
            Some(Meaning::Broken) => None,
            _ => {
                // Resolving the name as a path reports what it names instead, or that it names
                // nothing.
                let path = [name.clone()];
                let (meaning, _) =
                    self.walk(ctx, Namespace::Types, "a type parameter", false, &path);
                if !matches!(meaning, Meaning::Broken) {
                    self.wrong_kind(&name, &meaning, "a type parameter");
                }
                None
            }
        };
        let bounds = test
            .bounds()
            .map(|b| (self.tested_bound(ctx, &b), self.at(b.syntax())))
            .collect();
        BoundTest {
            param,
            name,
            bounds,
        }
    }

    /// One bound of a bound test: a trait with the arguments written, or a record bound
    /// (records.record-bounds). A trait with parameters written without arguments keeps none, since
    /// no declaration gives them member types.
    fn tested_bound(&mut self, ctx: &Ctx, b: &ast::Bound) -> TraitRef {
        if let Some(r) = b.record() {
            return self.record_bound(ctx, &r);
        }
        let path = self.path(b.path());
        let TraitRef::Trait(item, _) = self.trait_ref(ctx, &path) else {
            for a in b.args() {
                self.ty(ctx, Some(a));
            }
            return TraitRef::Error;
        };
        if !b.has_args() {
            return TraitRef::Trait(item, Vec::new());
        }
        let shape = self.shape_of(&item);
        let given: Vec<ast::Type> = b.args().collect();
        if given.len() != shape.params.len() {
            self.wrong_trait_args(self.at(b.syntax()), &item, &shape, given.len());
        }
        let mut args: Vec<Ty> = given.into_iter().map(|a| self.ty(ctx, Some(a))).collect();
        if args.len() != shape.params.len() {
            args = vec![Ty::Error; shape.params.len()];
        }
        TraitRef::Trait(item, args)
    }
}
