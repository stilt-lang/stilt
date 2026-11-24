//! Type declarations (declarations.records and declarations.type-parameters): a record or a variant
//! type, with its type parameters, its pack (variadics.packs) and its value parameters
//! (generics.value-parameters).

use stilt_diag::codes;
use stilt_syntax::ast::{self, AstNode};

use super::poly::Spot;
use super::{Ctx, Resolver, views};
use crate::hir::{GenericId, Owner, TypeDecl, TypeDef};

impl Resolver<'_> {
    /// A type declaration: its parameters, type and value (generics.value-parameters), and its
    /// definition.
    pub(super) fn type_decl(
        &mut self,
        ctx: &Ctx,
        t: &ast::TypeDecl,
        public: bool,
        owner: &Owner,
    ) -> TypeDecl {
        let name = self.name(t.name(), t.syntax());
        let mut ctx = Ctx {
            public,
            ..ctx.clone()
        };
        let mut params = Vec::new();
        let mut values = Vec::new();
        let written: Vec<ast::Generic> = t.params().collect();
        let placed = self.check_packs(&written, false);
        for (index, p) in (0..).zip(&written) {
            let id = GenericId {
                owner: owner.clone(),
                index,
            };
            // A type's value parameter (generics.value-parameters), which its fields may name.
            if let ast::Generic::ValueParam(v) = p {
                let (n, t) = self.value_param(&mut ctx, v, id);
                values.push((index, t));
                params.push(n.name);
                continue;
            }
            let n = self.name(p.name(), p.syntax());
            if p.is_pack() && placed {
                ctx.packs.push(id.clone());
            } else if p.is_pack() {
                self.misplaced.push(id.clone());
            }
            self.declare(&mut ctx.type_params, "a type parameter", &n, id);
            params.push(n.name);
        }
        let def = self.type_def(&ctx, t);
        TypeDecl {
            name: name.name,
            params,
            pack: written.last().is_some_and(ast::Generic::is_pack),
            values,
            def,
        }
    }

    /// What a type declaration defines: its fields, its variants, or a native type.
    fn type_def(&mut self, ctx: &Ctx, t: &ast::TypeDecl) -> TypeDef {
        match t.def() {
            Some(ast::TypeDef::RecordDef(record)) => self.record_def(ctx, &record),
            Some(ast::TypeDef::VariantList(list)) => self.variants_def(ctx, &list),
            None => match t.native() {
                // views.std-view: only the standard library declares native types. Anywhere
                // else `= ?` is the alias form, a syntax error (declarations.no-aliases).
                Some(q) if !self.module.std => {
                    self.error(codes::E0100, self.at_token(&q), "unexpected `?`".to_owned());
                    TypeDef::Variants(Vec::new())
                }
                Some(_) => TypeDef::Native,
                // A type that a part with a syntax error declares has no values
                // (program.errors-outside-bodies).
                None => TypeDef::Variants(Vec::new()),
            },
        }
    }

    fn record_def(&mut self, ctx: &Ctx, record: &ast::RecordDef) -> TypeDef {
        let fields: Vec<_> = record.fields().collect();
        let names: Vec<_> = fields
            .iter()
            .map(|f| self.name(f.name(), f.syntax()))
            .collect();
        for n in &names {
            self.check_not_primitive(n);
        }
        self.check_unique("a field", &names);
        TypeDef::Record(
            names
                .into_iter()
                .zip(&fields)
                .map(|(n, f)| {
                    let t = self.ty_in(ctx, f.ty(), Spot::Param);
                    (n.name, self.checked_view(t, f.ty().as_ref(), views::Field))
                })
                .collect(),
        )
    }

    fn variants_def(&mut self, ctx: &Ctx, list: &ast::VariantList) -> TypeDef {
        TypeDef::Variants(
            list.variants()
                .map(|v| {
                    let payloads: Vec<_> = v.payloads().collect();
                    for p in &payloads {
                        if let Some(name) = p.name() {
                            let n = self.name(Some(name), p.syntax());
                            self.check_not_primitive(&n);
                        }
                    }
                    let payload = payloads
                        .iter()
                        .map(|p| {
                            let t = self.ty_in(ctx, p.ty(), Spot::Param);
                            self.checked_view(t, p.ty().as_ref(), views::Payload)
                        })
                        .collect();
                    (self.name(v.name(), v.syntax()).name, payload)
                })
                .collect(),
        )
    }
}
