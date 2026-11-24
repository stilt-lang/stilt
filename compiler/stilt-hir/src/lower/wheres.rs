//! `where` clauses (traits.where): bounds on member types, which have no place beside a
//! parameter to be written in.

use stilt_diag::{Diagnostic, Edit, Fix, codes};
use stilt_syntax::TextRange;
use stilt_syntax::ast::{self, AstNode};

use super::Ctx;
use super::Resolver;
use super::bounds::Declared;
use crate::hir::{GenericKind, Name, TraitRef, Ty};

impl Resolver<'_> {
    /// Adds the bounds of a `where` clause to the member types it names, which `declared`
    /// declares. A bound on anything but a member type is E0336, and so is a clause on a
    /// function of a trait or a trait impl, whose signature is the trait's.
    pub(super) fn where_clause(
        &mut self,
        ctx: &mut Ctx,
        clause: Option<ast::WhereClause>,
        declared: &mut Declared<'_>,
        list: Option<&ast::GenericList>,
    ) {
        let Some(clause) = clause else { return };
        if ctx.trait_member {
            let at = clause
                .where_token()
                .map_or_else(|| self.at(clause.syntax()), |t| self.at_token(&t));
            let message = "a function of a trait or a trait impl has the trait's signature, so \
                           it can't bound what the trait leaves open; bound it in the trait's \
                           callers instead";
            let fix = Fix::new(
                "delete the `where` clause",
                vec![Edit::delete(self.spaced(clause.syntax()))],
            );
            self.diagnostics
                .push(Diagnostic::new(codes::E0336, at, message).with_fix(fix));
            return;
        }
        let all: Vec<ast::WhereBound> = clause.bounds().collect();
        for (i, wb) in all.iter().enumerate() {
            let path = self.path(wb.path());
            let at = wb
                .path()
                .map_or_else(|| self.at(wb.syntax()), |p| self.at(p.syntax()));
            let bounds: Vec<ast::Bound> = wb.bounds().collect();
            let ty = match path.as_slice() {
                [_, _] if ctx.type_params.iter().any(|(n, _)| *n == path[0].name) => {
                    self.member_type(ctx, &path, at)
                }
                // A longer path is a type of a module, resolved as a type is, whose bounds a
                // fixed type must meet.
                [_, _, ..] => self.record_ty(ctx, &path).ty,
                // A name that names no type is E0211, which resolving it reports, and nothing
                // more (errors.unknown-names, "Unknown names").
                [_] if matches!(self.record_ty(ctx, &path).ty, Ty::Error) => {
                    for b in &bounds {
                        self.loose_bound(ctx, b);
                    }
                    continue;
                }
                _ => {
                    let removed = if all.len() == 1 {
                        self.spaced(clause.syntax())
                    } else {
                        self.listed(&all, i)
                    };
                    let own = self.not_a_member_type(wb, &bounds, (at, removed), list);
                    // The bound still bounds its parameter, so its uses report nothing more.
                    if let Some(index) = own {
                        self.bound_generic(ctx, declared, index, &bounds);
                    } else {
                        for b in &bounds {
                            self.loose_bound(ctx, b);
                        }
                    }
                    continue;
                }
            };
            let name = Name::from(format!("{}.{}", path[0].name, path[1].name));
            self.bound_member(ctx, declared, (ty, &name, at), &bounds);
        }
    }

    /// Bounds the member type `ty`, named `name` at `at`: one of the declaration's own generics, one
    /// of its impl block's, which the function assumes, or a type that a bound's argument fixes,
    /// which must meet the bounds (traits.where).
    fn bound_member(
        &mut self,
        ctx: &mut Ctx,
        declared: &mut Declared<'_>,
        (ty, name, at): (Ty, &Name, TextRange),
        bounds: &[ast::Bound],
    ) {
        match &ty {
            Ty::Param(id) => {
                if let Some(index) = declared.index_of(id) {
                    self.bound_generic(ctx, declared, index, bounds);
                } else {
                    let refs = self.bounds(ctx, declared, (id, name), bounds);
                    ctx.assumed.push((id.clone(), refs));
                }
            }
            // A member type with an error bounds nothing, but its bounds are still resolved, so
            // a name there that names nothing is reported (errors.root-causes).
            Ty::Error => {
                for b in bounds {
                    self.loose_bound(ctx, b);
                }
            }
            fixed => {
                for b in bounds {
                    if let TraitRef::Trait(item, args) = self.loose_bound(ctx, b) {
                        ctx.fixed.push((fixed.clone(), item, args, at));
                    }
                }
            }
        }
    }

    /// Adds `bounds` to the declaration's own generic at `index`.
    fn bound_generic(
        &mut self,
        ctx: &mut Ctx,
        declared: &mut Declared<'_>,
        index: usize,
        bounds: &[ast::Bound],
    ) {
        let id = declared.id(index);
        let name = declared.generics[index].name;
        let refs = self.bounds(ctx, declared, (&id, &name), bounds);
        if let GenericKind::Type(existing) = &mut declared.generics[index].kind {
            existing.extend(refs);
        }
    }

    /// E0336 for a `where` bound on a type that isn't a member type, whose fix moves the bound
    /// beside the type parameter it names, deleting `removed`.
    fn not_a_member_type(
        &mut self,
        wb: &ast::WhereBound,
        bounds: &[ast::Bound],
        (at, removed): (TextRange, TextRange),
        list: Option<&ast::GenericList>,
    ) -> Option<usize> {
        let path = self.path(wb.path());
        let written: Vec<String> = bounds
            .iter()
            .map(|b| b.syntax().text().to_string())
            .collect();
        let param = match path.as_slice() {
            [one] => list.and_then(|l| {
                l.generics().enumerate().find_map(|(i, g)| match g {
                    ast::Generic::TypeParam(p)
                        if p.name().is_some_and(|n| n.text() == *one.name) =>
                    {
                        Some((i, p))
                    }
                    _ => None,
                })
            }),
            _ => None,
        };
        let Some((index, p)) = param else {
            let message = "a `where` clause bounds member types, as `C.Item`; this type has \
                           no bounds of its own";
            self.error(codes::E0336, at, message.to_owned());
            return None;
        };
        let name = path[0].name;
        let (insert_at, text) = match p.bounds().last() {
            Some(final_bound) => (
                self.at(final_bound.syntax()).end(),
                format!(" + {}", written.join(" + ")),
            ),
            None => (
                self.at(p.syntax()).end(),
                format!(": {}", written.join(" + ")),
            ),
        };
        let message = format!(
            "`{name}` is a type parameter, so its bounds go beside it, not in a `where` clause, \
             which bounds member types"
        );
        let fix = Fix::new(
            format!("move the bound beside `{name}`"),
            vec![Edit::insert(insert_at, text), Edit::delete(removed)],
        );
        self.diagnostics
            .push(Diagnostic::new(codes::E0336, at, message).with_fix(fix));
        Some(index)
    }

    /// A node with the blanks before it, which go with it when it is deleted.
    fn spaced(&self, node: &stilt_syntax::SyntaxNode) -> TextRange {
        let at = self.at(node);
        match node.prev_sibling_or_token() {
            Some(rowan::NodeOrToken::Token(t)) if t.kind().is_trivia() => {
                self.at_token(&t).cover(at)
            }
            _ => at,
        }
    }

    /// The `i`th of a clause's bounds with the comma that separates it from the next, or from
    /// the one before for the last.
    fn listed(&self, all: &[ast::WhereBound], i: usize) -> TextRange {
        let at = self.at(all[i].syntax());
        match (all.get(i + 1), i.checked_sub(1).map(|j| &all[j])) {
            (Some(next), _) => TextRange::new(at.start(), self.at(next.syntax()).start()),
            (None, Some(before)) => TextRange::new(self.at(before.syntax()).end(), at.end()),
            (None, None) => at,
        }
    }
}
