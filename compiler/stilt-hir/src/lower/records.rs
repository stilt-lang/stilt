//! Anonymous and open record types and record bounds (records.anonymous-types,
//! records.record-bounds and records.open-parameter-types), and spreads of packs in types
//! (variadics.packs and variadics.type-spreads).
//!
//! An anonymous record type names each field once (E0316) and is the constructor of its fields'
//! names applied to their types, in alphabetical order. An open record type is a function's own
//! parameter's type, which stands for a type parameter of the function with that record bound,
//! hidden and unnamed; anywhere else it is E0341, whose fix names a type parameter with the
//! bound where the function's generics can take one. A record bound ends with `..` (E0341). A
//! pack is written only spread, and each spread names exactly one pack and holds no other
//! spread (E0343).

use stilt_diag::{Diagnostic, Edit, Fix, codes};
use stilt_syntax::ast::{self, AstNode};
use stilt_syntax::{SyntaxKind, TextRange, TextSize};

use super::poly::Spot;
use super::{Ctx, Resolver};
use crate::hir::{Generic, GenericId, GenericKind, Item, Name, Owner, TraitRef, Ty, sorted_fields};

/// The type parameters that the open record types of a function's parameters stand for, while
/// its signature is resolved.
pub(super) struct Hidden {
    owner: Owner,
    next: u32,
    pub(super) made: Vec<Generic>,
    /// Where a type parameter is added to the function's generics: the end of its name, or the
    /// end of its generics before their `>`, and whether it has any.
    insert: (TextSize, bool),
}

impl Hidden {
    /// The function `f`'s, whose generics so far are `declared`, owned by `owner`.
    pub(super) fn of(f: &ast::Fn, owner: &Owner, declared: usize, at: TextSize) -> Self {
        let end = f.generic_list().and_then(|l| {
            l.syntax()
                .children_with_tokens()
                .filter_map(rowan::NodeOrToken::into_token)
                .find(|t| t.kind() == SyntaxKind::R_ANGLE)
                .map(|t| t.text_range().start())
        });
        Self {
            owner: owner.clone(),
            next: u32::try_from(declared).unwrap_or(u32::MAX),
            made: Vec::new(),
            insert: end.map_or((at, false), |e| (e, true)),
        }
    }
}

impl Resolver<'_> {
    /// The fields of a record type, sorted, each named once (E0316); `None` when one is named
    /// twice.
    fn record_fields(&mut self, ctx: &Ctx, r: &ast::RecordType) -> Option<Vec<(Name, Ty)>> {
        let mut fields: Vec<(Name, Ty)> = Vec::new();
        let mut twice = false;
        for f in r.fields() {
            let n = self.name(f.name(), f.syntax());
            let t = self.ty_in(ctx, f.ty(), Spot::Param);
            if fields.iter().any(|(m, _)| *m == n.name) {
                let message = format!("the field `{}` is named twice", n.name);
                self.error(codes::E0316, n.at, message);
                twice = true;
            }
            fields.push((n.name, t));
        }
        // A record type has a field (records.anonymous-types), so one without any is what a syntax
        // error left, which has the error type.
        (!twice && !fields.is_empty()).then(|| sorted_fields(fields))
    }

    /// An anonymous record type, or an open one written at `spot` (records.anonymous-types and
    /// records.open-parameter-types).
    pub(super) fn record_type(&mut self, ctx: &Ctx, r: &ast::RecordType, spot: Spot) -> Ty {
        let Some(fields) = self.record_fields(ctx, r) else {
            return Ty::Error;
        };
        let (names, types): (Vec<Name>, Vec<Ty>) = fields.into_iter().unzip();
        if !r.is_open() {
            return Ty::Con(Item::record(&names), types);
        }
        let bound = TraitRef::Trait(Item::record_bound(&names), types);
        if spot == Spot::OwnParam
            && let Some(hidden) = &mut self.hidden
        {
            let id = GenericId {
                owner: hidden.owner.clone(),
                index: hidden.next,
            };
            hidden.next += 1;
            hidden.made.push(Generic {
                name: Name::from(written(r.syntax())),
                kind: GenericKind::Type(vec![bound]),
                member: false,
                pack: false,
            });
            return Ty::Param(id);
        }
        self.open_out_of_place(ctx, r, spot);
        Ty::Error
    }

    /// E0341: an open record type that isn't a function's parameter's type, whose fix, in a
    /// function's result, names a type parameter with the bound.
    fn open_out_of_place(&mut self, ctx: &Ctx, r: &ast::RecordType, spot: Spot) {
        let at = self.at(r.syntax());
        let message = "an open record type stands for a type the caller gives, so only a \
                       parameter can have one; name a type parameter with the bound";
        let mut d = Diagnostic::new(codes::E0341, at, message);
        if let Some(hidden) = &self.hidden
            && spot == Spot::Result
        {
            let fresh = super::bounds::fresh_name(ctx);
            let generic = format!("{fresh}: {}", written(r.syntax()));
            let (insert, has_list) = hidden.insert;
            let added = if has_list {
                format!(", {generic}")
            } else {
                format!("<{generic}>")
            };
            let title = format!("name a type parameter `{fresh}` with the bound");
            let edits = vec![
                Edit::insert(insert + self.base, added),
                Edit::replace(at, fresh),
            ];
            d = d.with_fix(Fix::new(title, edits));
        }
        self.diagnostics.push(d);
    }

    /// A record bound, `{ f: T, .. }`, which is a bound on the item of its fields' names with their
    /// types as its arguments; one without `..` is E0341, whose fix adds it
    /// (records.record-bounds).
    pub(super) fn record_bound(&mut self, ctx: &Ctx, r: &ast::RecordType) -> TraitRef {
        if !r.is_open() {
            let at = self.at(r.syntax());
            let message = "a record bound ends with `..`, since one that named every field \
                           would be a type";
            let mut d = Diagnostic::new(codes::E0341, at, message);
            if let Some(last) = r.fields().last() {
                let after = last
                    .syntax()
                    .next_sibling_or_token()
                    .filter(|t| t.kind() == SyntaxKind::COMMA);
                let edit = match after {
                    Some(comma) => Edit::insert(self.in_file(comma.text_range()).end(), " .."),
                    None => Edit::insert(self.at(last.syntax()).end(), ", .."),
                };
                d = d.with_fix(Fix::new("add `..`", vec![edit]));
            }
            self.diagnostics.push(d);
        }
        let Some(fields) = self.record_fields(ctx, r) else {
            return TraitRef::Error;
        };
        let (names, types): (Vec<Name>, Vec<Ty>) = fields.into_iter().unzip();
        TraitRef::Trait(Item::record_bound(&names), types)
    }

    /// A spread `..T`, which names exactly one pack and holds no other spread
    /// (variadics.type-spreads).
    pub(super) fn spread_type(&mut self, ctx: &Ctx, s: &ast::SpreadType) -> Ty {
        let at = self.at(s.syntax());
        if self.spread.is_some() {
            let message = "a spread can't stand inside another spread";
            self.error(codes::E0343, at, message.to_owned());
            return Ty::Error;
        }
        self.spread = Some(Vec::new());
        let inner = self.ty_in(ctx, s.ty(), Spot::Tuple);
        let mut packs = self.spread.take().unwrap_or_default();
        packs.sort();
        packs.dedup();
        // A spread of a misplaced pack is its body, since the pack is a plain type parameter
        // after E0344 (variadics.packs).
        if packs.iter().any(|p| self.misplaced.contains(p)) {
            return inner;
        }
        match packs.as_slice() {
            [pack] if inner != Ty::Error => Ty::Spread(pack.clone(), Box::new(inner)),
            // An error inside the spread is reported where it is (errors.root-causes).
            _ if holds_error(&inner) => Ty::Error,
            [] => {
                let message = "a spread names a pack, as `..Ts` or `..List<Ts>`, which gives it \
                               its elements";
                self.error(codes::E0343, at, message.to_owned());
                Ty::Error
            }
            [..] => {
                let message = "a spread names exactly one pack, so that its length is the \
                               pack's; this one names several";
                self.error(codes::E0343, at, message.to_owned());
                Ty::Error
            }
        }
    }

    /// The type a pack `v` named `name` is, where a type names it: itself inside a spread, and
    /// E0343 anywhere else (variadics.type-spreads).
    pub(super) fn pack_use(&mut self, v: GenericId, name: &str, at: TextRange) -> Ty {
        if let Some(named) = &mut self.spread {
            named.push(v.clone());
            return Ty::Param(v);
        }
        if self.misplaced.contains(&v) {
            return Ty::Param(v);
        }
        let message = format!("`{name}` is a pack, which is written only spread, as `(..{name})`");
        self.error(codes::E0343, at, message);
        Ty::Error
    }

    /// Checks a type's or a trait's parameters for packs: a type declares at most one, as its
    /// last parameter, and a trait none (variadics.packs; E0344). Each declaration reports its
    /// first such pack. Gives whether its packs are well placed: if not, each is a plain type
    /// parameter after E0344, so that nothing more is reported of it.
    pub(super) fn check_packs(&mut self, params: &[ast::Generic], trait_params: bool) -> bool {
        let packs: Vec<(usize, &ast::Generic)> = params
            .iter()
            .enumerate()
            .filter(|(_, p)| p.is_pack())
            .collect();
        let found = match packs.as_slice() {
            [(_, p), ..] if trait_params => Some((*p, "a trait's parameters are never packs")),
            [_, (_, p), ..] => Some((
                *p,
                "a type declares at most one pack, so that its arguments say where it starts",
            )),
            [(i, p)] if *i + 1 != params.len() => Some((
                *p,
                "a type's pack is its last parameter, so that its arguments after the others \
                 are the pack's",
            )),
            [] | [_] => None,
        };
        let Some((p, message)) = found else {
            return true;
        };
        let at = self.at(p.syntax());
        self.error(codes::E0344, at, message.to_owned());
        false
    }
}

/// Whether a type holds the error type.
fn holds_error(t: &Ty) -> bool {
    match t {
        Ty::Error => true,
        Ty::Con(_, ts) | Ty::Tuple(ts) | Ty::App(_, ts) => ts.iter().any(holds_error),
        Ty::Spread(_, t) => holds_error(t),
        Ty::Fn(f) => {
            f.params.iter().any(|(_, t)| holds_error(t)) || f.ret.as_ref().is_some_and(holds_error)
        }
        Ty::Handler(h) => {
            h.effect.args.iter().any(holds_error) || h.answer.as_ref().is_some_and(holds_error)
        }
        Ty::Param(_) | Ty::SelfTy | Ty::Value(_) => false,
    }
}

/// A record type as written, its blanks each one space.
fn written(node: &stilt_syntax::SyntaxNode) -> String {
    node.text()
        .to_string()
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ")
}
