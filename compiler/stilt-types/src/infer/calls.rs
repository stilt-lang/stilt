//! Calls: of functions, variants, members, methods and function values.

use stilt_diag::{Diagnostic, Edit, Fix, codes};
use stilt_hir::decls::{MemberInfo, MemberKindInfo, TraitMethod};
use stilt_hir::hir::{self, Arg, ExprKind, Ident, Item, Mode};
use stilt_syntax::TextRange;

use super::fields::{checked_place, may_be_place, not_a_place};
use super::members::{Ambiguous, Found};
use super::types::{Instance, Sig};
use super::{Cx, State, error_node, node};
use crate::tast::{self, Callee};
use crate::ty::Ty;
use crate::ty::is_prelude;

pub(super) fn arg_mode(a: &Arg) -> Mode {
    if a.inout { Mode::Inout } else { Mode::Let }
}

/// A call by name: a place when the callee is a projection (projections.call-is-place).
fn call_node(callee: Callee, inst: Instance, args: Vec<tast::Arg>, at: TextRange) -> tast::Expr {
    let kind = if inst.projection {
        tast::ExprKind::Project(callee, inst.targs, args, inst.row)
    } else {
        tast::ExprKind::Call(callee, inst.targs, args, inst.row)
    };
    node(kind, inst.ret, at)
}

impl State<'_> {
    /// A call of the prelude's `print` or `eprint` with several arguments, as Python's and
    /// JavaScript's print takes them: E0315 says that one string holds the values.
    fn printing_several(&mut self, item: &Item, first: usize, args: &[Arg]) {
        if !(is_prelude(item, "print") || is_prelude(item, "eprint")) {
            return;
        }
        let fix = self.one_string(args);
        for d in &mut self.errors[first..] {
            if d.code == codes::E0315 {
                let name = &item.name;
                let message = format!(
                    "`{name}` takes one string, which holds the values, as `{name}(\"a is {{a}}\")`"
                );
                let help = "A string inserts the value of each `{…}` in it, so one string says \
                            it all.";
                let mut found = Diagnostic::new(d.code, d.range, message).with_help(help);
                if let Some(fix) = fix.clone() {
                    found = found.with_fix(fix);
                }
                *d = found;
            }
        }
    }

    /// The fix that writes the arguments of a `print` as one string, a space between two as
    /// Python's `print` puts it: each a string literal, written as it is, or a local, inserted
    /// as `{name}` (lexical.interpolation).
    fn one_string(&self, args: &[Arg]) -> Option<Fix> {
        let (first, last) = (args.first()?, args.last()?);
        let mut pieces = Vec::new();
        for a in args {
            match &a.value.kind {
                ExprKind::Str(s) if !s.contains(['{', '}', '"', '\\', '\n']) => {
                    pieces.push(s.clone());
                }
                ExprKind::Local(id) if !a.inout => {
                    let name = self.local_names.get(usize::try_from(id.0).ok()?)?;
                    pieces.push(format!("{{{name}}}"));
                }
                _ => return None,
            }
        }
        let range = TextRange::new(first.at.start(), last.at.end());
        let text = format!("\"{}\"", pieces.join(" "));
        Some(Fix::new(
            "write one string",
            vec![Edit::replace(range, text)],
        ))
    }

    /// Whether a call's arguments or its parameters spread packs (variadics.spread-expressions).
    fn spreads_in(&self, params: &[(Mode, Ty)], args: &[Arg]) -> bool {
        args.iter().any(|a| super::exprs::is_spread(&a.value))
            || params.iter().any(|(_, t)| {
                self.table
                    .elements(std::slice::from_ref(t))
                    .iter()
                    .any(|t| t.as_spread().is_some())
            })
    }

    /// expressions.arguments and expressions.inout-arguments.
    pub(super) fn arguments(
        &mut self,
        cx: &mut Cx,
        at: TextRange,
        params: &[(Mode, Ty)],
        passing: &[bool],
        args: &[Arg],
    ) -> Vec<tast::Arg> {
        if self.spreads_in(params, args) {
            return self.spread_arguments(cx, at, params, args);
        }
        if params.len() != args.len() {
            let (n, m) = (params.len(), args.len());
            let message = format!(
                "this takes {n} argument{}, but {m} {} given",
                if n == 1 { "" } else { "s" },
                if m == 1 { "is" } else { "are" }
            );
            self.error(codes::E0315, at, message);
            return args
                .iter()
                .map(|a| tast::Arg {
                    mode: arg_mode(a),
                    value: self.abandon(cx, &a.value),
                    passes: false,
                    kept: false,
                })
                .collect();
        }
        let passes = |i: usize| passing.get(i).copied().unwrap_or(false);
        let checked = params
            .iter()
            .zip(args)
            .enumerate()
            .map(|(i, ((mode, ty), a))| {
                // Before the argument meets it, a type parameter's type is still a variable.
                let kept = matches!(ty, Ty::Fn(_)) && !passes(i);
                let value = self.argument(cx, *mode, ty, a);
                match (mode, a.inout) {
                    (Mode::Inout, false) => {
                        let message =
                            "this parameter is `inout`, so its argument is marked `inout`";
                        // Only a place, and not a field read through an `Option` or an element read
                        // through a view, can be passed `inout` (expressions.inout-arguments;
                        // types.option-field-not-place; projections.places-through-views).
                        let place =
                            checked_place(&a.value, &value) && not_a_place(&value).is_none();
                        let fix = place.then(|| {
                            let mark = Edit::insert(a.value.at.start(), "inout ");
                            Fix::new("mark it `inout`", vec![mark])
                        });
                        let fixes = fix.into_iter().collect();
                        self.error_fixed(codes::E0400, a.value.at, message.to_owned(), fixes);
                    }
                    (Mode::Let, true) => {
                        let message = "this parameter isn't `inout`, so its argument isn't marked";
                        let mark = TextRange::new(a.at.start(), a.value.at.start());
                        let fix = Fix::new("delete the `inout`", vec![Edit::delete(mark)]);
                        self.error_fixed(codes::E0400, a.value.at, message.to_owned(), vec![fix]);
                    }
                    _ => {}
                }
                tast::Arg {
                    mode: *mode,
                    value,
                    // A parameter of the error type keeps nothing, since no diagnostic arises
                    // from it (errors.error-type).
                    passes: passes(i) || matches!(ty, Ty::Error),
                    kept,
                }
            })
            .collect();
        // The arguments may decide the types that bounds give traits' parameters
        // (traits.bound-arguments).
        self.settle_args();
        checked
    }

    /// An argument for a parameter of mode `mode` and type `ty`.
    fn argument(&mut self, cx: &mut Cx, mode: Mode, ty: &Ty, a: &Arg) -> tast::Expr {
        match mode {
            Mode::Inout if a.inout && !may_be_place(&a.value) => {
                let message = "only a variable, a field or an element can be passed `inout`";
                self.error(codes::E0401, a.value.at, message.to_owned());
                self.abandon(cx, &a.value)
            }
            Mode::Inout => {
                let v = self.infer(cx, Some(ty), &a.value);
                if a.inout && !checked_place(&a.value, &v) {
                    let message = "only a variable, a field or an element can be passed `inout`";
                    self.error(codes::E0401, a.value.at, message.to_owned());
                    return error_node(a.value.at);
                } else if let Some(reason) = not_a_place(&v).filter(|_| a.inout) {
                    let message = format!("{reason}, so it can't be passed `inout`");
                    self.error(codes::E0401, a.value.at, message);
                } else if !self.leaving(a.value.at, ty, self.place_depth(&v), "be passed to it") {
                    // The callee writes the place back, so its type is the parameter's exactly
                    // (effects.inout-function-arguments). A fresh type it would give a variable
                    // declared outside its arm leaves the arm (meta.leaving-arm).
                    self.expect(a.value.at, ty, &v.ty);
                }
                v
            }
            Mode::Let => self.check(cx, ty, &a.value),
        }
    }

    /// A call that can't be checked, whose arguments are checked as the error type, a spread's
    /// `e` among them, since a spread stands among a call's arguments.
    pub(super) fn give_up(&mut self, cx: &mut Cx, at: TextRange, args: &[Arg]) -> tast::Expr {
        for a in args {
            match &a.value.kind {
                hir::ExprKind::Spread(inner) => self.abandon(cx, inner),
                _ => self.abandon(cx, &a.value),
            };
        }
        error_node(at)
    }

    /// The receiver `r` of a method whose `self` has the mode `mode`, as an argument.
    fn receiver_arg(&mut self, receiver: &hir::Expr, r: tast::Expr, mode: Mode) -> tast::Arg {
        if mode == Mode::Inout && (!checked_place(receiver, &r) || not_a_place(&r).is_some()) {
            let message = "this method takes `inout self`, so its receiver must be a variable, a \
                           field or an element";
            self.error(codes::E0401, receiver.at, message.to_owned());
        }
        tast::Arg {
            mode,
            value: r,
            passes: false,
            kept: false,
        }
    }

    /// A call of a member `m` of the inherent impls of the receiver's type `ty`.
    #[allow(clippy::too_many_arguments)]
    fn inherent_call(
        &mut self,
        cx: &mut Cx,
        at: TextRange,
        receiver: &hir::Expr,
        r: tast::Expr,
        ty: &Ty,
        name: &Ident,
        m: &MemberInfo,
        args: &[Arg],
    ) -> tast::Expr {
        let mode = match m.kind {
            MemberKindInfo::Method(mode) => mode,
            MemberKindInfo::Function => {
                let message = format!(
                    "`{0}` takes no `self`, so it is called as `{1}.{0}(…)`",
                    name.name, m.owner.name
                );
                self.error(codes::E0314, name.at, message);
                return self.give_up(cx, at, args);
            }
            MemberKindInfo::Constant => {
                let message = format!(
                    "`{0}` is a constant, written `{1}.{0}`",
                    name.name, m.owner.name
                );
                self.error(codes::E0314, name.at, message);
                return self.give_up(cx, at, args);
            }
        };
        self.require_visible(name, m);
        let inst = self.instantiate(name.at, &Sig::of(&m.signature, None), None, at);
        let (self_ty, rest) = match inst.params.split_first() {
            Some(((_, t), rest)) => (t.clone(), rest),
            None => (Ty::Error, &[][..]),
        };
        self.expect(receiver.at, &self_ty, ty);
        let mut call_args =
            self.arguments(cx, at, rest, inst.passing.get(1..).unwrap_or(&[]), args);
        self.perform_call(cx, inst.row.clone(), at);
        call_args.insert(0, self.receiver_arg(receiver, r, mode));
        let callee = Callee::Member(m.owner.clone(), m.name);
        self.c_use(&callee, &inst.targs, at);
        call_node(callee, inst, call_args, at)
    }

    /// A call of the method `m` of `trait_item`, which the receiver's type `ty` implements.
    #[allow(clippy::too_many_arguments)]
    fn trait_call(
        &mut self,
        cx: &mut Cx,
        at: TextRange,
        receiver: &hir::Expr,
        r: tast::Expr,
        ty: &Ty,
        name: &Ident,
        (trait_item, m): (Item, &TraitMethod),
        args: &[Arg],
    ) -> tast::Expr {
        let Some(mode) = self.method_mode(name, (&trait_item, m), ty) else {
            return self.give_up(cx, at, args);
        };
        let self_ty = self.self_for(&trait_item, ty, at);
        let fixed = self.trait_params(&trait_item, ty, at);
        let sig = Sig::of(&m.signature, None).with_fixed(fixed);
        let inst = self.instantiate(name.at, &sig, Some(&self_ty), at);
        self.obligation(
            self.implementer(&trait_item, ty, &self_ty),
            trait_item.clone(),
            name.at,
        );
        let rest = match inst.params.split_first() {
            // A constructor trait's receiver writes its type, whose arguments its own are
            // (traits.receiver-types).
            Some(((_, receiver_ty), rest)) => {
                if self.arity(&trait_item) > 0 {
                    self.expect(receiver.at, receiver_ty, ty);
                }
                rest
            }
            None => &[][..],
        };
        let mut call_args =
            self.arguments(cx, at, rest, inst.passing.get(1..).unwrap_or(&[]), args);
        self.perform_call(cx, inst.row.clone(), at);
        call_args.insert(0, self.receiver_arg(receiver, r, mode));
        let callee = Callee::TraitMethod(trait_item, m.name, ty.clone());
        call_node(callee, inst, call_args, at)
    }

    /// The mode of the receiver of a trait's member `m` called as a method, or E0314 for a function
    /// without `self` or a constant, which is named on the type (traits.functions-without-self and
    /// traits.trait-constants).
    fn method_mode(
        &mut self,
        name: &Ident,
        (t, m): (&Item, &TraitMethod),
        ty: &Ty,
    ) -> Option<Mode> {
        let shown = self.show(ty);
        let message = match m.kind {
            MemberKindInfo::Method(mode) => return Some(mode),
            MemberKindInfo::Function => format!(
                "`{0}` is a function of `{1}` without `self`, so it is called as `{shown}.{0}(…)`",
                name.name, t.name
            ),
            MemberKindInfo::Constant => format!(
                "`{0}` is a constant of `{1}`, written `{shown}.{0}`",
                name.name, t.name
            ),
        };
        self.error(codes::E0314, name.at, message);
        None
    }

    /// The call `r.name(…)` where the type `ty` of `r` has no method `name`: of a field, or a
    /// tuple's element, that holds a function.
    #[allow(clippy::too_many_arguments)]
    fn field_call(
        &mut self,
        cx: &mut Cx,
        at: TextRange,
        receiver: &hir::Expr,
        r: tast::Expr,
        ty: &Ty,
        name: &Ident,
        args: &[Arg],
    ) -> tast::Expr {
        let field = match (name.name.parse::<usize>(), ty) {
            (Ok(i), Ty::Tuple(ts)) if i < ts.len() => {
                Some((tast::ExprKind::TupleField(Box::new(r), i), ts[i].clone()))
            }
            (Ok(_), _) => None,
            (Err(_), _) => self
                .record_fields(ty)
                .and_then(|fields| fields.into_iter().find(|(n, _)| *n == name.name))
                .map(|(_, t)| (tast::ExprKind::Field(Box::new(r), name.name), t)),
        };
        let Some((kind, field_ty)) = field else {
            if !self.left_out(ty, &name.name) {
                let message = format!("`{}` has no method `{}`", self.show(ty), name.name);
                let methods = self.method_names(ty, true);
                self.not_found(codes::E0314, name, message, methods.iter().map(|n| &**n));
            }
            return self.give_up(cx, at, args);
        };
        // A field of a polymorphic function type is instantiated at each call
        // (polymorphism.instantiation).
        let f = self.instantiated(node(kind, field_ty, receiver.at));
        match self.resolved(&f.ty) {
            Ty::Fn(fty) => {
                let call_args = self.arguments(cx, at, &fty.params, &[], args);
                self.perform_call(cx, fty.row, at);
                node(
                    tast::ExprKind::CallValue(Box::new(f), call_args),
                    fty.ret,
                    at,
                )
            }
            t => {
                let message = format!("expected a function, found `{}`", self.show(&t));
                self.error(codes::E0311, name.at, message);
                self.give_up(cx, at, args)
            }
        }
    }

    fn method_call(
        &mut self,
        cx: &mut Cx,
        at: TextRange,
        receiver: &hir::Expr,
        name: &Ident,
        args: &[Arg],
    ) -> tast::Expr {
        let r = self.infer(cx, None, receiver);
        let Some(ty) = self.known(receiver.at, &r.ty) else {
            return self.give_up(cx, at, args);
        };
        let name = &self.edition_name(&ty, name);
        match self.find_method(&ty, &name.name) {
            Found::Inherent(m) => self.inherent_call(cx, at, receiver, r, &ty, name, m, args),
            Found::ViaTrait(t, m) => self.trait_call(cx, at, receiver, r, &ty, name, (t, m), args),
            Found::Ambiguous(traits) => {
                let call = Ambiguous::Method {
                    at,
                    receiver: receiver.at,
                    args,
                };
                self.ambiguous(name, &traits, &call);
                self.give_up(cx, at, args)
            }
            Found::Missing => self.field_call(cx, at, receiver, r, &ty, name, args),
        }
    }

    pub(super) fn call(
        &mut self,
        cx: &mut Cx,
        (at, expected): (TextRange, Option<&Ty>),
        callee: &hir::Expr,
        args: &[Arg],
    ) -> tast::Expr {
        match &callee.kind {
            ExprKind::Func(item) => {
                let Some(s) = self.env.decls.function(item) else {
                    return error_node(at);
                };
                let inst = self.instantiate(callee.at, &Sig::of(s, None), None, callee.at);
                let first = self.errors.len();
                let call_args = self.arguments(cx, at, &inst.params, &inst.passing, args);
                self.printing_several(item, first, args);
                self.perform_call(cx, inst.row.clone(), at);
                let target = Callee::Function(item.clone());
                self.c_use(&target, &inst.targs, at);
                call_node(target, inst, call_args, at)
            }
            ExprKind::Variant(item) => self.variant_call(cx, at, callee, item, args),
            ExprKind::Perform(effect, op) => self.perform_op(cx, (at, callee.at), effect, op, args),
            ExprKind::Member(owner, name)
                if let Some(read) = self.reflect_call(cx, at, owner, name, args) =>
            {
                read
            }
            ExprKind::Member(owner, name) => match self.member(callee.at, owner, name, expected) {
                Some((target, _)) if self.is_trait_constant(&target) => {
                    let message = format!(
                        "`{0}` is a constant, read as `{1}` without a call",
                        name.name,
                        self.callee_text(callee)
                    );
                    self.error(codes::E0314, name.at, message);
                    self.give_up(cx, at, args)
                }
                Some((target, inst)) => {
                    let call_args = self.arguments(cx, at, &inst.params, &inst.passing, args);
                    self.perform_call(cx, inst.row.clone(), at);
                    self.c_use(&target, &inst.targs, at);
                    call_node(target, inst, call_args, at)
                }
                None => self.give_up(cx, at, args),
            },
            ExprKind::Field(receiver, name) => self.method_call(cx, at, receiver, name, args),
            _ => self.value_call(cx, at, callee, args),
        }
    }
}
