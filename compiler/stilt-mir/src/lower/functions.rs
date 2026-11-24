//! Lowering the body of a function or a constant: its parameters, in the order of the calling
//! convention, then its code. A `let` parameter is one parameter per word of its type's layout,
//! and an `inout` one a pointer to its words.

use std::sync::Arc;

use stilt_db::SourceFile;
use stilt_diag::LineIndex;
use stilt_hir::decls::{FnSig, Lookup};
use stilt_hir::hir::{Item, LocalId, Mode, Name};
use stilt_hir::{body_starts, module_hir};
use stilt_syntax::TextRange;
use stilt_types::infer_body;
use stilt_types::tast::{Code, Definition, Stmt, StmtKind, TestKind};
use stilt_types::ty::{Row, Ty};

use super::calls::error_type;
use super::cons::is_constructor;
use super::{Conv, Cx, Lower, Origin, Var};
use crate::FnRef;
use crate::items::{Code as Where, ImplRef, code_of};
use crate::mir::{Counted, Function, Operand, ParamMode, Repr};

/// The functions that make up `f`: its own, and those of the closures it holds. A native
/// function, and one the compiler makes, have none here.
pub(crate) fn lower(cx: &Cx<'_>, f: &FnRef) -> Vec<Function> {
    let Some(Where::Body(file, index)) = code_of(cx.db, cx.program, f.clone()) else {
        return Vec::new();
    };
    let typed = &infer_body(cx.db, cx.program, file, index).body;
    let std = module_hir(cx.db, cx.program, file).std;
    let mut l = Lower::new(cx, f.clone(), std);
    l.origin = origin(cx, (file, index), std);
    l.names.clone_from(&typed.locals);
    match f.generic() {
        FnRef::Const(item) | FnRef::MemberConst(item, _) => {
            l.ret = Conv::of(constant_type(cx, f, item));
        }
        // A test's body gives `()`, an example's a `bool` and a property's its closure, and each
        // raises the error its code raises (program.test-declarations and program.doc-examples;
        // tests.property-form).
        FnRef::Test(..) => {
            let Some(tested) = &typed.tested else {
                return Vec::new();
            };
            l.ret = Conv::of(match tested.kind {
                TestKind::Test => Ty::unit(),
                TestKind::Example => Ty::bool(),
                TestKind::Property => match &typed.code {
                    Definition::Code(Code::Block(b)) => match b.first().map(|s| &s.kind) {
                        Some(StmtKind::Expr(e)) => e.ty.clone(),
                        _ => return Vec::new(),
                    },
                    _ => return Vec::new(),
                },
            });
            l.err = Conv::of(tested.error.clone());
        }
        _ => {
            let Some(sig) = signature(&cx.decls(), f) else {
                return Vec::new();
            };
            l.add_generics(f, &sig);
            l.add_params(&typed.params, &sig);
        }
    }
    l.count_at(Counted::Entry, TextRange::empty(0.into()));
    let example = typed
        .tested
        .as_ref()
        .is_some_and(|t| t.kind == TestKind::Example);
    match &typed.code {
        Definition::Code(code) if example => l.example(code),
        Definition::Code(code) if l.cons.is_empty() => l.body(code),
        Definition::Code(code) => {
            let code = l.retyped(code);
            l.body(&code);
        }
        Definition::Native | Definition::Broken => return Vec::new(),
    }
    l.finish()
}

/// The type of a constant's value.
fn constant_type(cx: &Cx<'_>, f: &FnRef, item: &Item) -> Ty {
    let decls = cx.decls();
    let ty = match f.generic() {
        FnRef::MemberConst(owner, name) => decls
            .inherent_members(owner)
            .iter()
            .find(|m| &m.name == name)
            .map(|m| m.signature.ret.clone()),
        _ => decls.constant(item).cloned(),
    };
    ty.map_or(Ty::Error, |t| Ty::from_hir(&t, None))
}

/// A function with the signature of `f` that panics with `error` as soon as it is called, in
/// place of code with an error (program.bodies-with-errors).
pub(crate) fn check_error(
    cx: &Cx<'_>,
    f: &FnRef,
    error: &crate::check_errors::CheckError,
) -> Option<Function> {
    let mut l = Lower::new(cx, f.clone(), false);
    match f.generic() {
        FnRef::Const(item) | FnRef::MemberConst(item, _) => {
            l.ret = Conv::of(constant_type(cx, f, item));
        }
        _ => {
            let sig = signature(&cx.decls(), f)?;
            l.add_generics(f, &sig);
            l.add_params(&[], &sig);
        }
    }
    l.b.terminate(crate::check_errors::panic_terminator(error));
    let mut function = l.into_function();
    function.broken = false;
    Some(function)
}

/// Where the body `index` of `file` is, and the checks of it that a release build drops, which the
/// standard library's code, whose operations have its caller's location, has none of.
fn origin(cx: &Cx<'_>, (file, index): (SourceFile, u32), std: bool) -> Option<Origin> {
    let position = cx.program.files(cx.db).iter().position(|&f| f == file)?;
    let text: Arc<str> = String::from_utf8_lossy(file.bytes(cx.db)).into();
    let proofs = if std {
        Arc::default()
    } else {
        Arc::new(stilt_types::released(cx.db, cx.program, file, index).clone())
    };
    Some(Origin {
        file: u32::try_from(position).ok()?,
        start: body_starts(cx.db, cx.program, file)[index as usize],
        lines: Arc::new(LineIndex::new(&text)),
        text,
        proofs,
    })
}

/// The signature of a function with a body.
pub(crate) fn signature(decls: &dyn Lookup, f: &FnRef) -> Option<FnSig> {
    match f.generic() {
        FnRef::Function(item) => decls.function(item).cloned(),
        FnRef::Member(owner, name) => decls
            .inherent_members(owner)
            .iter()
            .find(|m| &m.name == name)
            .map(|m| m.signature.clone()),
        FnRef::ImplMethod(t, owner, name) => {
            let imp = decls.trait_impl(t, owner)?;
            match imp.members.iter().find(|m| &m.name == name) {
                Some(m) => Some(m.signature.clone()),
                // A method that the impl lacks panics where it is called
                // (program.programs-with-errors). It takes what the trait's method takes, after the
                // impl's type parameters.
                None => trait_method(decls, t, *name).map(|(_, sig)| FnSig {
                    type_params: imp
                        .generics
                        .iter()
                        .cloned()
                        .chain(sig.type_params)
                        .collect(),
                    values: imp.values.iter().cloned().chain(sig.values).collect(),
                    ..sig
                }),
            }
        }
        FnRef::DefaultMethod(t, name) => trait_method(decls, t, *name).map(|(_, sig)| sig),
        _ => None,
    }
}

/// Whether an impl of a trait calls its own method `name`: one it holds, or one it lacks, which
/// has no default to stand in for it (program.programs-with-errors).
pub(crate) fn calls_own(decls: &dyn Lookup, t: &Item, owner: &Item, name: Name) -> bool {
    let holds = decls
        .trait_impl(t, owner)
        .is_some_and(|i| i.members.iter().any(|m| m.name == name));
    let default = decls
        .trait_info(t)
        .and_then(|info| info.methods.iter().find(|m| m.name == name))
        .is_some_and(|m| m.has_default);
    holds || !default
}

/// Whether an impl holds its trait's method `name`, and whether it calls its own
/// ([`calls_own`]).
pub(crate) fn holds_method(decls: &dyn Lookup, imp: &ImplRef, name: Name) -> Option<(bool, bool)> {
    match imp {
        ImplRef::Written { trait_item, owner } => {
            let holds = decls
                .trait_impl(trait_item, owner)?
                .members
                .iter()
                .any(|m| m.name == name);
            Some((holds, calls_own(decls, trait_item, owner, name)))
        }
        ImplRef::Structural { .. } => Some((true, true)),
    }
}

/// A method of a trait: its place among the trait's methods, and its signature.
pub(crate) fn trait_method(decls: &dyn Lookup, t: &Item, name: Name) -> Option<(u32, FnSig)> {
    let info = decls.trait_info(t)?;
    let index = info.methods.iter().position(|m| m.name == name)?;
    Some((
        u32::try_from(index).expect("under 4G methods"),
        info.methods[index].signature.clone(),
    ))
}

impl Lower<'_> {
    /// Adds a parameter for the witness of each type parameter, and for each of its bounds a
    /// dictionary, and before them, in a trait's default method, those of `Self` and the
    /// witnesses of the trait's parameters, which the impl's arguments give.
    /// A constructor parameter, and a constructor trait's `Self`, take none: the key gives
    /// their constructors.
    pub(crate) fn add_generics(&mut self, f: &FnRef, sig: &FnSig) {
        let decls = self.decls();
        if let FnRef::DefaultMethod(t, _) = f.generic() {
            if decls.trait_info(t).is_some_and(|i| i.arity > 0) {
                let con = self.take_con();
                self.cons.self_ty = Some(con);
            } else {
                self.add_generic(Ty::SelfTy, std::slice::from_ref(t));
            }
            let params = decls
                .trait_info(t)
                .map(|i| i.params.clone())
                .unwrap_or_default();
            for p in &params {
                self.add_generic(Ty::Param(p.clone()), &[]);
            }
            if !params.is_empty() {
                let args = params.into_iter().map(Ty::Param).collect();
                self.bound_args.push((Ty::SelfTy, t.clone(), args));
            }
        }
        let packs = sig.packs();
        for (g, traits) in &sig.type_params {
            if packs.contains(g) {
                self.add_pack_param(g, traits);
            } else if super::records::has_record_bound(traits) {
                self.add_record_param(g);
            } else if is_constructor(&decls, traits) {
                let con = self.take_con();
                self.cons.params.push((g.clone(), con));
            } else {
                self.add_generic(Ty::Param(g.clone()), traits);
            }
        }
        self.add_descriptors(f, sig);
        self.b.hide();
        let scope = stilt_types::params::scope_of(&sig.bound_args);
        let retyped = scope.into_iter().map(|(t, tr, args)| {
            (
                self.cons.ty(&t),
                tr,
                args.iter().map(|a| self.cons.ty(a)).collect(),
            )
        });
        self.bound_args.extend(retyped);
    }

    /// A type of the function's signature, as its code holds it: each constructor parameter
    /// its key's constructor.
    pub(crate) fn sig_ty(&self, t: &stilt_hir::hir::Ty) -> Ty {
        self.cons.ty(&Ty::from_hir(t, None))
    }

    pub(crate) fn add_generic(&mut self, ty: Ty, traits: &[Item]) {
        self.add_generic_held(ty, traits, None);
    }

    /// Adds a generic's witness and dictionaries, held as `held` says, or as the instance's key
    /// holds its next generic. A record bound passes no dictionary (`super::records`).
    pub(crate) fn add_generic_held(&mut self, ty: Ty, traits: &[Item], held: Option<&crate::Held>) {
        let witness = self.b.param(Repr::Scalar, ParamMode::Borrowed, None);
        let dicts = super::records::dict_bounds(traits)
            .iter()
            .map(|t| {
                let d = self.b.param(Repr::Heap, ParamMode::Borrowed, None);
                (t.clone(), Operand::Local(d))
            })
            .collect();
        // Its descriptor, if it travels with the witness.
        let desc = self
            .carries(&ty, traits)
            .then(|| Operand::Local(self.b.param(Repr::Heap, ParamMode::Borrowed, None)));
        self.push_generic(ty, witness, dicts, held);
        self.set_last_descriptor(desc);
        self.b.hide();
    }

    /// Adds the value parameters of the signature, binding the typed body's locals to them,
    /// and takes the signature's result and error as the function's. A hole binds none
    /// (declarations.typed-holes), but its function takes the parameters all the same.
    pub(crate) fn add_params(&mut self, bound: &[(Mode, LocalId)], sig: &FnSig) {
        self.ret = Conv::of(self.sig_ty(&sig.ret));
        let row = self.cons.row(&Row::from_hir(&sig.row, None));
        self.err = Conv::of(error_type(&row));
        self.raises_to_slot = super::raises::raises_to_slot(sig);
        for (i, &(mode, ref ty)) in sig.params.iter().enumerate() {
            let ty = self.sig_ty(ty);
            let id = bound.get(i).map(|&(_, id)| id);
            let name = id.map(|id| self.names[id.0 as usize]);
            let var = self.param_var(mode, name, &ty);
            if let Some(id) = id {
                self.vars.insert(id, var);
            }
        }
        // A projection takes the caller's access last, and gives nothing back but what the
        // access raises (projections.declaring-projection; `super::projections`).
        if sig.projection {
            self.access = Some(self.b.param(Repr::Heap, ParamMode::Borrowed, None));
            self.ret = Conv::of(Ty::unit());
        }
    }

    /// The parameters of a value of type `ty` passed in `mode`, and the variable they hold.
    pub(crate) fn param_var(&mut self, mode: Mode, name: Option<Name>, ty: &Ty) -> Var {
        match mode {
            Mode::Let => {
                let locals = self
                    .words_named(name.as_ref(), ty, false)
                    .into_iter()
                    .map(|w| {
                        let l = self.b.param(w.repr, ParamMode::Borrowed, w.name);
                        self.b.decl_mut(l).shown = w.shown;
                        l
                    })
                    .collect();
                Var::Value {
                    locals,
                    mutable: false,
                }
            }
            Mode::Inout => {
                let repr = self.ref_repr(ty);
                let pointer = self.b.param(repr, ParamMode::Ref, name);
                if self.one_word(ty) {
                    self.b.decl_mut(pointer).shown = Some(crate::repr::shown(ty, true));
                }
                Var::Ref(pointer)
            }
        }
    }

    /// Lowers a doc example's code. An example that is a comparison tells `stilt test` its
    /// sides when it gives `false`.
    fn example(&mut self, code: &Code) {
        let tail = match code {
            Code::Expr(e) => Some(&**e),
            Code::Block(b) => match b.as_slice() {
                [
                    Stmt {
                        kind: StmtKind::Expr(e),
                        ..
                    },
                ] => Some(e),
                _ => None,
            },
        };
        match tail.and_then(|e| Some((self.compared(e)?, e))) {
            Some((compared, e)) => {
                self.source_at(e.at);
                let value = self.noted_comparison(&compared, e);
                self.return_(value);
            }
            None => self.body(code),
        }
    }

    /// Lowers a body's code, which returns its value.
    pub(crate) fn body(&mut self, code: &Code) {
        let value = match code {
            Code::Block(b) => self.block(b),
            Code::Expr(e) => self.expr(e),
        };
        self.return_(value);
    }
}
