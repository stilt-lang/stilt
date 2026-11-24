//! Calls past the caps of instances (goal inline-values): a call that an
//! instance makes with a type argument its key can't hold, since the key would grow with each
//! call, as only polymorphic recursion makes it grow without end. Within the instance's own
//! cycle of the call graph, that is a type argument that the instance builds from its own type
//! parameters with more words than a key holds ([`super::keys::MAX_WORDS`]), or that holds
//! such a type, and an argument of several words of a method of a dictionary past the
//! constructors a key knows ([`super::keys::MAX_KNOWN`]), whose entry holds the method's own
//! type parameters in one word. A call of a function that reflects crosses too, with each type
//! argument of several words that it reflects on, so that it is compiled once for all of them
//! (`super::meta`). Each such type *crosses*
//! into the callee boxed: the callee is compiled for a type held in one word, as generic code
//! compiled once holds every argument of one word, and that word is the box of the type's
//! words, its witness the type's shape, so that the runtime reads and writes the lists and maps
//! the callee makes or is given by that shape ([`shrink`]).
//!
//! The call converts each value whose type holds a crossing argument into the callee's
//! representation, and its result and error back ([`Dir`], `convert`): a composite field by
//! field, a list or a map whose elements are of a type that holds the argument by rebuilding
//! it, a value of a recursive type whose nodes hold it by rebuilding its nodes, and a closure by
//! a closure that converts what it takes and gives. The dictionaries of the argument's bounds
//! that the callee is given forward to the argument's own ([`crate::FnRef::Forward`]). Each
//! crossing argument is a type parameter made up for the call, brought into scope while the
//! call is lowered, which the callee's representation names.

mod convert;
mod cross;
mod places;
mod shrink;

pub(crate) use cross::{Witnesses, held_of_words};

use stilt_hir::decls::{FnSig, Lookup};
use stilt_hir::hir::{self, DeclId, GenericId, Item, Mode, Name, Owner};
use stilt_types::tast;
use stilt_types::ty::{FnTy, Row, Subst, Table, Ty};

use super::calls::{Forms, Target, can_raise};
use super::keys::key_word;
use super::places::{Place, Writeback};
use super::words::operands;
use super::{Catcher, Conv, Lower};
use crate::mir::{Arg, Callee, Const, Heapness, Operand};
use crate::{FnRef, Word};

/// Which way a value crosses: into code past the caps, which holds each crossing type argument
/// in its box, or back out of it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Dir {
    In,
    Out,
}

/// A call past the caps: of what, with which signature, and its type arguments as code outside
/// holds them.
#[derive(Clone, Debug)]
pub(crate) struct Crossing {
    pub(crate) callee: Past,
    pub(crate) sig: FnSig,
    /// The type of `Self`, for a trait's method.
    pub(crate) self_ty: Option<Ty>,
    /// The type arguments of the signature's type parameters.
    pub(crate) targs: Vec<Ty>,
    /// Whether each type argument crosses in its box whatever its size: one that the callee
    /// reflects on (`super::meta`).
    pub(crate) reflected: Vec<bool>,
}

/// What a call past the caps calls.
#[derive(Clone, Debug)]
pub(crate) enum Past {
    /// Method `index` of a type parameter's dictionary, whose entry is compiled once for the
    /// method's own type parameters, each held in one word.
    Method(Operand, u32),
    /// A function, with its type arguments.
    Function(FnRef),
    /// The method `name` of trait `t`, on a receiver of type `Self`.
    Trait(Item, Name),
}

/// What a call across the caps calls: a target, with its row, or a closure, with the hidden
/// arguments that a value of a polymorphic function type takes before its own.
pub(crate) enum Bridged {
    Target(Target, Row),
    Closure(Operand, Vec<Arg>),
}

/// How an argument of a call past the caps is given: its words, or for an `inout` one, where
/// its value is.
pub(crate) enum Given {
    Let(Vec<Operand>),
    Place(Place),
    Pointer(Operand),
}

/// A generic made up for a type argument that crosses, which no declaration has.
pub(crate) fn crossing_generic(index: u32) -> GenericId {
    GenericId {
        owner: Owner {
            decl: DeclId {
                module: Name::from("#crossing"),
                index: 0,
            },
            member: None,
        },
        index,
    }
}

/// The type a signature gives `t`, `Self` being `self_ty` and each of `params` its argument.
pub(crate) fn sig_type(t: &hir::Ty, self_ty: Option<&Ty>, params: &[GenericId], args: &[Ty]) -> Ty {
    let s = Subst {
        self_ty: self_ty.cloned(),
        types: params.iter().cloned().zip(args.iter().cloned()).collect(),
        rows: Vec::new(),
    };
    Table::default().subst(&s, &Ty::from_hir(t, None))
}

impl Lower<'_> {
    /// A new generic that stands for a type argument that crosses.
    pub(crate) fn cross_generic(&mut self) -> Ty {
        let index = self.next_cross;
        self.next_cross += 1;
        Ty::Param(crossing_generic(index))
    }

    /// The type of `Self` and the type arguments of a call past the caps as its callee holds
    /// them, each type that crosses replaced by a generic brought into scope ([`shrink`]); a
    /// dictionary's method holds each of its own of several words in one word.
    fn demote(&mut self, c: &Crossing) -> (Option<Ty>, Vec<Ty>) {
        let method = matches!(c.callee, Past::Method(..));
        let self_u = match &c.self_ty {
            Some(t) if !method => Some(self.shrink(t)),
            other => other.clone(),
        };
        let targs = c
            .targs
            .iter()
            .enumerate()
            .map(|(i, a)| {
                let u = self.shrink(a);
                let boxed = method || c.reflected.get(i).copied().unwrap_or(false);
                if boxed && !self.one_word(&u) {
                    self.crossing_for(u)
                } else {
                    u
                }
            })
            .collect();
        (self_u, targs)
    }

    /// What a call past the caps calls, for its type arguments as the callee holds them.
    fn past_target(&mut self, c: &Crossing, self_u: Option<&Ty>, targs_u: &[Ty]) -> Target {
        match &c.callee {
            Past::Method(dict, index) => {
                let hidden = {
                    let packs = self.pack_kinds(&c.sig, targs_u, None);
                    self.generic_args(&c.sig.type_params, &packs, targs_u)
                };
                Target::Method(dict.clone(), *index, hidden, Box::new(c.sig.clone()))
            }
            Past::Function(f) => self.direct(f.clone(), targs_u),
            Past::Trait(t, name) => {
                self.trait_target(t, *name, self_u.unwrap_or(&Ty::Error), targs_u)
            }
        }
    }

    /// Takes the generics from `start` on, and the crossings from `crossed` on, out of scope.
    pub(crate) fn undemote(&mut self, start: usize, crossed: usize) {
        self.generics.truncate(start);
        self.crossing.truncate(crossed);
        self.instances.borrow_mut().clear();
    }

    /// The dictionary of trait `t` for a type of type `a` that crosses boxed: its entries
    /// forward to `a`'s own dictionary, which it holds after them with `a`'s witness.
    pub(crate) fn forward_dict(&mut self, a: &Ty, t: &Item) -> Operand {
        let methods = self.decls().trait_info(t).map_or(0, |i| i.methods.len());
        let words: Box<[Word]> = self.layout(a).into_iter().map(key_word).collect();
        let mut fields: Vec<(Operand, Heapness)> = (0..methods)
            .map(|i| {
                let index = u32::try_from(i).expect("under 4G methods");
                let entry = FnRef::Forward(t.clone(), index, words.clone());
                (Operand::Const(Const::Code(entry)), Heapness::Static(false))
            })
            .collect();
        fields.push((self.dict(a, t), Heapness::Static(true)));
        fields.push((self.witness(a), Heapness::Static(false)));
        self.alloc(0, fields)
    }

    /// A call past the caps, with the arguments of the typed body.
    pub(crate) fn call_crossing(
        &mut self,
        c: &Crossing,
        args: &[tast::Arg],
        row: &Row,
        e: &tast::Expr,
    ) -> Vec<Operand> {
        // Every `let` argument is evaluated, from left to right, before the `inout` places are
        // read (values.left-to-right).
        let given: Vec<Given> = args
            .iter()
            .map(|a| match a.mode {
                Mode::Let => Given::Let(self.expr(&a.value)),
                Mode::Inout => Given::Place(self.place(&a.value)),
            })
            .collect();
        let loc = self.loc_at(e.at);
        self.cross_call(c, given, loc, row, &e.ty)
    }

    /// A call past the caps, with its arguments as `given` gives them, as code outside holds
    /// them, and its result `ret`, which it returns in its words.
    pub(crate) fn cross_call(
        &mut self,
        c: &Crossing,
        given: Vec<Given>,
        loc: Operand,
        row: &Row,
        ret: &Ty,
    ) -> Vec<Operand> {
        let (start, crossed) = (self.generics.len(), self.crossing.len());
        let (self_u, targs_u) = self.demote(c);
        let params: Vec<GenericId> = c.sig.type_params.iter().map(|(g, _)| g.clone()).collect();
        let types = |t: &hir::Ty| {
            let n = sig_type(t, c.self_ty.as_ref(), &params, &c.targs);
            let u = sig_type(t, self_u.as_ref(), &params, &targs_u);
            (n, u)
        };
        let target = self.past_target(c, self_u.as_ref(), &targs_u);
        let args = given
            .into_iter()
            .zip(&c.sig.params)
            .map(|(g, (_, t))| {
                let (n, u) = types(t);
                (g, n, u)
            })
            .collect();
        let ret_u = types(&c.sig.ret).1;
        let errs = c.sig.row.raise.as_ref().map(|t| types(t));
        let row_u = Row {
            raise: errs.as_ref().map(|(_, u)| Box::new(u.clone())),
            ..row.clone()
        };
        let call = Bridged::Target(target, row_u);
        let out = self.bridged_call(call, args, Dir::In, (ret, &ret_u), errs, loc);
        self.undemote(start, crossed);
        out
    }

    /// A function called past the caps named as a value of type `n`: the closure of its code
    /// for its type arguments as past the caps, held by a closure that converts what it takes
    /// and gives.
    pub(crate) fn crossing_value(
        &mut self,
        c: &Crossing,
        callee: &tast::Callee,
        n: &Ty,
    ) -> Operand {
        let (start, crossed) = (self.generics.len(), self.crossing.len());
        let (self_u, targs_u) = self.demote(c);
        let target = self.past_target(c, self_u.as_ref(), &targs_u);
        let value = self.target_value(target, callee, &targs_u);
        let params: Vec<GenericId> = c.sig.type_params.iter().map(|(g, _)| g.clone()).collect();
        let u_of = |t: &hir::Ty| sig_type(t, self_u.as_ref(), &params, &targs_u);
        let out = match n {
            Ty::Fn(nf) => {
                let u = Ty::Fn(Box::new(FnTy {
                    generics: nf.generics.clone(),
                    bound_args: nf.bound_args.clone(),
                    params: c.sig.params.iter().map(|(m, t)| (*m, u_of(t))).collect(),
                    ret: u_of(&c.sig.ret),
                    row: Row {
                        raise: c.sig.row.raise.as_ref().map(|t| Box::new(u_of(t))),
                        ..nf.row.clone()
                    },
                }));
                let words = self.cross_convert(vec![value], n, &u, Dir::Out);
                operands(&self.copy_into_temps(words, n))
            }
            _ => vec![value],
        };
        self.undemote(start, crossed);
        out.into_iter().next().unwrap_or(Operand::word(0))
    }

    /// A call of code whose values are held as on one side of the caps, from code on the
    /// other: each argument, given with its type outside and past the caps, converts in
    /// direction `dir`, and the result, of types `ret` outside and past the caps, and the error,
    /// of types `errs`, convert back, the result into new locals.
    pub(crate) fn bridged_call(
        &mut self,
        call: Bridged,
        args: Vec<(Given, Ty, Ty)>,
        dir: Dir,
        (ret_n, ret_u): (&Ty, &Ty),
        errs: Option<(Ty, Ty)>,
        loc: Operand,
    ) -> Vec<Operand> {
        let back = if dir == Dir::In { Dir::Out } else { Dir::In };
        let inner = |n: &Ty, u: &Ty| if dir == Dir::In { u.clone() } else { n.clone() };
        let forms = match &call {
            Bridged::Target(target, _) => self.forms_of(target),
            Bridged::Closure(..) => Forms::layout(),
        };
        let (values, backs, writebacks) = self.bridged_args(args, &forms, dir);
        let callee_ret = inner(ret_n, ret_u);
        let catcher = errs.as_ref().map(|(n, u)| {
            let ty = inner(n, u);
            let catcher = Catcher {
                error: self.temps(&ty),
                ty,
                arms: self.b.new_block(),
            };
            self.catchers.push(catcher.clone());
            catcher
        });
        let result = match call {
            Bridged::Target(target, row) => {
                let raises = can_raise(&row);
                self.emit_call(target, values, &writebacks, loc, raises, &callee_ret, &row)
            }
            Bridged::Closure(closure, mut hidden) => {
                let err = errs.as_ref().map_or(Ty::Error, |(n, u)| inner(n, u));
                let (ret, err) = (Conv::of(callee_ret.clone()), Conv::boxed(err));
                let callee = Callee::Value(closure);
                hidden.extend(values);
                self.finish_call(callee, hidden, &writebacks, loc, true, &ret, &err)
            }
        };
        if catcher.is_some() {
            self.catchers.pop();
        }
        self.cross_back(&backs);
        let result = self.cross_convert(result, ret_n, ret_u, back);
        let outer = if dir == Dir::In { ret_n } else { ret_u };
        let out = self.copy_into_temps(result, outer);
        if let (Some(catcher), Some((n, u))) = (catcher, errs) {
            let join = self.b.new_block();
            self.b.goto(join);
            self.b.switch_to(catcher.arms);
            self.pass_aborts();
            self.cross_back(&backs);
            let error = self.cross_convert(operands(&catcher.error), &n, &u, back);
            self.raise(error);
            self.b.switch_to(join);
        }
        operands(&out)
    }

    /// The arguments of a call across the caps, each given with its type outside and past the
    /// caps and converted in direction `dir`, with the `inout` ones to convert back and to write
    /// back. An `inout` argument whose type both sides hold alike goes as the pointer to its
    /// place, or to its words for a dictionary's method that takes it so.
    fn bridged_args(
        &mut self,
        args: Vec<(Given, Ty, Ty)>,
        forms: &Forms,
        dir: Dir,
    ) -> (Vec<Arg>, Vec<places::Back>, Vec<Writeback>) {
        let (mut values, mut backs, mut writebacks) = (Vec::new(), Vec::new(), Vec::new());
        for (i, (g, n, u)) in args.into_iter().enumerate() {
            match g {
                Given::Let(words) => {
                    let words = self.cross_convert(words, &n, &u, dir);
                    let ty = if dir == Dir::In { &u } else { &n };
                    values.extend(self.pass(words, ty, forms.param(i)));
                }
                Given::Place(place) if n == u => {
                    let (pointer, writeback) = self.inout(place);
                    writebacks.extend(writeback);
                    values.push(Arg::Ref(self.passed_place(pointer, &n, forms, i)));
                }
                Given::Pointer(pointer) if n == u => {
                    values.push(Arg::Ref(self.passed_place(pointer, &n, forms, i)));
                }
                at => {
                    let (pointer, b) = self.cross_inout(at, (&n, &u), dir);
                    values.push(Arg::Ref(pointer));
                    backs.push(b);
                }
            }
        }
        (values, backs, writebacks)
    }

    /// The pointer that passes parameter `i` of a value of type `ty` whose place `pointer`
    /// points to.
    fn passed_place(&mut self, pointer: Operand, ty: &Ty, forms: &Forms, i: usize) -> Operand {
        if forms.self_words(i) {
            self.words_pointer(pointer, ty)
        } else {
            pointer
        }
    }
}
