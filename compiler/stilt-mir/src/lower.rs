//! Lowering typed bodies to MIR, mirroring the reference interpreter's evaluation, whose order of
//! evaluation values.left-to-right, values.assignment-order and values.compound-assignment-order
//! fix.
//!
//! A [`Lower`] builds one function. It knows how each local of the typed body is held, the
//! witnesses and dictionaries of the type parameters in scope, the loops and `try` blocks it is
//! inside, and where its positions are, so that its panics are reported at the right place
//! (program.panic-location).

pub(crate) mod arrays;
pub(crate) mod bridge;
pub(crate) mod calls;
mod closures;
pub(crate) mod cons;
mod constants;
mod control;
mod conventions;
pub(crate) mod dicts;
mod exprs;
mod foreign;
pub(crate) mod functions;
mod handlers;
mod hidden;
pub(crate) mod keys;
pub(crate) mod lists;
pub(crate) mod meta;
mod names;
pub(crate) mod natives;
mod notes;
mod numeric;
pub(crate) mod packs;
mod pairs;
mod patterns;
mod places;
mod poly;
mod projections;
mod proved;
pub(crate) mod raises;
mod records;
mod scopes;
mod shared;
pub(crate) mod strings;
pub(crate) mod targets;
pub(crate) mod traits;
mod unique;
mod values;
mod views;
mod windows;
pub(crate) mod words;

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;
use std::sync::Arc;

use stilt_db::{Db, Program};
use stilt_diag::LineIndex;
use stilt_hir::decls::{Lookup, Queried};
use stilt_hir::hir::{Item, LocalId};
use stilt_syntax::{TextRange, TextSize};
use stilt_types::ty::Ty;

use crate::build::Builder;
use crate::layout::{Instance, Templates};
use crate::mir::{BlockId, Function, Local, Operand, Repr, Rvalue};
use crate::{FnRef, Held};

pub(crate) use functions::lower;

/// What lowering reads of the program.
pub(crate) struct Cx<'db> {
    pub(crate) db: &'db dyn Db,
    pub(crate) program: Program,
}

impl Cx<'_> {
    pub(crate) fn decls(&self) -> Queried<'_> {
        Queried {
            db: self.db,
            program: self.program,
        }
    }
}

/// Where a body's positions are: the index of its file among the program's files, as the
/// runtime numbers them, and the file's text, whose lines the body's start offsets.
#[derive(Clone)]
pub(crate) struct Origin {
    pub(crate) file: u32,
    pub(crate) start: TextSize,
    pub(crate) text: Arc<str>,
    pub(crate) lines: Arc<LineIndex>,
    /// The checks of the body that verification proves (facts.verification), which
    /// [`Lower::proved_at`] marks.
    pub(crate) proofs: Arc<stilt_types::verify::Proofs>,
}

/// How a local of the typed body is held.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Var {
    /// In locals of its own, one per word of its layout, which a `var` binding may assign
    /// again.
    Value { locals: Vec<Local>, mutable: bool },
    /// Through a pointer in this local to its words: an `inout` parameter.
    Ref(Local),
}

/// How a value is passed, returned or raised (`words`): in the words of its type's layout, as
/// code that names its type, generic code and closures take it, whatever its size; or in one
/// word, its box if it has several, lent as natives and the methods of dictionaries take it, and
/// given as an error of no known type, from a row variable, is raised.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Form {
    Layout,
    Word,
}

/// How a function returns its result, or raises its error.
#[derive(Clone, Debug)]
pub(crate) struct Conv {
    pub(crate) ty: Ty,
    pub(crate) form: Form,
}

impl Conv {
    pub(crate) fn of(ty: Ty) -> Self {
        Self {
            ty,
            form: Form::Layout,
        }
    }

    pub(crate) fn boxed(ty: Ty) -> Self {
        Self {
            ty,
            form: Form::Word,
        }
    }
}

/// The witness and dictionaries of a type parameter, or of `Self`, and the words that hold its
/// values: in an instance whose argument has several words, those of the argument's layout,
/// each a scalar, a heap word, or a word whose heapness a local tells by its lowest bit, which
/// the witness gives (`crate::shape`); otherwise one word, which the witness tells.
#[derive(Clone, Debug)]
pub(crate) struct Generic {
    pub(crate) witness: Local,
    pub(crate) dicts: Vec<(Item, Operand)>,
    pub(crate) held: Option<Vec<Repr>>,
    /// The constructor of its argument and how the constructor's arguments are held, where
    /// the instance's key knows them ([`crate::Known`]).
    pub(crate) known: Option<(Item, Box<[Held]>)>,
    /// A value parameter's value, where the instance's key gives it ([`Held::Value`]).
    pub(crate) value: Option<i128>,
    /// Its descriptor, where the code reflects on it or names it.
    pub(crate) desc: Option<Operand>,
}

impl Generic {
    /// The words that hold a value of the type parameter.
    pub(crate) fn layout(&self) -> Vec<Repr> {
        self.held
            .clone()
            .unwrap_or_else(|| vec![Repr::Generic(self.witness)])
    }
}

/// Where `break` and `continue` go, and the number of `with`s around the loop, which they
/// leave those inside it of.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Loop {
    pub(crate) exit: BlockId,
    pub(crate) next: BlockId,
    pub(crate) withs: usize,
}

/// What a block holds until it ends, however it ends: the node of the handler a `with`
/// installed, or the handles of the values a `when` holds.
#[derive(Clone, Debug)]
pub(crate) enum Exit {
    With(Local),
    When(Vec<Operand>),
}

/// Where a raise goes inside `try … catch`: the block of the arms, with the error's words in
/// locals.
#[derive(Clone, Debug)]
pub(crate) struct Catcher {
    /// The type of the error it handles, and the locals that receive its words.
    pub(crate) ty: Ty,
    pub(crate) error: Vec<Local>,
    pub(crate) arms: BlockId,
}

pub(crate) struct Lower<'a> {
    pub(crate) cx: &'a Cx<'a>,
    pub(crate) b: Builder,
    /// Whether the code belongs to the standard library, whose panics are reported at the call
    /// that led into it, which its location parameter holds.
    pub(crate) std: bool,
    pub(crate) loc: Local,
    pub(crate) origin: Option<Origin>,
    pub(crate) vars: HashMap<LocalId, Var>,
    /// The type parameters in scope, and `Self` in a trait's default method.
    pub(crate) generics: Vec<(Ty, Generic)>,
    /// The arguments the bounds of the type parameters in scope give traits with parameters
    /// (traits.bound-arguments).
    pub(crate) bound_args: Vec<(Ty, Item, Vec<Ty>)>,
    /// The constructors that the instance's key gives its constructor parameters, and `Self` in a
    /// constructor trait's default method, which its types are compiled for, and the number of
    /// generics they take from the key.
    pub(crate) cons: crate::lower::cons::Cons,
    /// The element that each spread's type parameter stands for, in the bodies of the spreads
    /// being lowered, the outermost's first (`packs`).
    pub(crate) elements: Vec<(stilt_hir::hir::GenericId, Ty)>,
    pub(crate) loops: Vec<Loop>,
    /// The places of the loops being lowered, whose bodies' runs a profile counts.
    pub(crate) loop_places: Vec<stilt_syntax::TextRange>,
    pub(crate) catchers: Vec<Catcher>,
    /// What the `with`s and `when`s around the code being lowered hold, which a jump out of
    /// them ends, the innermost last (`handlers`, `shared`).
    pub(crate) withs: Vec<Exit>,
    /// The names of the typed body's locals.
    pub(crate) names: Vec<stilt_hir::hir::Name>,
    /// The functions of the closures the body holds, lowered.
    pub(crate) closures: Vec<Function>,
    pub(crate) next_closure: u32,
    /// Where the code being lowered stands to the function of a scope (`scopes`).
    pub(crate) scope: scopes::Scoped,
    pub(crate) templates: Templates<'a>,
    /// The layouts of the declared types met so far, which follow the generics in scope.
    pub(crate) instances: RefCell<HashMap<Ty, Rc<Instance>>>,
    /// How the instance being lowered holds each of its generics, in the order it takes them.
    pub(crate) held: Box<[Held]>,
    /// How the function returns and raises.
    pub(crate) ret: Conv,
    pub(crate) err: Conv,
    /// Whether the function raises in one word whatever its error's type, as a closure's code
    /// does, and so takes, as its last parameter, a pointer to memory that its caller provides
    /// for an error of several words, which it writes there ([`Lower::error_slot`]).
    pub(crate) raises_to_slot: bool,
    slot: Option<Local>,
    /// The generics that stand for type arguments crossing into code past the caps of
    /// instances, each with the type that code outside holds it as (`bridge`), and the number
    /// of generics made up for them so far.
    pub(crate) crossing: Vec<(Ty, Ty)>,
    /// The type parameters of the polymorphic function types around the structure being
    /// converted across the caps, the outermost's first (`bridge`).
    pub(crate) rigid: Vec<Ty>,
    pub(crate) next_cross: u32,
    /// Whether each node of the call graph reaches this function (`keys::cycles`).
    cycles: RefCell<HashMap<keys::Node, bool>>,
    /// In a projection's body, the parameter that holds the caller's access, a closure given a
    /// pointer to the yielded place (projections.yield; `projections`).
    pub(crate) access: Option<Local>,
    /// The values of the expressions of a construct whose places are rooted in projections'
    /// calls, evaluated before the projections open, by their nodes (`projections`).
    pub(crate) evaluated: HashMap<projections::Node, (Vec<Operand>, Ty)>,
    /// The pointers to the places that the projections opened so far have yielded, by the nodes
    /// of their calls.
    pub(crate) opened: HashMap<projections::Node, Local>,
    /// The pointers to the roots of such a construct's places in this frame, by their nodes.
    pub(crate) roots: HashMap<projections::Node, Local>,
    /// Where the value that the construct's access gives goes, and its type.
    pub(crate) out: Option<(Local, Ty)>,
}

impl<'a> Lower<'a> {
    pub(crate) fn new(cx: &'a Cx<'a>, name: FnRef, std: bool) -> Self {
        let held = name_held(&name);
        let mut b = Builder::new(name);
        let loc = b.param(Repr::Scalar, crate::mir::ParamMode::Borrowed, None);
        Self {
            cx,
            b,
            std,
            loc,
            origin: None,
            vars: HashMap::new(),
            generics: Vec::new(),
            bound_args: Vec::new(),
            cons: crate::lower::cons::Cons::default(),
            elements: Vec::new(),
            loops: Vec::new(),
            loop_places: Vec::new(),
            catchers: Vec::new(),
            withs: Vec::new(),
            names: Vec::new(),
            closures: Vec::new(),
            next_closure: 0,
            scope: scopes::Scoped::Outside,
            templates: Templates::new(cx.decls()),
            instances: RefCell::new(HashMap::new()),
            held,
            ret: Conv::of(Ty::unit()),
            err: Conv::of(Ty::Error),
            raises_to_slot: false,
            slot: None,
            crossing: Vec::new(),
            rigid: Vec::new(),
            next_cross: 0,
            cycles: RefCell::new(HashMap::new()),
            access: None,
            evaluated: HashMap::new(),
            opened: HashMap::new(),
            roots: HashMap::new(),
            out: None,
        }
    }

    pub(crate) fn decls(&self) -> Queried<'a> {
        self.cx.decls()
    }

    /// The number of words the function returns: its result's or its error's, whichever has
    /// more.
    fn results(&self) -> u32 {
        let words = self.width(&self.ret).max(self.width(&self.err));
        u32::try_from(words).expect("under 4G words")
    }

    /// The pointer to the memory for an error of several words that the function raises in one
    /// word, which its last parameter holds.
    pub(crate) fn error_slot(&mut self) -> Local {
        *self.slot.get_or_insert_with(|| self.b.temp(Repr::Scalar))
    }

    /// The function, without closures.
    pub(crate) fn into_function(mut self) -> Function {
        let results = self.results();
        self.add_error_slot();
        self.b.finish(results)
    }

    /// The function and the functions of its closures.
    pub(crate) fn finish(mut self) -> Vec<Function> {
        let results = self.results();
        self.add_error_slot();
        let mut all = vec![self.b.finish(results)];
        all.extend(self.closures);
        all
    }

    fn add_error_slot(&mut self) {
        if self.raises_to_slot {
            let slot = self.error_slot();
            self.b.add_param(slot, crate::mir::ParamMode::Borrowed);
        }
    }

    /// The generic of a type parameter, or of `Self`.
    pub(crate) fn generic(&self, ty: &Ty) -> Option<&Generic> {
        self.generics.iter().find(|(t, _)| t == ty).map(|(_, g)| g)
    }

    /// Brings a generic into scope with its witness and dictionaries, held as the instance
    /// holds its next generic, or as `held` says for one whose holding is known, as a closure
    /// knows its function's.
    pub(crate) fn push_generic(
        &mut self,
        ty: Ty,
        witness: Local,
        dicts: Vec<(Item, Operand)>,
        held: Option<&Held>,
    ) {
        let held = held
            .or_else(|| self.held.get(self.key_index()))
            .cloned()
            .unwrap_or(Held::Word);
        let known = match &held {
            Held::Impl(k) => Some((k.con.clone(), k.args.clone())),
            _ => None,
        };
        let value = match held {
            Held::Value(v) => Some(v),
            _ => None,
        };
        let held = match held.layout() {
            Held::Words(words) => Some(self.held_words(witness, words)),
            _ => None,
        };
        self.instances.borrow_mut().clear();
        self.generics.push((
            ty,
            Generic {
                witness,
                dicts,
                held,
                known,
                value,
                desc: None,
            },
        ));
    }

    /// The bounds of the type parameters in scope, as the type checker states them.
    pub(crate) fn bounds(&self) -> stilt_types::Bounds {
        self.generics
            .iter()
            .map(|(t, g)| {
                (
                    t.clone(),
                    g.dicts.iter().map(|(tr, _)| tr.clone()).collect(),
                )
            })
            .collect()
    }

    /// The location of the operation at `at` (program.panic-location): the location parameter in
    /// the standard library, and otherwise the start of the operation in its file.
    pub(crate) fn loc_at(&self, at: TextRange) -> Operand {
        match (&self.origin, self.std) {
            (Some(o), false) => {
                let position = o.lines.position(&o.text, o.start + at.start());
                Operand::word(stilt_runtime_location(o.file, position.line, position.col))
            }
            _ => Operand::Local(self.loc),
        }
    }

    /// Lowers the code that follows as coming from the start of `at` in its file, for a
    /// debugger's line table (goal debuggable-builds). The standard library's code has no
    /// location of its own.
    pub(crate) fn source_at(&mut self, at: TextRange) {
        let word = match (&self.origin, self.std) {
            (Some(o), false) => {
                let position = o.lines.position(&o.text, o.start + at.start());
                stilt_runtime_location(o.file, position.line, position.col)
            }
            _ => 0,
        };
        self.b.set_at(word);
    }

    /// How the local `id` of type `ty` is held. One that no pattern bound is a binding of a
    /// pattern with an error, which the code after it reads: it gets locals of its own, and
    /// the function panics in place of running (program.bodies-with-errors).
    pub(crate) fn var(&mut self, id: LocalId, ty: &Ty) -> Var {
        if let Some(var) = self.vars.get(&id) {
            return var.clone();
        }
        self.b.met_error();
        let locals = self.bind_locals(id, ty, true);
        Var::Value {
            locals,
            mutable: true,
        }
    }

    /// The words of a local of the typed body, as operands that later code can't change.
    pub(crate) fn read_var(&mut self, id: LocalId, ty: &Ty) -> Vec<Operand> {
        match self.var(id, ty) {
            Var::Value {
                locals,
                mutable: false,
            } => locals.into_iter().map(Operand::Local).collect(),
            Var::Value { locals, .. } => locals
                .into_iter()
                .map(|l| {
                    let repr = self.b.repr_of(l);
                    self.b.define_op(repr, Rvalue::Use(Operand::Local(l)))
                })
                .collect(),
            Var::Ref(pointer) => self.load_words(&Operand::Local(pointer), ty),
        }
    }

    /// Whether a type implements a trait, under the bounds in scope.
    pub(crate) fn implements(&self, ty: &Ty, trait_item: &Item) -> bool {
        let decls = self.decls();
        let scope = (&self.bounds(), self.bound_args.as_slice());
        stilt_types::implements_trait(&decls as &dyn Lookup, scope, ty, trait_item)
    }
}

/// A location word, as the runtime decodes it: the file, line and column of `stilt_runtime`'s
/// `location`.
pub(crate) fn stilt_runtime_location(file: u32, line: u32, col: u32) -> u64 {
    u64::from(file) << 44 | (u64::from(line) & 0xff_ffff) << 20 | u64::from(col) & 0xf_ffff
}

/// How an instance holds each of its generics, by its name: a closure as its function does.
fn name_held(name: &FnRef) -> Box<[Held]> {
    match name {
        FnRef::Closure(parent, _) => name_held(parent),
        _ => name.held().into(),
    }
}
