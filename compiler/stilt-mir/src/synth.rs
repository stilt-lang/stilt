//! The functions the compiler makes: the entries of dictionaries, the code of functions and
//! variants used as values, structural impls, and the entries of the program and of its tests.
//!
//! Generic code and natives call the entries of dictionaries, which take a value of `Self` or
//! of a type parameter in one word, lent in a box if it has several, and give one in the words
//! that hold it where a type parameter stands; the code of a function used as a value takes
//! every value in those words, as a closure's does. Each converts between the forms it is given its values in and those of the
//! function it calls (`crate::lower::Form`).

mod adapters;
mod crossing;
pub(crate) mod input;
pub(crate) mod props;
mod structural;
mod tests;

use stilt_hir::decls::{Lookup, prelude_item};
use stilt_hir::hir::{DeclId, GenericId, Item, Mode, Name, Owner};
use stilt_types::ty::{Row, Ty};

use crate::FnRef;
use crate::items::Shape;
use crate::lower::calls::{Target, can_raise};
use crate::lower::{Conv, Cx, Form, Lower};
use crate::mir::{
    Arg, Callee, Const, Function, Local, Operand, ParamMode, Repr, Runtime, Rvalue, Stmt,
    Terminator,
};

/// Loads the C libraries that the program's packages link, in the order of c.loading-libraries,
/// before any code of the program runs: the first thing an entry of the program or of a test
/// does.
pub(crate) fn load_libraries(cx: &Cx<'_>, l: &mut Lower<'_>) {
    let packages = cx.program.packages(cx.db);
    let names: String = (packages.libraries().iter())
        .flat_map(|&(_, name, _)| [name, "\n"])
        .collect();
    if !names.is_empty() {
        let names = Operand::Const(Const::Str(names.into()));
        l.b.emit(Stmt::Effect(Runtime::CLoad, vec![names]));
    }
}

/// The functions that make up `f`, if the compiler makes it.
pub(crate) fn synthesize(cx: &Cx<'_>, f: &FnRef) -> Option<Vec<Function>> {
    let function = match f.generic() {
        FnRef::Entry(imp, index) => adapters::entry(cx, f, imp, *index)?,
        FnRef::Value(target) => adapters::value(cx, f, target)?,
        FnRef::Method(t, index) => adapters::method(cx, f, t, *index)?,
        FnRef::Constructor(item) => adapters::constructor(cx, f, item)?,
        FnRef::Lent(n) => adapters::lent(cx, f, *n)?,
        FnRef::Structural(t, name, shape) => structural::structural(cx, f, t, *name, shape)?,
        FnRef::Forward(t, index, words) => crossing::forward(cx, f, t, *index, words)?,
        FnRef::Rebuild(cross, into) => crossing::rebuild(cx, f, cross, *into),
        FnRef::Adapt(cross, into) => crossing::adapt(cx, f, cross, *into)?,
        FnRef::Describe(d) => crate::lower::meta::describe(cx, f, d)?,
        FnRef::Access(d, op) => crate::lower::meta::access(cx, f, d, *op)?,
        FnRef::Shaped(t, walk) => crate::lower::meta::shaped(cx, f, t, *walk)?,
        FnRef::Main => main(cx),
        FnRef::TestEntry(module, index) => tests::entry(cx, f, *module, *index)?,
        FnRef::PropEntry(module, index) => props::entry(cx, f, *module, *index)?,
        FnRef::Decode(module, index, k) => props::decoder(cx, f, *module, *index, *k)?,
        _ => return None,
    };
    Some(vec![function])
}

/// A generic made up for a structural impl's type argument, which no declaration has.
pub(crate) fn made_up_generic(index: u32) -> GenericId {
    GenericId {
        owner: Owner {
            decl: DeclId {
                module: Name::from("#structural"),
                index: 0,
            },
            member: None,
        },
        index,
    }
}

/// The type parameters of a structural impl's constructor.
pub(crate) fn shape_params(decls: &dyn Lookup, shape: &Shape) -> Vec<GenericId> {
    match shape {
        Shape::Con(item) => decls
            .type_info(item)
            .map(|t| t.params.clone())
            .unwrap_or_default(),
        Shape::Tuple(n) => (0..*n).map(made_up_generic).collect(),
        Shape::Pack => vec![made_up_generic(0)],
    }
}

/// The type a structural impl is for, applied to its own parameters.
pub(crate) fn shape_type(shape: &Shape, params: &[GenericId]) -> Ty {
    let args = params.iter().cloned().map(Ty::Param).collect();
    match shape {
        Shape::Con(item) => Ty::Con(item.clone(), args),
        Shape::Tuple(_) => Ty::Tuple(args),
        // Its pack's element, which the type parameter stands for (variadics.type-spreads).
        Shape::Pack => match params {
            [p] => Ty::Tuple(vec![Ty::spread(
                Ty::Param(p.clone()),
                p.clone(),
                Ty::Param(p.clone()),
            )]),
            _ => Ty::Error,
        },
    }
}

impl Lower<'_> {
    /// Reads field `index` of a data object as a borrowed local.
    pub(crate) fn borrowed_field(
        &mut self,
        base: Local,
        len: u32,
        index: u32,
        repr: Repr,
    ) -> Local {
        let local = self.b.temp(repr);
        self.b.decl_mut(local).borrowed = true;
        self.b.assign(
            local,
            Rvalue::Field {
                base: Operand::Local(base),
                len,
                index,
                variant: None,
            },
        );
        local
    }

    /// Adds the parameters of a value of type `ty` passed in `mode` that a caller gives in the
    /// form `from`, and returns the arguments that give it to a function that takes it in the
    /// form `to`. An `inout` value goes as a pointer to the words that hold it.
    pub(crate) fn adapted_param(&mut self, mode: Mode, ty: &Ty, from: Form, to: Form) -> Vec<Arg> {
        match mode {
            Mode::Let => {
                let reprs = match from {
                    Form::Layout => self.layout(ty),
                    Form::Word => vec![self.repr(ty)],
                };
                let params: Vec<Local> = reprs
                    .into_iter()
                    .map(|r| self.b.param(r, ParamMode::Borrowed, None))
                    .collect();
                if from == to {
                    return params
                        .into_iter()
                        .map(|p| Arg::Borrow(Operand::Local(p)))
                        .collect();
                }
                let words = if params.len() == 1 && !self.one_word(ty) {
                    self.unbox_lasting(params[0], ty)
                } else {
                    params.into_iter().map(Operand::Local).collect()
                };
                self.pass(words, ty, to)
            }
            Mode::Inout => {
                let repr = self.ref_repr(ty);
                let p = self.b.param(repr, ParamMode::Ref, None);
                vec![Arg::Ref(Operand::Local(p))]
            }
        }
    }

    /// Calls a target and returns what it returns, raising what it raises, each in the
    /// function's conventions.
    pub(crate) fn tail_call(&mut self, target: Target, args: Vec<Arg>, ret: &Ty, row: &Row) {
        let loc = Operand::Local(self.loc);
        let v = self.emit_call(target, args, &[], loc, can_raise(row), ret, row);
        self.return_(v);
    }

    /// Adds the witnesses and dictionaries of a signature's own type parameters as parameters,
    /// and returns them as the hidden arguments of a call.
    pub(crate) fn own_generics(&mut self, sig: &stilt_hir::decls::FnSig) -> Vec<Arg> {
        let start = self.generics.len();
        for (g, traits) in &sig.type_params {
            self.add_generic(Ty::Param(g.clone()), traits);
        }
        self.b.hide();
        self.generic_hidden(start)
    }

    /// The witnesses and dictionaries of the generics from `start` on, as hidden arguments, and
    /// the descriptor of each whose descriptor travels with them.
    pub(crate) fn generic_hidden(&self, start: usize) -> Vec<Arg> {
        self.generics[start..]
            .iter()
            .flat_map(|(ty, g)| {
                let traits: Vec<Item> = g.dicts.iter().map(|(t, _)| t.clone()).collect();
                let desc = g.desc.clone().filter(|_| self.carries(ty, &traits));
                std::iter::once(Arg::Borrow(Operand::Local(g.witness)))
                    .chain(g.dicts.iter().map(|(_, d)| Arg::Borrow(d.clone())))
                    .chain(desc.map(Arg::Borrow))
            })
            .collect()
    }

    /// The number of words that the generics of `params` take in a data object: a witness, a
    /// dictionary for each bound, and a descriptor for each whose descriptor travels with them.
    pub(crate) fn generic_words<'p>(
        &self,
        params: impl Iterator<Item = (&'p Ty, &'p [Item])>,
    ) -> usize {
        params
            .map(|(ty, traits)| 1 + traits.len() + usize::from(self.carries(ty, traits)))
            .sum()
    }

    /// Gives `ty` a generic whose witness and dictionaries are fields of a data object, from
    /// field `*next` on, of `len` fields, one dictionary for each of `traits`.
    pub(crate) fn generic_from(
        &mut self,
        ty: Ty,
        traits: &[Item],
        env: Local,
        len: u32,
        next: &mut u32,
    ) {
        let witness = self.borrowed_field(env, len, *next, Repr::Scalar);
        *next += 1;
        let dicts = traits
            .iter()
            .map(|t| {
                let d = self.borrowed_field(env, len, *next, Repr::Heap);
                *next += 1;
                (t.clone(), Operand::Local(d))
            })
            .collect();
        let desc = self.carries(&ty, traits).then(|| {
            let d = self.borrowed_field(env, len, *next, Repr::Heap);
            *next += 1;
            Operand::Local(d)
        });
        self.push_generic(ty, witness, dicts, None);
        self.set_last_descriptor(desc);
    }

    /// Gives `Self` a witness of a known value, and the dictionary `dict` of `t`, held in one
    /// word: the methods of a dictionary take it so.
    pub(crate) fn self_generic(&mut self, witness: Operand, dict: Operand, t: &Item) {
        let witness = self.b.define(Repr::Scalar, Rvalue::Use(witness));
        self.push_generic(
            Ty::SelfTy,
            witness,
            vec![(t.clone(), dict)],
            Some(&crate::Held::Word),
        );
    }
}

/// The program's entry: it runs `main`, shows the error that escapes it, if one does
/// (program.exit-statuses), and releases the values of the program's constants. A `main` whose
/// error type has an error panics as soon as it is called (program.meeting-the-error-type), so
/// nothing is shown.
fn main(cx: &Cx<'_>) -> Function {
    let mut l = Lower::new(cx, FnRef::Main, true);
    load_libraries(cx, &mut l);
    l.err = Conv::of(Ty::str());
    let main_item = Item {
        home: Name::from("main"),
        name: Name::from("main"),
    };
    let decls = cx.decls();
    let sig = decls.function(&main_item);
    // A `main` whose row holds an effect takes the memory for an error it never raises.
    let slot = sig
        .as_ref()
        .is_some_and(|s| crate::lower::raises::raises_to_slot(s));
    let row = sig
        .filter(|s| {
            !s.row
                .raise
                .as_deref()
                .is_some_and(stilt_types::hir_holds_error)
        })
        .map_or(Row::EMPTY, |s| Row::from_hir(&s.row, None));
    let loc = Operand::Local(l.loc);
    let next = l.b.new_block();
    let raised = row
        .raise
        .as_deref()
        .map(|e| (l.temps(e), l.b.new_block(), e.clone()));
    let dest = vec![l.b.temp(Repr::Scalar)];
    let mut args = vec![Arg::Borrow(loc.clone())];
    if slot {
        args.push(Arg::Borrow(Operand::word(0)));
    }
    l.b.terminate(Terminator::Call {
        callee: Callee::Direct(FnRef::Function(main_item)),
        args,
        dest,
        next,
        raised: raised.as_ref().map(|(e, b, _)| (e.clone(), *b)),
    });
    if let Some((error, block, ty)) = raised {
        l.b.switch_to(block);
        let words = crate::lower::words::operands(&error);
        let shown = l.trait_call("Show", "show", &ty, vec![words], loc);
        l.b.emit(Stmt::ReleaseConstants);
        l.b.terminate(Terminator::Raise(vec![shown]));
    }
    l.b.switch_to(next);
    l.b.emit(Stmt::ReleaseConstants);
    l.b.terminate(Terminator::Return(vec![Operand::word(0)]));
    let _ = prelude_item("Show");
    l.into_function()
}
