//! The functions of a compiled program, by what they are the code of, and where their bodies
//! are.

use std::collections::HashMap;
use std::sync::Arc;

use stilt_db::{Db, Program, SourceFile};
use stilt_hir::hir::{DeclKind, FnBody, Item, ItemHir, MemberKind, Name, TraitRef, Ty};
use stilt_hir::module_hir;

use crate::cases::test_bodies;
use crate::described::{Access, Described, Walk};
use serde::{Deserialize, Serialize};

mod display;
mod words;

pub use words::Word;

/// A type constructor that a structural impl is for (traits.structural-impls).
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub enum Shape {
    /// A named type constructor.
    Con(Item),
    /// The tuples of this many elements.
    Tuple(u32),
    /// A tuple that spreads a pack whose length is known at run time only.
    Pack,
}

/// An impl of a trait for a type constructor: one the program writes, or a structural one.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub enum ImplRef {
    /// One the program writes.
    Written {
        /// The trait.
        trait_item: Item,
        /// The type constructor it is for.
        owner: Item,
    },
    /// A structural one.
    Structural {
        /// The trait.
        trait_item: Item,
        /// The type constructor it is for.
        shape: Shape,
    },
}

/// How an instance holds the values of one of its type parameters (goal
/// inline-values): in one word, whose heapness the parameter's witness tells, as the
/// generic code does, or in the words of a layout of several; and for a parameter bounded by a
/// trait with methods of their own type parameters, also the impls its argument has.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub enum Held {
    /// In one word, whose heapness the parameter's witness tells.
    Word,
    /// In the words of a layout of several, of these classes.
    Words(Box<[Word]>),
    /// As this known type argument is held, with the impls of its constructor.
    Impl(Arc<Known>),
    /// A constructor parameter's, or a constructor trait's `Self`, instantiated with this type
    /// constructor: the instance is compiled for it, with every type that applies the
    /// parameter that constructor applied, so it takes no witness or dictionary for it.
    Con(Item),
    /// A pack's: the instance is compiled for its arity, each element held as
    /// its key says; or, for a pack whose length grows through polymorphic recursion, `None`,
    /// for code that takes its length, its elements' shapes and their dictionaries at run time.
    Pack(Option<Box<[Held]>>),
    /// A value parameter's of type `i64`, which may give an array its size, instantiated with
    /// this value: the instance is compiled for it, so that the arrays it holds have their
    /// layouts. It still takes the value as its hidden argument.
    Value(i128),
}

/// A type argument whose constructor the instance knows, so that it calls the methods of the
/// constructor's impls directly, compiled for the layouts of their own type arguments, which a
/// dictionary's entry can't be: held as `held` says, a [`Held::Word`] or [`Held::Words`], of
/// constructor `con`, whose arguments are held as `args` say. The constructor and its
/// arguments decide how it is held, so they alone are hashed and named.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct Known {
    /// How it is held: a [`Held::Word`] or [`Held::Words`].
    pub held: Held,
    /// Its type constructor.
    pub con: Item,
    /// How the constructor's arguments are held.
    pub args: Box<[Held]>,
}

impl std::hash::Hash for Known {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.con.hash(state);
        self.args.hash(state);
    }
}

impl Held {
    /// How a value is held, without the impls it has.
    #[must_use]
    pub fn layout(&self) -> &Held {
        match self {
            Held::Impl(known) => known.held.layout(),
            _ => self,
        }
    }

    /// The number of constructors a key knows.
    #[must_use]
    pub fn knows(&self) -> usize {
        match self {
            Held::Impl(known) => 1 + known.args.iter().map(Held::knows).sum::<usize>(),
            Held::Pack(Some(elements)) => elements.iter().map(Held::knows).sum::<usize>(),
            _ => 0,
        }
    }
}

/// A type whose values cross into code past the caps of instances and back out of it
/// (`crate::lower::bridge`), as the code that converts them knows it: its structure, down to
/// the type arguments that the code past the caps holds in one word, their box, and the types
/// that hold none, which both sides hold alike.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub enum Cross {
    /// A type that the code past the caps holds in its box: the box holds the words of the
    /// type inside, which other code holds as this structure says.
    Boxed(Box<Cross>),
    /// A type that holds no such argument, in the words of its layout, of these classes.
    Same(Box<[Word]>),
    /// A tuple type, by its elements.
    Tuple(Box<[Cross]>),
    /// A type constructor with its arguments.
    Con(Item, Box<[Cross]>),
    /// A function type: each parameter's, `inout` or not, its result's, and its error's.
    Fn(Box<[(bool, Cross)]>, Box<Cross>, Option<Box<Cross>>),
    /// A polymorphic function type: the bounds of each of its type parameters, and its function
    /// type, which names them as [`Cross::Rigid`].
    Poly(Box<[Box<[Item]>]>, Box<Cross>),
    /// The type parameter at this place among those of the polymorphic function types around
    /// it, the outermost's first, which a call of the function gives the witness of.
    Rigid(u32),
}

/// A function of a compiled program: a function with a body of the program or the standard
/// library, or one that the compiler makes.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub enum FnRef {
    /// A function of a module.
    Function(Item),
    /// A function of an inherent impl, by its type constructor and name.
    Member(Item, Name),
    /// A method of a trait impl, by its trait, type constructor and name.
    ImplMethod(Item, Item, Name),
    /// A default method of a trait, by its trait and name.
    DefaultMethod(Item, Name),
    /// The closure of a function's body, by its place among the body's closures.
    Closure(Box<FnRef>, u32),
    /// A method of a structural impl, by its trait, its name and the impl's constructor.
    Structural(Item, Name, Shape),
    /// Method `index` of a trait, as a dictionary of an impl holds it: it takes the impl's type
    /// arguments from the dictionary.
    Entry(Box<ImplRef>, u32),
    /// The code of a function used as a value, which takes the function's type arguments
    /// from the closure.
    Value(Box<FnRef>),
    /// The code of method `index` of a trait used as a value on a type parameter: it calls the
    /// method of the dictionary the closure holds.
    Method(Item, u32),
    /// The code of a variant with a payload used as a value.
    Constructor(Item),
    /// The code of a closure that a native calls, which takes its arguments, of this number, and
    /// gives its result in one word, a box of their words if they have several, and calls the
    /// closure it holds with them in the words that hold them where a type parameter stands.
    Lent(u32),
    /// The value of a constant, computed where it is first used.
    Const(Item),
    /// The value of a constant of an inherent impl, by its type constructor and name.
    MemberConst(Item, Name),
    /// The program's entry: it runs `main`, and shows the error that escapes it.
    Main,
    /// A test's body or a doc example, by its module and the index of its body there.
    Test(Name, u32),
    /// The entry of a test or doc example, which `stilt test` runs: it gives 1 when the test
    /// passes and 0 when it raises, or when the example is false (program.test-declarations and
    /// program.doc-examples).
    TestEntry(Name, u32),
    /// The entry of a property, which `stilt test` runs once for each run of its closure, on
    /// values it reads from a tape (tests.property-cases and tests.running-cases;
    /// `crate::synth::props`).
    PropEntry(Name, u32),
    /// The decoder of node `k` of the types of a property's parameters, which reads a value of
    /// its type from the tape.
    Decode(Name, u32, u32),
    /// An input of the REPL, by its number in the session: its body, which takes the session's
    /// bindings (repl.running-inputs; `crate::synth::input`).
    Input(u32),
    /// The entry of an input, which the REPL runs on the frame of the session's bindings.
    InputEntry(u32),
    /// The code of a generic function for type arguments of these layouts, one per generic
    /// it takes in the order of its hidden parameters, of which some has several words.
    Instance(Box<FnRef>, Box<[Held]>),
    /// Method `index` of a trait, as the dictionary of a type argument that crosses into code
    /// past the caps holds it: it takes a value of `Self` in its box, and calls the method of
    /// the argument's own dictionary on the value's words, held outside in these.
    Forward(Item, u32, Box<[Word]>),
    /// The conversion of a value of a recursive type into code past the caps, or out of it.
    Rebuild(Box<Cross>, bool),
    /// The code of a closure that converts the values that a closure it holds takes and gives,
    /// into code past the caps, or out of it.
    Adapt(Box<Cross>, bool),
    /// The code of a closure that gives the descriptor of a type, and of one that reads or
    /// makes its values, which hold the witness and the descriptor of each type parameter it
    /// holds.
    Describe(Box<Described>),
    /// The code of a closure that reads or makes values of a described type.
    Access(Box<Described>, Access),
    /// The method of a prelude trait that a shape dictionary of a descriptor's table holds,
    /// which walks the parts of any value of that shape (`crate::lower::meta::shaped`).
    Shaped(Item, Walk),
    /// A release build's instance of the code `g` for what stands for its type and value
    /// arguments, numbered among `g`'s instances (builds.specialization; `crate::special`).
    Specialized(Box<FnRef>, u32),
    /// A foreign function, which C gives (c.calls): its call takes the location, then
    /// each argument in its word, and gives its result in one word, which the back ends pass
    /// and take as C does.
    Foreign(Box<Foreign>),
}

/// A foreign function: its C symbol, and the C types of its parameters and of its result, none
/// for `()` (c.foreign-functions and c.types-c-takes).
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct Foreign {
    /// Its C symbol.
    pub name: String,
    /// The C types of its parameters.
    pub params: Vec<crate::CType>,
    /// The C type of its result, none for `()`.
    pub result: Option<crate::CType>,
}

impl FnRef {
    /// The name of the function's code, unique in the program.
    #[must_use]
    pub fn symbol(&self) -> String {
        self.to_string()
    }

    /// The function whose body holds the closure, through closures that closures hold, or the
    /// function itself: the one whose lowering gives its code.
    #[must_use]
    pub fn root(&self) -> &FnRef {
        match self {
            FnRef::Closure(parent, _) => parent.root(),
            _ => self,
        }
    }

    /// The function an instance is of, or the function itself.
    #[must_use]
    pub fn generic(&self) -> &FnRef {
        match self {
            FnRef::Instance(g, _) => g,
            _ => self,
        }
    }

    /// How an instance holds the values of each of its generics, or none for code that holds
    /// every one in a word.
    #[must_use]
    pub fn held(&self) -> &[Held] {
        match self {
            FnRef::Instance(_, held) => held,
            _ => &[],
        }
    }

    /// The code of `g` for generics held as `held` says: `g` itself when each is held in a
    /// word, and otherwise its instance.
    #[must_use]
    pub fn instance(g: FnRef, held: Vec<Held>) -> FnRef {
        if held.iter().all(|h| *h == Held::Word) {
            g
        } else {
            FnRef::Instance(Box::new(g), held.into())
        }
    }
}

/// Where a function's or a constant's code is.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Code {
    /// The body of this index of a file's module.
    Body(SourceFile, u32),
    /// A native item of the standard library (declarations.native-items).
    Native,
}

/// Where the code of every function and constant with a body is, the standard library's
/// included.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Bodies {
    /// The code of each, by the function.
    pub code: HashMap<FnRef, Code>,
}

fn fn_code(file: SourceFile, std: bool, body: Option<FnBody>) -> Option<Code> {
    match body? {
        FnBody::Hole(_) if std => Some(Code::Native),
        FnBody::Block(i) | FnBody::Hole(i) => Some(Code::Body(file, i.0)),
    }
}

/// Where the code of one function or constant is: the entry of [`bodies`] that lowering reads,
/// so that an edit that adds or removes an item lowers again only what names it.
// Salsa takes a query's key by value.
#[allow(clippy::needless_pass_by_value)]
#[salsa::tracked(returns(copy))]
pub fn code_of(db: &dyn Db, program: Program, f: FnRef) -> Option<Code> {
    bodies(db, program).code.get(f.generic()).copied()
}

/// The bodies of a program and of the standard library. Of two items with the same name, the
/// first is the one names refer to (errors.several-places).
#[salsa::tracked(returns(ref))]
pub fn bodies(db: &dyn Db, program: Program) -> Bodies {
    let mut bodies = Bodies::default();
    for &file in program.std(db).iter().chain(program.files(db)) {
        let module = module_hir(db, program, file);
        let mut add = |key: FnRef, code: Option<Code>| {
            if let Some(code) = code {
                bodies.code.entry(key).or_insert(code);
            }
        };
        for entry in &module.items {
            match entry {
                ItemHir::Use => {}
                ItemHir::Decl(d) => add_decl(file, module.std, module.name, &d.kind, &mut add),
                ItemHir::Impl(imp) => add_impl(file, module.std, imp, &mut add),
            }
        }
        // The standard library's tests are its own, which only `test --std` runs (std.examples),
        // and no other code names.
        for index in test_bodies(module) {
            add(
                FnRef::Test(module.name, index),
                Some(Code::Body(file, index)),
            );
        }
    }
    bodies
}

/// The hole that stands for each native item of the standard library, by the function it is:
/// the body whose facts the analyses read from the native's declaration (facts.native-allocation,
/// facts.capability-natives), which only the documentation of the library asks for (docs.std).
pub fn native_bodies(db: &dyn Db, program: Program) -> HashMap<FnRef, (SourceFile, u32)> {
    let code = &bodies(db, program).code;
    let mut natives = HashMap::new();
    for &file in program.std(db) {
        let module = module_hir(db, program, file);
        // Read as a program's, a native's hole is a body of its file.
        let mut add = |key: FnRef, hole: Option<Code>| {
            if let (Some(Code::Body(file, index)), Some(Code::Native)) = (hole, code.get(&key)) {
                natives.entry(key).or_insert((file, index));
            }
        };
        for entry in &module.items {
            match entry {
                ItemHir::Use => {}
                ItemHir::Decl(d) => add_decl(file, false, module.name, &d.kind, &mut add),
                ItemHir::Impl(imp) => add_impl(file, false, imp, &mut add),
            }
        }
    }
    natives
}

fn add_decl(
    file: SourceFile,
    std: bool,
    home: Name,
    kind: &DeclKind,
    add: &mut impl FnMut(FnRef, Option<Code>),
) {
    let item = |name: &Name| Item { home, name: *name };
    match kind {
        DeclKind::Fn(f) => add(FnRef::Function(item(&f.name)), fn_code(file, std, f.body)),
        DeclKind::Const(c) => add(
            FnRef::Const(item(&c.name)),
            Some(Code::Body(file, c.value.0)),
        ),
        // A trait's default constant is code of no arguments, as its default methods are
        // (traits.trait-constants).
        DeclKind::Trait(t) => {
            for m in &t.members {
                let key = FnRef::DefaultMethod(item(&t.name), *m.name());
                match &m.kind {
                    MemberKind::Fn(f) => add(key, fn_code(file, std, f.body)),
                    MemberKind::TraitConst(_, _, value) => {
                        add(key, value.map(|v| Code::Body(file, v.0)));
                    }
                    MemberKind::Const(_) => {}
                }
            }
        }
        DeclKind::Type(_) | DeclKind::Test(..) | DeclKind::Macro(_) | DeclKind::Effect(_) => {}
    }
}

fn add_impl(
    file: SourceFile,
    std: bool,
    imp: &stilt_hir::hir::Impl,
    add: &mut impl FnMut(FnRef, Option<Code>),
) {
    let Ty::Con(owner, _) = &imp.self_ty else {
        return;
    };
    let trait_item = match &imp.trait_ref {
        Some(TraitRef::Trait(t, _)) => Some(t.clone()),
        Some(TraitRef::Error) => return,
        None => None,
    };
    for m in &imp.members {
        let name = *m.name();
        let (key, code) = match (&m.kind, &trait_item) {
            (MemberKind::Fn(f), Some(t)) => (
                FnRef::ImplMethod(t.clone(), owner.clone(), name),
                fn_code(file, std, f.body),
            ),
            (MemberKind::Fn(f), None) => (
                FnRef::Member(owner.clone(), name),
                fn_code(file, std, f.body),
            ),
            // A trait impl's constant is the code of its trait's entry (traits.trait-constants).
            (MemberKind::Const(c), Some(t)) => (
                FnRef::ImplMethod(t.clone(), owner.clone(), name),
                Some(Code::Body(file, c.value.0)),
            ),
            (MemberKind::Const(c), None) => (
                FnRef::MemberConst(owner.clone(), name),
                Some(Code::Body(file, c.value.0)),
            ),
            (MemberKind::TraitConst(..), _) => continue,
        };
        add(key, code);
    }
}
