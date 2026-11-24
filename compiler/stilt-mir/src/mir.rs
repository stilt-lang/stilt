//! The MIR: each function as a control-flow graph of blocks over word-sized locals.
//!
//! A value is one word or several: lowering holds a value of a record, a tuple or a variant
//! that isn't recursive in one local per word of its layout (goal inline-values), and
//! passes, returns and raises it as those words. A local's [`Repr`] says whether it holds a heap
//! word, whose references are counted, a scalar, or a value of a type parameter, whose witness
//! tells at run time. Lowering writes no reference counting: `stilt-rc` inserts the [`Stmt::Dup`]
//! and [`Stmt::Drop`] statements from ownership, which this module defines:
//!
//! - a local owns its value, except a parameter that it borrows ([`ParamMode::Borrowed`]);
//! - [`Rvalue::Use`], [`Arg::Own`], [`Rvalue::Alloc`]'s fields, [`Stmt::Store`]'s value,
//!   [`Terminator::Return`] and [`Terminator::Raise`] consume their operand;
//! - every other operand is borrowed for the statement that reads it;
//! - [`Rvalue::Field`], [`Rvalue::Load`] and the runtime calls that [`Runtime::borrows`] names
//!   give a word without a reference of its own, which the result's local must count before
//!   anything can release its source.

use std::sync::Arc;

use serde::{Deserialize, Serialize};

use crate::FnRef;

mod debug;
mod elements;
mod prims;
mod runtime;
mod terminators;
mod words;

pub use debug::{Shown, ShownElements, ShownKind};
pub use elements::{Element, Elements, MEMORY_WORDS, Table};
pub use prims::{NumKind, Prim};
pub use runtime::{Effects, Runtime, Shared, Views};
pub use terminators::{Arg, Callee, Terminator};
pub use words::{Heapness, Repr, offsets};

/// A local of a function, by its place in [`Function::locals`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct Local(pub u32);

/// A block of a function, by its place in [`Function::blocks`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct BlockId(pub u32);

/// How a parameter is passed. Lowering borrows every `let` parameter, and `stilt-rc` gives a
/// function the ones it consumes (values.passing-values and values.consumed-parameters).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ParamMode {
    /// A `let` parameter that the function doesn't consume, and every hidden one: the caller
    /// keeps ownership.
    Borrowed,
    /// A `let` parameter that the function consumes: the callee owns the word.
    Owned,
    /// An `inout` parameter: a pointer to the caller's slot, whose word the callee may replace.
    Ref,
}

/// A local's facts.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
// Each flag is a fact of its own about the local, which a different pass reads; no two of them
// make one state.
#[allow(clippy::struct_excessive_bools)]
pub struct LocalDecl {
    /// For a [`ParamMode::Ref`] parameter, what its slot holds.
    pub repr: Repr,
    /// Whether the local lives in memory, because a pointer to it is taken.
    pub slot: bool,
    /// Whether its slot follows the slot of the local before it, as the words of one value
    /// do, so that a pointer to the first word reaches every word of the value.
    pub grouped: bool,
    /// Whether the local borrows its value: it is assigned once, from a source that outlives
    /// it and owns the value, such as a closure's captured variable read from the closure.
    pub borrowed: bool,
    /// Whether it holds a word of a `var` binding of the source, which never stands for the value
    /// it is bound to: rebinding a parameter with `var` consumes it (values.consumed-parameters).
    pub var: bool,
    /// The name it has in the source, for reading the MIR and for debuggers.
    pub name: Option<stilt_hir::hir::Name>,
    /// How a debugger shows it, for a local the source names.
    pub shown: Option<Shown>,
}

/// A parameter of a function.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Param {
    /// The local that holds it.
    pub local: Local,
    /// How it is passed.
    pub mode: ParamMode,
}

/// A function: its parameters in the order of the calling convention, its locals and its
/// blocks, the first of which is its entry.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Function {
    /// The function.
    pub name: FnRef,
    /// Its parameters, in the order of the calling convention.
    pub params: Vec<Param>,
    /// The number of its first parameters that a release build specializes it for
    /// (builds.specialization): the location, then what stands for its type and value arguments,
    /// the witnesses, dictionaries, value parameters and descriptors, or for the code of an object,
    /// a closure or a dictionary, the object.
    pub hidden: u32,
    /// The number of words the function returns: those of its result's layout or of its
    /// error's, whichever has more.
    pub results: u32,
    /// Its locals, by [`Local`].
    pub locals: Vec<LocalDecl>,
    /// Its blocks, by [`BlockId`], the entry first.
    pub blocks: Vec<Block>,
    /// Whether lowering met the error type, which only a program with errors has
    /// (errors.error-type): how its values are held is then unknown, so the function can't run.
    pub broken: bool,
}

impl Function {
    /// The function with no more room in its vectors than they hold, as the database and the
    /// engine keep it (goal bounded-cache).
    #[must_use]
    pub fn fitted(mut self) -> Self {
        stilt_hir::hir::fit(&mut self.params);
        stilt_hir::hir::fit(&mut self.locals);
        stilt_hir::hir::fit(&mut self.blocks);
        for b in &mut self.blocks {
            stilt_hir::hir::fit(&mut b.stmts);
        }
        self
    }
}

/// A block: statements, then a terminator.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Block {
    /// Its statements, in order.
    pub stmts: Vec<Stmt>,
    /// Where control goes after them.
    pub term: Terminator,
}

/// The tag of the dictionary of the structural `Ord` of a signed integer type, whose keys the
/// runtime compares as signed integers; a dictionary of `Ord` of an unsigned integer type has
/// [`UNSIGNED_ORDER`]. A dictionary of the structural `Eq` or `Hash` of an integer type or
/// `bool` has [`WORD_KEYS`], and one of `str` [`STR_KEYS`], whose keys a map hashes and compares
/// itself, and every other dictionary 0. `stilt_runtime::layout` gives the same tags, which
/// `stilt-codegen-clif`'s tests check.
pub const SIGNED_ORDER: u16 = 1;
/// The tag of the dictionary of the structural `Ord` of an unsigned integer type.
pub const UNSIGNED_ORDER: u16 = 2;
/// The tag of the dictionaries of the structural `Eq` and `Hash` of an integer type or `bool`.
pub const WORD_KEYS: u16 = 3;
/// The tag of the dictionaries of the structural `Eq` and `Hash` of `str`.
pub const STR_KEYS: u16 = 4;

/// The tag of a box, the data object that holds the words of a value where its type's layout
/// can't, which no variant's index is: the runtime counts the boxes a program makes
/// (goal inline-values). `stilt_runtime::layout` gives the same tag.
pub const BOX: u16 = u16::MAX;

/// The most fields whose heap bits a data object's layout word holds itself; a larger object has
/// mask words after its fields. `stilt_runtime::layout` gives the same.
pub const INLINE_FIELDS: usize = 30;

/// The layout word of a data object of `len` fields whose heap words are the bits of `mask`, the
/// low half of its header's second word: the mask with a bit set above it at `len`, or for an
/// object of more than [`INLINE_FIELDS`] fields, its length with the highest bit set, as
/// `stilt_runtime::layout::data_layout` makes it, which `stilt-codegen-clif`'s tests check.
#[must_use]
// The bits kept are those below 31, which a small length's bit and mask take.
#[allow(clippy::cast_possible_truncation)]
pub const fn data_layout(len: usize, mask: u64) -> u32 {
    if len <= INLINE_FIELDS {
        (1 << len | mask & ((1 << len) - 1)) as u32
    } else {
        1 << 31 | len as u32
    }
}

/// What memory that [`Runtime::Reclaim`] kept holds already of the object built in it
/// ([`Rvalue::AllocIn`]), when it kept it: its header, when the object it held was of the same
/// variant, of the same layout, and the words of its fields that the bits of `words` name, which
/// hold the values the new object's fields have there, as the fields read from the old one that
/// the new one holds in the same places do.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Kept {
    /// Whether the header is the new object's.
    pub header: bool,
    /// The words that hold their values.
    pub words: u64,
}

/// The variant of a declared type that a data object holds: its tag, and its layout word
/// ([`data_layout`]) when the heapness of each of its words is fixed, not a type parameter's.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Variant {
    /// The object's tag.
    pub tag: u16,
    /// Its layout word, if it is the same whatever the type arguments.
    pub layout: Option<u32>,
}

/// The word that tells [`Runtime::Reclaim`] what the object it releases is known to be: 0 when
/// nothing is known, and otherwise its highest bit set, the variant's tag from bit 32, and its
/// layout word in the low half, when it is fixed, which bit 48 tells.
#[must_use]
pub fn known_object(v: Option<Variant>) -> u64 {
    match v {
        None => 0,
        Some(Variant { tag, layout }) => {
            1 << 63 | u64::from(tag) << 32 | layout.map_or(0, |l| 1 << 48 | u64::from(l))
        }
    }
}

/// The variant that a word of [`known_object`] tells.
#[must_use]
// Each part is taken from its own bits of the word.
#[allow(clippy::cast_possible_truncation)]
pub fn known_variant(word: u64) -> Option<Variant> {
    (word >> 63 == 1).then(|| Variant {
        tag: (word >> 32) as u16,
        layout: (word >> 48 & 1 == 1).then_some(word as u32),
    })
}

/// A constant, which costs nothing to make. A string or a data object is immortal static data.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Const {
    /// A scalar, or an immediate.
    Word(u64),
    /// A string literal, static data.
    Str(Arc<str>),
    /// A data object, each field with whether its type is one of heap words.
    Data(u16, Vec<(Const, bool)>),
    /// The address of a function's code.
    Code(FnRef),
}

/// What a statement reads: a local or a constant.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Operand {
    /// A local.
    Local(Local),
    /// A constant.
    Const(Const),
}

impl Operand {
    /// The constant word `w`.
    #[must_use]
    pub const fn word(w: u64) -> Self {
        Operand::Const(Const::Word(w))
    }

    /// The local, if the operand is one.
    #[must_use]
    pub fn local(&self) -> Option<Local> {
        match self {
            Operand::Local(l) => Some(*l),
            Operand::Const(_) => None,
        }
    }
}

/// What an assignment computes.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Rvalue {
    /// The operand's value.
    Use(Operand),
    /// A primitive operation on its operands, with its location.
    Prim(Prim, Vec<Operand>, Operand),
    /// A new data object with this tag and these fields, which it consumes, each field's words
    /// after the last's.
    Alloc(u16, Vec<(Operand, Heapness)>),
    /// [`Rvalue::Alloc`], in the memory that the first operand holds unless it is 0: memory
    /// that [`Runtime::Reclaim`] kept for an object of as many words, of which the last field
    /// tells what it holds already.
    AllocIn(Operand, u16, Vec<(Operand, Heapness)>, Kept),
    /// The value at word `index` of a data object of `len` words, borrowed: one word, or the
    /// words of an array held in memory, for a local of its representation.
    Field {
        /// The data object.
        base: Operand,
        /// Its number of words.
        len: u32,
        /// The word read.
        index: u32,
        /// What the object is, when it holds a variant of a declared type: what a release
        /// that keeps its memory needn't test, and a value built there needn't write again.
        variant: Option<Variant>,
    },
    /// A variant's index among its type's variants.
    Tag(Operand),
    /// The word a pointer points to, borrowed, or the words of an array held in memory, for a
    /// local of its representation.
    Load(Operand),
    /// A pointer to a local that lives in memory.
    SlotOf(Local),
    /// A pointer `words` words past a pointer: to a later word of a value in memory.
    Offset(Operand, u32),
    /// A pointer to field `index` of the data object of `len` fields that a slot holds, which
    /// is made unique first.
    FieldSlot {
        /// The slot.
        slot: Operand,
        /// The data object's number of fields.
        len: u32,
        /// The field pointed to.
        index: u32,
    },
    /// A call of a runtime function, with its arguments.
    Runtime(Runtime, Vec<Operand>),
    /// Value `k` of a constant's value, of these words one after the other, an array held in
    /// memory taking its words, borrowed from where the program keeps
    /// it: computed by its code, with this location, where it is first used. Whether computing
    /// it can't panic is the last field, and then a read of it may move to where the function
    /// first could need it (declarations.constant-evaluation).
    Constant(FnRef, Operand, u32, Arc<[Repr]>, bool),
}

impl Rvalue {
    /// The operands the rvalue reads.
    #[must_use]
    pub fn operands(&self) -> Vec<&Operand> {
        match self {
            Rvalue::Use(o)
            | Rvalue::Tag(o)
            | Rvalue::Load(o)
            | Rvalue::Constant(_, o, ..)
            | Rvalue::Offset(o, _)
            | Rvalue::Field { base: o, .. }
            | Rvalue::FieldSlot { slot: o, .. } => vec![o],
            Rvalue::Prim(_, args, loc) => args.iter().chain([loc]).collect(),
            Rvalue::Runtime(_, args) => args.iter().collect(),
            Rvalue::Alloc(_, fields) => fields.iter().map(|(o, _)| o).collect(),
            Rvalue::AllocIn(memory, _, fields, _) => std::iter::once(memory)
                .chain(fields.iter().map(|(o, _)| o))
                .collect(),
            Rvalue::SlotOf(_) => Vec::new(),
        }
    }
}

/// A statement of a block.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Stmt {
    /// Assigns the rvalue's value to the local.
    Assign(Local, Rvalue),
    /// Writes a word into the slot a pointer points to, releasing the word it held, or for an
    /// array held in memory, its words.
    Store {
        /// The pointer to the slot.
        slot: Operand,
        /// The word written.
        value: Operand,
        /// What the slot holds.
        repr: Repr,
    },
    /// A runtime function called for its effect.
    Effect(Runtime, Vec<Operand>),
    /// Releases the values of the program's constants, which the program's entry does last.
    ReleaseConstants,
    /// Counts a reference more to the local's value.
    Dup(Local),
    /// Releases a reference to the local's value.
    Drop(Local),
    /// The code after this marker comes from the source at this location word, as
    /// `stilt_runtime::location` encodes it, until the next marker (goal debuggable-builds).
    At(u64),
    /// The place, at this location word, of what a profile counts (builds.profiles): the entry
    /// of a body, an arm of an `if` or a `match`, or the body of a loop, which a profiled run
    /// counts and a release build with a profile reads as a hint. Lowering marks them only for
    /// those builds (`crate::profiling`); every other pass treats the mark as `At` treats its
    /// location.
    Count(Counted, u64),
}

/// What a [`Stmt::Count`] counts. `stilt_runtime::profile` numbers them alike.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub enum Counted {
    /// A body's entry.
    Entry,
    /// An arm of an `if` or a `match`.
    Arm,
    /// A loop's body.
    Loop,
}

impl Counted {
    /// The number the runtime gives what it counts.
    #[must_use]
    pub fn number(self) -> u64 {
        match self {
            Counted::Entry => 0,
            Counted::Arm => 1,
            Counted::Loop => 2,
        }
    }
}

/// The mark of the location word of an operation whose check of an index, a list's slot or a
/// divisor verification proves can't fail (facts.proved-indexes, facts.proved-divisions,
/// facts.range-loops, facts.guards and facts.divisors), in its highest bit, which no file's index
/// reaches: a release build drops the check (builds.dropped-checks), and a debug build reads no
/// mark and keeps it. The runtime reads a location without its marks.
pub const PROVED_CHECK: u64 = 1 << 63;

/// The mark of the location word of an arithmetic operation, a shift or a signed division that
/// verification proves can't overflow (facts.proved-overflow).
pub const PROVED_OVERFLOW: u64 = 1 << 62;

/// The mark of the location word of a call of `List.pop` whose list the facts of the counted
/// MIR prove that nothing else references, which a release build pops where it is, checking
/// nothing of its count ([`crate::opt::in_place`]).
pub const UNIQUE_LIST: u64 = 1 << 61;

/// The line, counted from 1, of the location that a word of [`Stmt::At`] marks.
#[must_use]
pub fn line_of(word: u64) -> u32 {
    u32::try_from(word >> 20 & 0xff_ffff).unwrap_or(0)
}
