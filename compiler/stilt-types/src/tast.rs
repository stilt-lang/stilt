//! The bodies after type checking, which the later phases read.
//!
//! Every expression carries its type, every literal its numeric type, and every call its
//! target and type arguments. Trait methods are called through the type that implements them,
//! as dictionary passing would. Types are frozen: no variable in them is solved, and every row
//! holds what inference found it holds. A read through an `Option` is elaborated as the
//! `match` that types.fields-through-option defines.

pub mod retype;
pub mod walk;

use stilt_hir::hir::{
    BinaryOp, CodeForm, GenericId, Item, ListRest, LocalId, Mode, Name, Place, QuoteTok, UnaryOp,
};
use stilt_syntax::TextRange;

use crate::ty::{Row, RowParam, Ty};

/// A function that a program can call by name.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Callee {
    /// A function of a module.
    Function(Item),
    /// A function of an inherent impl of a type constructor.
    Member(Item, Name),
    /// A method of a trait, of the impl for a type.
    TraitMethod(Item, Name, Ty),
    /// An operation of an effect, which a call performs on the nearest handler of its effect
    /// (handlers.performing-operation). Its type arguments are the effect's.
    Operation(Item, Name),
}

/// What a signature pairs a row variable with: an error type (effects.paired-row-variables), or an
/// effect with its type arguments (handlers.with-pairing).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Label {
    /// An error type.
    Raise(Ty),
    /// An effect, with its type arguments.
    Effect(Item, Vec<Ty>),
}

impl Label {
    /// The label with each of its types replaced by `f`'s.
    #[must_use]
    pub fn map(&self, f: impl Fn(&Ty) -> Ty) -> Self {
        match self {
            Self::Raise(t) => Self::Raise(f(t)),
            Self::Effect(e, args) => Self::Effect(e.clone(), args.iter().map(f).collect()),
        }
    }
}

/// A handler literal (handlers.handler-literals): its effect, whether it takes control, written `->
/// R` (handlers.resuming), and its operations, each a closure of the operation's parameters, in the
/// order written.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HandlerExpr {
    /// Its effect.
    pub effect: Item,
    /// Whether it takes control, written `-> R`.
    pub control: bool,
    /// Each operation's name and closure, in the order written.
    pub ops: Vec<(Name, Expr)>,
}

/// An expression, with its type.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Expr {
    /// What it is.
    pub kind: ExprKind,
    /// Its type.
    pub ty: Ty,
    /// Its span.
    pub at: TextRange,
}

impl Expr {
    /// The value that the expression instantiates, if it instantiates a value of a polymorphic
    /// function type, and otherwise the expression itself (polymorphism.instantiation).
    #[must_use]
    pub fn instantiated(&self) -> &Self {
        match &self.kind {
            ExprKind::Instantiate(value, _) => value.instantiated(),
            _ => self,
        }
    }

    /// Whether the expression is a projection's call, or a field, an element or an index of one,
    /// which is a place (projections.call-is-place). An expression with an error may be anything
    /// (errors.error-type), and is taken to be one.
    #[must_use]
    pub fn rooted_in_projection(&self) -> bool {
        match &self.kind {
            ExprKind::Project(..) | ExprKind::Error => true,
            ExprKind::Field(base, _) | ExprKind::TupleField(base, _) | ExprKind::Index(base, _) => {
                base.rooted_in_projection()
            }
            _ => false,
        }
    }
}

/// What a typed expression is.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExprKind {
    /// A literal as written, of the numeric type `ty`.
    Int(String),
    /// A float literal, as written.
    Float(String),
    /// A string, its escapes resolved.
    Str(String),
    /// An interpolated string's parts, in order.
    Interpolated(Vec<Segment>),
    /// `true` or `false`.
    Bool(bool),
    /// A local variable.
    Local(LocalId),
    /// A constant of a module.
    Constant(Item),
    /// A value parameter in scope, a value of its type (generics.value-parameters-in-body).
    ValueParam(GenericId),
    /// `T.shape()` or `T.name()`, of the type `T` (meta.shape-and-name).
    Reflect(Reflection, Ty),
    /// A bound test, of type `bool`: the type tested, and each trait with its arguments, none
    /// for a trait with parameters written without them (meta.bound-tests).
    Bound(Ty, Vec<(Item, Vec<Ty>)>),
    /// `Type.NAME`, with the type's arguments.
    MemberConstant(Item, Name, Vec<Ty>),
    /// A function as a value, with its type arguments: the impl's, then its own.
    Callee(Callee, Vec<Ty>),
    /// A variant with a payload, as a value.
    Constructor(Item, Vec<Ty>),
    /// A variant applied.
    Construct(Item, Vec<Ty>, Vec<Expr>),
    /// A record literal, with its fields in the order they are written.
    Record(Item, Vec<Ty>, Vec<(Name, Expr)>),
    /// An update: the base, then the fields written, in order, which replace the base's
    /// (records.update). Its type is the base's.
    Update(Box<Expr>, Vec<(Name, Expr)>),
    /// A spread among a tuple's, a list's or a call's elements (variadics.spread-expressions).
    Spread(Box<SpreadExpr>),
    /// A tuple's elements.
    Tuple(Vec<Expr>),
    /// A list's elements.
    List(Vec<Expr>),
    /// A record's field.
    Field(Box<Expr>, Name),
    /// A tuple's element, by its index.
    TupleField(Box<Expr>, usize),
    /// A call by name, with the row it performs. A method's receiver is its first argument.
    Call(Callee, Vec<Ty>, Vec<Arg>, Row),
    /// The call of a projection, which is a place of its result type (projections.call-is-place).
    Project(Callee, Vec<Ty>, Vec<Arg>, Row),
    /// A call of a function value, with its arguments.
    CallValue(Box<Expr>, Vec<Arg>),
    /// A value of a polymorphic function type at type arguments, one for each of its type
    /// parameters, as a call or a monomorphic function type uses it (polymorphism.instantiation).
    Instantiate(Box<Expr>, Vec<Ty>),
    /// Of a list or a map, as the first's type says.
    Index(Box<Expr>, Box<Expr>),
    /// A prefix operator and its operand.
    Unary(UnaryOp, Box<Expr>),
    /// A binary operator and its operands.
    Binary(BinaryOp, Box<Expr>, Box<Expr>),
    /// `a else b`.
    Else(Box<Expr>, Box<Expr>),
    /// `try e`, with its `catch` if it has one.
    Try(Box<Expr>, Option<Catch>),
    /// `raise e`.
    Raise(Box<Expr>),
    /// `return`, with its value if it is written.
    Return(Option<Box<Expr>>),
    /// `break`.
    Break,
    /// `continue`.
    Continue,
    /// A closure literal: the patterns of its parameters, and its body.
    Closure(Vec<Pat>, Box<Expr>),
    /// A block.
    Block(Block),
    /// `if c { … }`: the condition, the block, and what follows `else`.
    If(Box<Expr>, Block, Option<Box<Expr>>),
    /// `if let P = e { … }`, matched as a `match` arm without a guard (expressions.if-let).
    IfLet(Pat, Box<Expr>, Block, Option<Box<Expr>>),
    /// `match e { … }`, with its arms.
    Match(Box<Expr>, Vec<Arm>),
    /// `loop { … }`.
    Loop(Block),
    /// `while c { … }`.
    While(Box<Expr>, Block),
    /// `for p in e { … }`.
    For(Pat, Box<Iterable>, Block),
    /// A handler literal (handlers.handler-literals).
    Handler(Box<HandlerExpr>),
    /// `with h { … }`: the handler, the effect it handles with its type arguments, and the
    /// block it runs installed in (handlers.with). `with a, b { … }` is `with a { with b { …
    /// } }`.
    With(Box<Expr>, Item, Vec<Ty>, Block),
    /// `resume(v)`, of type the handler's `R` (handlers.resuming).
    Resume(Option<Box<Expr>>),
    /// `when a, b { … }` (shared.when): each handle, a `Shared<T>`, with the local of type
    /// `T` that stands for its value's place in the block, and the block.
    When(Vec<(Expr, LocalId)>, Block),
    /// A quote (macros.quote), which evaluates its splices and makes code of its form.
    Quote(Box<Quote>),
    /// `?`, a hole, or the body of a function written `= ?`.
    Hole,
    /// An expression with an error. The program never runs.
    Error,
}

/// A quote (macros.quote, macros.splices and macros.quote-hygiene): the module where its names
/// resolve, its form, its tokens, its text as a note shows it, and its splices, in the order
/// written.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Quote {
    /// The module where its names resolve.
    pub home: Name,
    /// The form of the code it makes.
    pub form: CodeForm,
    /// Its tokens, in order.
    pub tokens: Vec<QuoteTok>,
    /// Its splices, in the order written.
    pub splices: Vec<Splice>,
    /// Its text, as a note shows it.
    pub written: String,
}

/// A splice of a quote: where it stands, whether it is a spread, its span, and its value.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Splice {
    /// Where it stands.
    pub place: Place,
    /// Whether it is a spread, `$..x`.
    pub spread: bool,
    /// Its span, from its `$`.
    pub at: TextRange,
    /// Its value.
    pub value: Expr,
}

/// What reflection reads of a type (meta.shape-and-name): its shape, a `meta.Shape<T>`, or its
/// name, as a diagnostic writes it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Reflection {
    /// `T.shape()`.
    Shape,
    /// `T.name()`.
    Name,
}

/// A spread `..e`: `body`, evaluated once for each element of `pack`, with each of the pack
/// tuples `mapped` standing for its element there, and `of` standing in their types for the
/// element's type (variadics.spread-expressions).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpreadExpr {
    /// The expression evaluated for each element.
    pub body: Expr,
    /// The pack tuples that stand for their element in it.
    pub mapped: Vec<LocalId>,
    /// The pack it spreads.
    pub pack: Ty,
    /// The parameter that stands for the element's type in it.
    pub of: GenericId,
}

/// A part of an interpolated string.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Segment {
    /// Text, its escapes resolved.
    Text(String),
    /// An interpolated expression, with its format spec.
    Splice(Box<Expr>, Option<String>),
}

/// An argument of a call.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Arg {
    /// Its parameter's, or for a receiver, its `self`'s.
    pub mode: Mode,
    /// Its expression.
    pub value: Expr,
    /// Whether its parameter, of a function or method that the call names, is non-escaping,
    /// so that it passes the argument's effects through (effects.non-escaping-parameters).
    pub passes: bool,
    /// Whether its parameter is declared with a function type and escapes, so that it keeps the
    /// closure the argument gives (effects.escaping-parameters). A parameter of a type
    /// parameter keeps none: a view the argument is or captures is the call's result's source
    /// (views.across-calls).
    pub kept: bool,
}

/// The `catch` of a `try`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Catch {
    /// The type `E` that the arms handle (effects.catch).
    pub error: Ty,
    /// Its arms, in order.
    pub arms: Vec<Arm>,
}

impl Catch {
    /// Whether the `catch` handles `Never`, because its operand raises nothing (effects.catch).
    #[must_use]
    pub fn handles_never(&self) -> bool {
        self.error == Ty::never()
    }
}

/// An arm of a `match` or of a `catch`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Arm {
    /// Its pattern.
    pub pattern: Pat,
    /// Its `if` guard.
    pub guard: Option<Box<Expr>>,
    /// Whether the arm gives a reason (effects.catch-alls-need-reason).
    pub because: bool,
    /// The expression after `=>`.
    pub body: Expr,
}

/// What a `for` loop runs over.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Iterable {
    /// A value whose elements it takes.
    Iter(Box<Expr>),
    /// A range, and whether it includes its end.
    Range(Box<Expr>, Box<Expr>, bool),
}

/// A block's statements, in order.
pub type Block = Vec<Stmt>;

/// A statement.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Stmt {
    /// What it is.
    pub kind: StmtKind,
    /// Its span.
    pub at: TextRange,
}

/// What a statement is.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StmtKind {
    /// `let p = e`.
    Let(Binding),
    /// `var p = e`.
    Var(Binding),
    /// An assignment, with its compound operator.
    Assign(Option<BinaryOp>, Expr, Expr),
    /// `assert e`.
    Assert(Expr),
    /// `yield e`: a place, or an expression of a view type that a temporary holds
    /// (projections.yield).
    Yield(Expr),
    /// An expression, as a statement.
    Expr(Expr),
}

/// A `let` or a `var`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Binding {
    /// The pattern it binds.
    pub pattern: Pat,
    /// The value it binds.
    pub value: Expr,
    /// The `else` branch of a let-else (patterns.let-else).
    pub otherwise: Option<Box<Expr>>,
}

/// A pattern, with its type.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Pat {
    /// What it is.
    pub kind: PatKind,
    /// The type of the values it matches.
    pub ty: Ty,
    /// Its span.
    pub at: TextRange,
}

/// What a typed pattern is.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PatKind {
    /// `_`.
    Wild,
    /// A name, which binds this local.
    Bind(LocalId),
    /// An integer, with its `-` if it has one.
    Int(String),
    /// A string, its escapes resolved.
    Str(String),
    /// `true` or `false`.
    Bool(bool),
    /// A tuple's elements.
    Tuple(Vec<Pat>),
    /// A constant, which matches values equal to it.
    Const(Box<Expr>),
    /// A variant, with its payload's patterns.
    Variant(Item, Vec<Pat>),
    /// The fields matched, in the order they are written.
    Record(Vec<(Name, Pat)>),
    /// A list's elements, and what follows them.
    List(Vec<Pat>, ListRest),
    /// Two or more alternatives, which bind the same variables.
    Or(Vec<Pat>),
    /// A pattern with an error.
    Error,
}

/// What a body is defined by.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Definition<T> {
    /// A native item of the standard library (declarations.native-items).
    Native,
    /// Code.
    Code(T),
    /// Code with an error, which the later phases skip (errors.broken-parts). A program with one
    /// never runs.
    Broken,
}

/// The code of a body: a function's or a test's block, or a constant's value or a doc
/// example's claim.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Code {
    /// A function's or a test's block.
    Block(Block),
    /// A constant's value or a doc example's claim.
    Expr(Box<Expr>),
}

/// A body after type checking.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypedBody {
    /// The names of its locals: those of the HIR's body, then those that elaboration adds,
    /// such as the parameter of a key path's closure.
    pub locals: Vec<Name>,
    /// A function's parameters, its receiver's first for a method, with their modes. Other
    /// bodies have none.
    pub params: Vec<(Mode, LocalId)>,
    /// The row variables, written and implicit, that its function's signature pairs with an
    /// error type, with that type (effects.paired-row-variables).
    pub pairs: Vec<(RowParam, Label)>,
    /// A function's parameters that pass their arguments' effects through
    /// (effects.non-escaping-parameters).
    pub passing: Vec<LocalId>,
    /// For each use of a function whose signature pairs a row variable with an error type, the
    /// row and the error type that the use gives them (effects.passing-to-paired-variables).
    pub passed: Vec<(TextRange, Row, Label)>,
    /// What a test's body, a doc example or a property performs. Other bodies have none.
    pub tested: Option<Tested>,
    /// Each staging annotation, as its `comptime` with the blanks after it, and the `if`,
    /// `match` or `for` it marks: the body holds the form itself, which is what the annotation
    /// means (meta.staging-annotations and meta.erasure).
    pub staged: Vec<(TextRange, TextRange)>,
    /// Each method's name that its package's edition renamed, with the name it has there,
    /// which `stilt migrate` writes (editions.renames and editions.migrate).
    pub renamed: Vec<(TextRange, &'static str)>,
    /// Its code.
    pub code: Definition<Code>,
}

/// What a test's body, a doc example or a property performs, as inference finds it
/// (program.running-tests and program.doc-examples; tests.property-io): whether it may do `io`,
/// which keeps its result from being cached, and the error type it raises, `Never` when it raises
/// none.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Tested {
    /// What it is.
    pub kind: TestKind,
    /// Whether it may do `io`.
    pub io: bool,
    /// The error type it raises.
    pub error: Ty,
}

/// What a tested body is: a test's, of type `()`; a doc example, of type `bool`; or a property, a
/// closure whose cases `stilt test` generates (tests.property-form and tests.property-cases),
/// which performs no `io` and raises nothing, while its closure may raise.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TestKind {
    /// A test's body.
    Test,
    /// A doc example.
    Example,
    /// A property.
    Property,
}
