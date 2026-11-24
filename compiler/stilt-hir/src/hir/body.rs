//! Bodies, whose parts hold their positions for their diagnostics. Their patterns are in
//! [`super::patterns`].

use stilt_diag::{Diagnostic, Edit};
use stilt_syntax::{TextRange, TextSize};

use super::{GenericId, Ident, Item, Limit, Mode, Name, Pat, Ty, TypeRef};

/// The place of a body among its module's bodies.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BodyIndex(pub u32);

/// A local variable of a body, by its place in [`Body::locals`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LocalId(pub u32);

/// A local variable: a parameter, `self`, or a binding of a pattern.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Local {
    /// Its name.
    pub name: Name,
    /// Where it is bound.
    pub at: TextRange,
}

/// The code of a function, a constant's value, a test, a doc example or a property. Its positions are
/// relative to its start, which [`crate::ModuleResolution::body_starts`] gives, so that an
/// edit that only moves it leaves it unchanged.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Body {
    /// Its locals, by [`LocalId`].
    pub locals: Vec<Local>,
    /// A function's `self` and parameters, in order.
    pub params: Vec<LocalId>,
    /// Its code.
    pub value: BodyValue,
    /// Where the body as a whole is reported: at the name of its function or constant, the
    /// `test` of its test, or the claim of its doc example or property. The body starts there.
    pub at: TextRange,
    /// Whether name resolution reported an error in it, so that only type checking runs on
    /// it (errors.phases).
    pub has_errors: bool,
    /// A function's: where fixes edit its signature.
    pub signature: Option<SignatureSpans>,
    /// A function's: where its `without` names `panic` and `alloc` (declarations.limits), for the
    /// diagnostics that it rules out.
    pub limits: Vec<(Limit, TextRange)>,
    /// The E0211 that resolution holds back for type checking, each with its name: those of
    /// names that a pattern of the body also writes without a module, whose failure only type
    /// checking finds, so that the body reports one E0211 for the name, where it fails first
    /// (errors.unknown-names).
    pub held: Vec<(Name, Diagnostic)>,
    /// The errors of the analyses that resolution finds where the body writes a type: a view type
    /// where a value of it is stored, or a `View` of what can't be viewed (views.viewable-types and
    /// views.view-types), which the body reports with those of its analyses, when type checking
    /// finds no error in it (errors.phases).
    pub analysed: Vec<Diagnostic>,
    /// A function's: the bounds of its `where` clause on member types that a bound's argument
    /// fixes, each a trait with its arguments and where it is written, which the fixed type
    /// must meet (traits.where).
    pub fixed: Vec<(Ty, Item, Vec<Ty>, TextRange)>,
    /// The expansions of its macro uses, outermost first (macros.expansion).
    pub expansions: Vec<super::Expansion>,
    /// Its `unsafe` blocks, a closure literal's included, in the order they start
    /// (c.unsafe-and-foreign). The body lowers each to its block.
    pub unsafe_blocks: Vec<UnsafeBlock>,
}

/// An `unsafe because "reason" { … }` block (c.unsafe-because): its `unsafe`, the reason's text,
/// and the whole expression, which holds the operations that only such a block may hold.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UnsafeBlock {
    /// Its `unsafe`.
    pub at: TextRange,
    /// The reason's text.
    pub reason: String,
    /// The whole expression.
    pub whole: TextRange,
}

/// Where fixes edit a function's signature. Its positions, like the rest of the body's, are
/// relative to the body's start, the function's name, which every part they mark follows.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct SignatureSpans {
    /// The function's own type parameters and row variables, in order: each one's name, where
    /// a bound is added to it, after its name or its last bound, and whether it has bounds.
    pub generics: Vec<(Name, TextSize, bool)>,
    /// Where a list of generics is written when the function has none: after its name.
    pub generics_at: TextSize,
    /// Where the function's own row is written: after the parameters, or after the return type
    /// if there is one.
    pub row: RowSpans,
    /// For each parameter, its receiver's first, whose type is a function type: where a row is
    /// written in that type, as for the function's own row.
    pub params: Vec<Option<RowSpans>>,
    /// Where the function's block ends, after its closing brace: where the reads that last a
    /// binding's scope at the block's top end (views.reads-that-last).
    pub end: TextSize,
}

/// Where the row of a function or a function type is written.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct RowSpans {
    /// Where a row is written when there is none: after the return type, if there is one.
    pub row_at: TextSize,
    /// Where the return type starts, when it is a function type with no row, which a row written
    /// after it would go to (declarations.function-type-rows). It is then parenthesized first.
    pub wrap: Option<TextSize>,
    /// The row written: the span of its elements, and whether braces enclose them. Braces
    /// around no element have an empty span, before the closing brace.
    pub row: Option<(TextRange, bool)>,
}

impl RowSpans {
    /// The edits that write `effect` in the row, first in it or last. With no row, they write
    /// one after the return type, in parentheses if it would take the row instead.
    #[must_use]
    pub fn written(&self, effect: &str, first: bool) -> Vec<Edit> {
        match self.row {
            None => match self.wrap {
                Some(start) => vec![
                    Edit::insert(start, "("),
                    Edit::insert(self.row_at, format!(") / {effect}")),
                ],
                None => vec![Edit::insert(self.row_at, format!(" / {effect}"))],
            },
            Some((span, true)) if span.is_empty() => vec![Edit::insert(span.start(), effect)],
            Some((span, true)) if first => vec![Edit::insert(span.start(), format!("{effect}, "))],
            Some((span, true)) => vec![Edit::insert(span.end(), format!(", {effect}"))],
            Some((span, false)) if first => vec![
                Edit::insert(span.start(), format!("{{{effect}, ")),
                Edit::insert(span.end(), "}"),
            ],
            Some((span, false)) => vec![
                Edit::insert(span.start(), "{"),
                Edit::insert(span.end(), format!(", {effect}}}")),
            ],
        }
    }
}

/// What a body's code is.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BodyValue {
    /// The block of a function or a test.
    Block(Block),
    /// A constant's value, or a doc example's claim.
    Expr(Expr),
    /// A property's closure, and its text, which seeds its cases (tests.prop-lines and
    /// tests.seeds).
    Property(Expr, String),
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
    /// `yield e`, in a projection's body (projections.yield).
    Yield(Expr),
    /// An expression, as a statement.
    Expr(Expr),
}

/// A `let` or a `var`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Binding {
    /// The pattern it binds.
    pub pattern: Pat,
    /// Its written type.
    pub annotation: Option<Box<TypeRef>>,
    /// The value it binds.
    pub value: Expr,
}

/// An expression.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Expr {
    /// What it is.
    pub kind: ExprKind,
    /// Its span.
    pub at: TextRange,
}

/// What an expression is.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExprKind {
    /// An integer literal, as the digits of numbers.integer-literals give its value.
    Int(String),
    /// A float literal, as written.
    Float(String),
    /// A string, its escapes resolved.
    Str(String),
    /// An interpolated string's parts, in order.
    Interpolated(Vec<Segment>),
    /// `true` or `false`.
    Bool(bool),
    /// A local variable, `self` included.
    Local(LocalId),
    /// A function, called or named as a value.
    Func(Item),
    /// A constant.
    Const(Item),
    /// A variant, a value or a constructor.
    Variant(Item),
    /// A value parameter in scope, an immutable value of its type
    /// (generics.value-parameters-in-body).
    ValueParam(GenericId, Ty),
    /// `Type.f`, `Type.NAME` or `Trait.m`, which the type checker looks up
    /// (traits.associated-functions and traits.qualified-calls).
    Member(MemberOwner, Ident),
    /// The `.` that starts a key path.
    KeyRoot,
    /// `?`, a hole, or the body of a function written `= ?`.
    Hole,
    /// A tuple's elements.
    Tuple(Vec<Expr>),
    /// A list's elements.
    List(Vec<Expr>),
    /// `e.f`: a field, a tuple's element by its index, or a method.
    Field(Box<Expr>, Ident),
    /// A call, with its arguments.
    Call(Box<Expr>, Vec<Arg>),
    /// `e[i]`.
    Index(Box<Expr>, Box<Expr>),
    /// A record literal: its type and its fields.
    Struct(TypeRef, Vec<FieldInit>),
    /// An update, `Name { ..base, f: e }`, or `{ ..base, f: e }` without a type (records.update,
    /// ): the declared record, the base, and the fields written.
    Update(Option<TypeRef>, Box<Expr>, Vec<FieldInit>),
    /// A spread, `..e`, among a tuple's, a list's or a call's elements
    /// (variadics.spread-expressions).
    Spread(Box<Expr>),
    /// A prefix operator and its operand.
    Unary(UnaryOp, Box<Expr>),
    /// A binary operator and its operands.
    Binary(BinaryOp, Box<Expr>, Box<Expr>),
    /// `a else b`.
    Else(Box<Expr>, Box<Expr>),
    /// A `try`, with the arms of its `catch`.
    Try(Box<Expr>, Option<Vec<Arm>>),
    /// `raise e`.
    Raise(Box<Expr>),
    /// `return`, with its value if it is written.
    Return(Option<Box<Expr>>),
    /// `break`.
    Break,
    /// `continue`.
    Continue,
    /// A closure literal: its parameters and its body.
    Closure(Vec<ClosureParam>, Box<Expr>),
    /// A block.
    Block(Block),
    /// `if c { … }`: the condition, the block, and what follows `else`.
    If(Box<Expr>, Block, Option<Box<Expr>>),
    /// `if let P = e { … }`, whose pattern's variables are in scope in the first block only
    /// (expressions.if-let).
    IfLet(Box<Pat>, Box<Expr>, Block, Option<Box<Expr>>),
    /// `match e { … }`, with its arms.
    Match(Box<Expr>, Vec<Arm>),
    /// `loop { … }`.
    Loop(Block),
    /// `while c { … }`.
    While(Box<Expr>, Block),
    /// `for p in e { … }`.
    For(Box<Pat>, Box<Iterable>, Block),
    /// `Effect.op`, an operation of an effect, which a call performs
    /// (handlers.performing-operation).
    Perform(Item, Ident),
    /// A handler literal (handlers.handler-literals).
    Handler(Box<super::HandlerLit>),
    /// `with h₁, h₂ { … }` (handlers.with).
    With(Vec<Expr>, Block),
    /// `resume(v)`, or `resume()` (handlers.resuming).
    Resume(Option<Box<Expr>>),
    /// `when a, b { … }` (shared.when): each name's handle, and the local that stands for
    /// its value's place in the block.
    When(Vec<Held>, Block),
    /// A staging annotation on its `if`, `match` or `for`, which means what the form means
    /// (meta.staging-annotations and meta.erasure).
    Comptime(Box<Expr>),
    /// A bound test, the whole condition of an `if` (meta.bound-tests).
    Bound(Box<BoundTest>),
    /// A quote (macros.quote).
    Quote(Box<super::Quote>),
    /// A name with an error, one whose uses have the error type, or a `break` or `continue`
    /// outside every loop.
    Error,
}

/// A bound test, `T: B + …` (meta.bound-tests): the type parameter it tests, `None` after an
/// error, which resolution reported, and each bound, a trait with the arguments written, where
/// it is written. A trait with parameters written without arguments has none here, and the
/// test holds for an impl of it with any.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BoundTest {
    /// The type parameter it tests.
    pub param: Option<GenericId>,
    /// The name written.
    pub name: Ident,
    /// Each bound, with where it is written.
    pub bounds: Vec<(super::TraitRef, TextRange)>,
}

/// A name of a `when`: the handle it names, a local or an error, and the local of the same
/// name that stands for the place of the handle's value in the block (shared.when).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Held {
    /// The handle it names.
    pub handle: Expr,
    /// The local that stands for the place of the handle's value.
    pub place: LocalId,
}

/// What a `Type.m` or `Trait.m` names a member of.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MemberOwner {
    /// A type, `Type.m`.
    Type(TypeRef),
    /// A trait, `Trait.m`.
    Trait(Item),
}

/// A part of an interpolated string.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Segment {
    /// Text, its escapes resolved.
    Text(String),
    /// An interpolated expression, with its format spec.
    Splice(Expr, Option<String>),
}

/// An argument of a call.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Arg {
    /// Whether it is written `inout`.
    pub inout: bool,
    /// Its expression.
    pub value: Expr,
    /// The argument, with its `inout` if it has one.
    pub at: TextRange,
}

/// A field of a record literal or of an update.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FieldInit {
    /// The field's name.
    pub field: Ident,
    /// Its value.
    pub value: Expr,
}

/// An arm of a `match` or of a `catch`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Arm {
    /// Its pattern.
    pub pattern: Pat,
    /// Its `if` guard.
    pub guard: Option<Box<Expr>>,
    /// The reason of a catch-all, unescaped.
    pub because: Option<(String, TextRange)>,
    /// The expression after `=>`.
    pub body: Expr,
}

/// A closure's parameter. One marked `inout` binds a name (expressions.inout-closure-parameters).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClosureParam {
    /// Whether it is written `inout`.
    pub mode: Mode,
    /// The pattern it binds.
    pub pattern: Pat,
    /// Its written type.
    pub annotation: Option<TypeRef>,
    /// The parameter, with its `inout` if it has one.
    pub at: TextRange,
}

/// What a `for` loop runs over.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Iterable {
    /// A value whose elements it takes.
    Iter(Expr),
    /// A range, and whether it includes its end.
    Range(Expr, Expr, bool),
}

/// A prefix operator.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum UnaryOp {
    /// `-`.
    Neg,
    /// `!`.
    Not,
}

/// A binary operator, or the operator of a compound assignment.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum BinaryOp {
    /// `+`.
    Add,
    /// `-`.
    Sub,
    /// `*`.
    Mul,
    /// `/`.
    Div,
    /// `%`.
    Rem,
    /// `+%`, which wraps.
    AddWrap,
    /// `-%`, which wraps.
    SubWrap,
    /// `*%`, which wraps.
    MulWrap,
    /// `==`.
    Eq,
    /// `!=`.
    Ne,
    /// `<`.
    Lt,
    /// `<=`.
    Le,
    /// `>`.
    Gt,
    /// `>=`.
    Ge,
    /// `&&`.
    And,
    /// `||`.
    Or,
    /// `&`.
    BitAnd,
    /// `|`.
    BitOr,
    /// `^`.
    BitXor,
    /// `<<`.
    Shl,
    /// `>>`.
    Shr,
}
