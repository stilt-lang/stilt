//! Type checking of one body (errors.phases, phase 1).
//!
//! A body is checked in evaluation order (values.left-to-right), with expected types flowing inward
//! where they are known, as in any bidirectional checker. Rules whose answer needs every type
//! of the body, such as trait bounds, literal ranges and unused values, are recorded as they
//! are met and decided at the end of the body, after literals take their default types
//! (numbers.literal-defaults).
//!
//! [`State`] holds what checking a body has found so far, and the submodules check its parts,
//! one concern each, as the reference interpreter's `Check_*` modules do.

mod arrays;
mod bare;
mod bindings;
mod blocks;
mod bodies;
mod calls;
mod closures;
mod control;
mod conversions;
mod editions;
mod effects;
mod expect;
mod exprs;
mod fields;
mod finish;
mod fixes;
mod foreign;
mod fresh;
mod handlers;
mod input;
mod members;
mod operators;
mod params;
mod patterns;
mod poly;
mod properties;
mod quotes;
mod records;
mod reflect;
mod refutable;
mod spreads;
mod synonyms;
mod types;
mod value_calls;
mod when;
mod with;

use std::collections::HashMap;

use stilt_diag::{Code, Diagnostic};
use stilt_hir::decls::Lookup;
use stilt_hir::hir::{GenericId, Item, LocalId, Name, SignatureSpans};
use stilt_pkg::edition::Rename;
use stilt_syntax::TextRange;

use crate::implements::Bounds;
use crate::params::BoundArgs;
use crate::tast;
use crate::ty::{Kind, Row, Table, Ty, VarId};
use refutable::Named;

pub(crate) use bodies::{BodyKind, check_body};
pub(crate) use input::check_input;

/// The types that an operator applies to (numbers.no-implicit-conversions,
/// numbers.bitwise-operators and numbers.comparisons).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Rule {
    Numeric,
    Integer,
    Negatable,
    BoolOrInteger,
}

/// Where a value must have type `()` or `Never` (expressions.statements and expressions.if). An
/// `if` without `else` carries its own type, which is `()` unless its block has another.
#[derive(Clone, Debug)]
enum UnitSite {
    /// An expression statement, and the closure that starts the next statement with `||`, if
    /// one does (lexical.terminator-insertion).
    Statement(Option<Leading>, Option<Receiver>),
    IfWithoutElse(Ty),
}

/// The local that a statement calls a method of, as `xs` in `xs.reversed()`, whose type an unused
/// value of the same type most likely was meant to replace (expressions.unused-values).
#[derive(Clone, Copy, Debug)]
struct Receiver {
    local: stilt_hir::hir::LocalId,
}

/// A closure without parameters that a statement starts with `||`: the operator that its
/// author may have meant to end the line before.
#[derive(Clone, Copy, Debug)]
struct Leading {
    /// The closure.
    closure: TextRange,
    /// Its `||`, with the blanks that follow it.
    operator: TextRange,
}

/// A numeric literal, whose range is checked once its type is known (numbers.integer-literals,
/// numbers.float-literals, numbers.literal-defaults and numbers.negative-literals).
#[derive(Clone, Debug)]
struct Literal {
    ty: Ty,
    text: String,
    negative: bool,
    float: bool,
    at: TextRange,
}

/// What a body is checked in: the declarations, and the module and declaration it belongs to.
pub(crate) struct Env<'a> {
    pub(crate) decls: &'a dyn Lookup,
    /// The module's dotted name.
    pub(crate) module: Name,
    /// Whether the module is the standard library's, whose code no member that a program's
    /// error leaves out reaches (errors.error-type).
    pub(crate) std: bool,
    /// The traits visible to method calls (traits.traits-in-scope).
    pub(crate) traits: Vec<Item>,
    pub(crate) bounds: Bounds,
    /// The arguments the bounds of the rigid types give traits with parameters
    /// (traits.bound-arguments).
    pub(crate) bound_args: BoundArgs,
    /// What `Self` means: the implementing type, in a trait's default method.
    pub(crate) self_ty: Option<Ty>,
    /// The names of type parameters and row variables, for messages.
    pub(crate) names: &'a dyn Fn(&GenericId) -> Name,
    /// The modules that the module imports, by name.
    pub(crate) imports: &'a [Name],
    /// Where fixes may edit the function's signature: one that no trait's signature binds.
    pub(crate) signature: Option<&'a SignatureSpans>,
    /// Whether the body is the program's `main`'s, which handles `async` and no other effect
    /// (handlers.no-effect-reaches-main; tasks.sequential-run).
    pub(crate) main: bool,
    /// Whether the body is a procedural macro's, whose row is empty or `raise<meta.Error>`
    /// (macros.procedural-declarations), so that no fix declares anything else in it.
    pub(crate) procedural: bool,
    /// The renames of `std`'s methods in force in the body's package, each with the edition
    /// that made it (editions.renames).
    pub(crate) renames: &'a [(Rename, &'static str)],
}

/// What checking one body has found so far.
pub(crate) struct State<'a> {
    env: Env<'a>,
    table: Table,
    locals: HashMap<LocalId, Ty>,
    /// Where each local that a pattern binds is bound, and the local each use reads, by where
    /// the use is, which a mismatch's chain names (goal one-form-per-reader).
    bound: HashMap<LocalId, TextRange>,
    uses: HashMap<TextRange, LocalId>,
    /// The names of the body's locals, then of those that elaboration adds.
    local_names: Vec<Name>,
    errors: Vec<Diagnostic>,
    /// Whether the body holds an error that resolution reported.
    broken: bool,
    vars: Vec<Ty>,
    /// Variables already reported as unknown.
    unknown: Vec<VarId>,
    obligations: Vec<(Ty, Item, TextRange)>,
    /// The arguments that types must give traits with parameters, as the bounds they meet say,
    /// each decided once the type is known (traits.bound-arguments).
    arg_obligations: Vec<(Ty, Item, Vec<Ty>, TextRange)>,
    operators: Vec<(Ty, Rule, TextRange)>,
    /// Shift amounts whose type was open where they were checked (numbers.shift-amounts).
    amounts: Vec<(Ty, TextRange)>,
    int_patterns: Vec<(Ty, TextRange)>,
    literals: Vec<Literal>,
    units: Vec<(Ty, UnitSite, TextRange)>,
    specs: Vec<(Ty, String, TextRange)>,
    /// The error types of `catch`es whose operands may still raise.
    catch_errors: Vec<Ty>,
    /// What uses give the row variables their callees pair (effects.passing-to-paired-variables).
    passed: Vec<(TextRange, Row, tast::Label)>,
    /// The staging annotations, each as its keyword and the form it marks
    /// (meta.staging-annotations).
    staged: Vec<(TextRange, TextRange)>,
    /// The type of each splice's value, its place and its span, checked once the body's types
    /// are known (macros.splices).
    splices: Vec<(Ty, stilt_hir::hir::Place, TextRange)>,
    /// The list patterns matched against arrays, each with the arrays' element type, which
    /// their refutability reads (generics.array-patterns).
    array_patterns: HashMap<TextRange, Ty>,
    /// Each mismatch, by its place among the errors, with the type it expected, to which the
    /// bindings of that type are added once the body is checked (goal admissible-alternatives).
    mismatches: Vec<(usize, Ty)>,
    /// What each name that a pattern writes without a module names, by the pattern's place,
    /// once checked (patterns.variants-by-type).
    bare: HashMap<TextRange, Named>,
    /// The E0211 of those names that name nothing, each with its name and its place among the
    /// errors, of which the body keeps one per name (errors.unknown-names).
    unknown_names: Vec<(Name, usize)>,
    /// How many copies of the type parameters of polymorphic function types it made
    /// (polymorphism.arguments).
    poly_copies: u32,
    /// Each method's name that its package's edition renamed, with the name it has there
    /// (editions.renames).
    renamed: Vec<(TextRange, &'static str)>,
    /// What a `when` around a read of a `Shared<T>`'s field would hold, for E0313's fix: the
    /// statement being checked, or a binding's value; none in a closure or a `when`.
    wrap: Option<TextRange>,
    /// How many fresh types of shapes it made, those that the next region takes, and the
    /// regions open (meta.fresh-types).
    fresh_count: u32,
    fresh_pending: Vec<GenericId>,
    regions: Vec<fresh::Region>,
    /// The body's `unsafe` blocks, each whole, which may hold unsafe operations
    /// (c.unsafe-operations).
    unsafe_blocks: Vec<TextRange>,
    /// The `var` bindings and `inout` parameters so far, which code may change
    /// (modes.what-can-be-modified).
    modifiable: Vec<stilt_hir::hir::LocalId>,
    /// The calls outside every `try`'s operand so far, whose raise a fix marks with `try`
    /// (effects.marking).
    unmarked: Vec<TextRange>,
    /// The types that C must hold, each with the call that reads, writes or lends them, checked
    /// once the body's types are known (c.element-types and c.lending-buffer).
    c_elements: Vec<(Ty, TextRange)>,
}

/// Where in a body an expression is.
struct Cx {
    /// The type that `return` returns.
    ret: Ty,
    /// The type of the place that `yield` hands the caller, in a projection's body
    /// (projections.yield).
    yields: Option<Ty>,
    /// The effects performed so far, in order.
    effects: Vec<(Row, TextRange)>,
    /// The effects of the row that the code must fit, with their type arguments, which a
    /// performance takes (handlers.performing-operation).
    known: Vec<(Item, Vec<Ty>)>,
    /// In an operation's body of a handler that takes control: the operation's result type,
    /// which `resume` takes, and the handler's `R` (handlers.resuming).
    resume: Option<(Ty, Ty)>,
    /// How many regions of fresh types were open where the function or closure whose value
    /// `return` gives starts (meta.fresh-types).
    returns_at: usize,
}

impl Cx {
    fn new(ret: Ty) -> Self {
        Self {
            ret,
            yields: None,
            effects: Vec::new(),
            known: Vec::new(),
            resume: None,
            returns_at: 0,
        }
    }
}

impl<'a> State<'a> {
    fn new(env: Env<'a>, local_names: Vec<Name>) -> Self {
        Self {
            env,
            table: Table::default(),
            locals: HashMap::new(),
            bound: HashMap::new(),
            uses: HashMap::new(),
            local_names,
            errors: Vec::new(),
            broken: false,
            vars: Vec::new(),
            unknown: Vec::new(),
            obligations: Vec::new(),
            arg_obligations: Vec::new(),
            operators: Vec::new(),
            amounts: Vec::new(),
            int_patterns: Vec::new(),
            literals: Vec::new(),
            units: Vec::new(),
            specs: Vec::new(),
            catch_errors: Vec::new(),
            passed: Vec::new(),
            staged: Vec::new(),
            splices: Vec::new(),
            array_patterns: HashMap::new(),
            mismatches: Vec::new(),
            bare: HashMap::new(),
            unknown_names: Vec::new(),
            poly_copies: 0,
            renamed: Vec::new(),
            wrap: None,
            fresh_count: 0,
            fresh_pending: Vec::new(),
            regions: Vec::new(),
            unsafe_blocks: Vec::new(),
            unmarked: Vec::new(),
            modifiable: Vec::new(),
            c_elements: Vec::new(),
        }
    }

    fn error(&mut self, code: Code, at: TextRange, message: String) {
        self.errors.push(Diagnostic::new(code, at, message));
    }

    /// A new type variable, of the expression at `at`.
    fn fresh(&mut self, at: TextRange) -> Ty {
        self.fresh_kind(Kind::Any, at)
    }

    fn fresh_kind(&mut self, kind: Kind, at: TextRange) -> Ty {
        let v = self.table.fresh(kind, at);
        self.vars.push(v.clone());
        v
    }

    fn show(&self, t: &Ty) -> String {
        self.table.show(t, self.env.names)
    }

    fn show_effect(&self, e: &Item, args: &[Ty]) -> String {
        self.table.show_effect(e, args, self.env.names)
    }

    fn is_never(&self, t: &Ty) -> bool {
        self.table.is_never(t)
    }

    /// The type with its outermost solved variables replaced, a constructor applied through a
    /// solved head made that constructor applied (traits.constructor-parameters).
    fn resolved(&self, t: &Ty) -> Ty {
        self.table.shape(t)
    }

    /// The type of a numeric literal, whose range is checked at the end of the body, after it takes
    /// its default type (numbers.integer-literals, numbers.float-literals, numbers.literal-defaults
    /// and numbers.negative-literals).
    fn literal(&mut self, text: &str, negative: bool, float: bool, at: TextRange) -> Ty {
        let kind = if float {
            Kind::FloatLiteral
        } else {
            Kind::IntLiteral
        };
        let ty = self.fresh_kind(kind, at);
        self.literals.push(Literal {
            ty: ty.clone(),
            text: text.to_owned(),
            negative,
            float,
            at,
        });
        ty
    }

    /// Requires a type to implement a trait, which is decided at the end of the body
    /// (traits.bounds).
    fn obligation(&mut self, ty: &Ty, trait_item: Item, at: TextRange) {
        self.obligations.push((ty.clone(), trait_item, at));
    }

    /// A local that elaboration adds, such as the parameter of a key path's closure.
    fn synthetic(&mut self, name: &str) -> LocalId {
        let id = LocalId(u32::try_from(self.local_names.len()).expect("under 4G locals"));
        self.local_names.push(Name::from(name));
        id
    }
}

fn node(kind: tast::ExprKind, ty: Ty, at: TextRange) -> tast::Expr {
    tast::Expr { kind, ty, at }
}

fn error_node(at: TextRange) -> tast::Expr {
    node(tast::ExprKind::Error, Ty::Error, at)
}
