//! The second and third steps of name resolution, for one module: its header is checked against
//! its name (program.module-header), and every declaration and body is resolved into its HIR form,
//! recording the places where it names another module.
//!
//! No error causes another (errors.root-causes). A name with an error resolves to an error node,
//! which the type checker gives the error type, and so does every use of a name whose
//! declaration is an error of its own name.

mod bodies;
mod bound_tests;
mod bounds;
mod control;
mod decls;
mod determined;
mod effects;
mod escaping;
mod expand;
mod exprs;
mod foreign;
mod impls;
mod input;
mod limits;
mod module;
mod paths;
mod patterns;
mod poly;
mod procs;
mod quotes;
mod records;
mod removal;
mod signature;
mod traits;
mod typedecls;
mod types;
mod values;
mod views;
mod wheres;

use std::cell::RefCell;
use std::collections::HashMap;
use std::sync::Arc;

use rustc_hash::FxHashMap;
use stilt_db::{Db, Program, SourceFile};
use stilt_diag::{Code, Diagnostic};
use stilt_syntax::{SyntaxNode, SyntaxToken, TextRange, TextSize, ast};

use crate::Anchor;
use crate::hir::{
    Body, GenericId, Ident, Item, Limit, Local, LocalId, ModuleHir, Name, Owner, TraitRef, Ty,
};
use crate::scope::{DefMap, Entry, Kind, Module, Scope, module_scope, modules_of};

pub use input::{Input, resolve_input};

/// The resolution of a module: its declarations and bodies, its diagnostics, and where it names
/// other modules.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ModuleResolution {
    /// Shared with [`module_hir`], each body with [`module_body`]: the database holds each once.
    pub module: Arc<ModuleHir>,
    /// The bodies, by [`crate::hir::BodyIndex`].
    pub bodies: Vec<Arc<Body>>,
    /// Where each body starts in the file, which its positions are relative to.
    pub body_starts: Vec<TextSize>,
    /// The limits of the header's `without`, each where it is written in the file
    /// (program.header-limits).
    pub header_limits: Vec<(Limit, TextRange)>,
    /// Its errors of name resolution, in the order found.
    pub diagnostics: Vec<Diagnostic>,
    /// The modules it names, each where it names them: at a `use` declaration, or at the first
    /// name of a path that names one of their items. They are in source order.
    pub references: Vec<(Name, TextRange)>,
    pub(crate) anchors: Anchors,
}

/// The spans of the parts of a module's items that diagnostics found without positions are
/// placed at.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct Anchors {
    items: Vec<ItemAnchors>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ItemAnchors {
    start: TextRange,
    name: Option<TextRange>,
    variants: Vec<TextRange>,
    impl_type: Option<TextRange>,
    members: Vec<TextRange>,
    wheres: Vec<TextRange>,
}

impl Anchors {
    pub(crate) fn range(&self, anchor: Anchor) -> TextRange {
        let item = |i: u32| &self.items[i as usize];
        match anchor {
            Anchor::FileStart => TextRange::default(),
            Anchor::Item(i) => item(i).start,
            Anchor::Name(i) => item(i).name.unwrap_or(item(i).start),
            Anchor::Variant(i, j) => item(i).variants[j as usize],
            Anchor::ImplType(i) => item(i).impl_type.unwrap_or(item(i).start),
            Anchor::Member(i, j) => item(i).members[j as usize],
            Anchor::Where(i, j) => item(i).wheres[j as usize],
        }
    }
}

/// Resolves the module of a file of the program or of the standard library. The standard
/// library's modules are resolved among themselves, since they name no module of a program.
///
/// Its result is never compared with the last one: the queries that read it are projections
/// of it, such as [`module_hir`], [`module_body`] and [`body_starts`], which all run again
/// whenever it does, and each is compared on its own, so that a part that didn't change leaves the
/// queries after it as they were (goal body-edits-recheck-one-body). The projections then share the
/// new result's parts, and the database never holds an old copy of a module beside a new one
/// (bounded-cache).
#[salsa::tracked(returns(ref), no_eq)]
pub fn resolve_module(db: &dyn Db, program: Program, file: SourceFile) -> ModuleResolution {
    let map = modules_of(db, program, file);
    let module = map
        .of_file(file)
        .expect("every file of the program has a module");
    let resolver = Resolver::new(db, program, map, module, file);
    resolver.module(&stilt_db::parse(db, file).tree())
}

/// A module's declarations, which an edit that changes none of them leaves as they are, so
/// that the queries that read only declarations don't run again.
#[salsa::tracked(returns(ref))]
pub fn module_hir(db: &dyn Db, program: Program, file: SourceFile) -> Arc<ModuleHir> {
    Arc::clone(&resolve_module(db, program, file).module)
}

/// The limits of a file's module header, each where it is written. The header comes before
/// every item, so an edit of an item leaves them as they are, and the diagnostics of a body
/// that point at them, through [`Diagnostic::with_note_in_file`], stay valid.
#[salsa::tracked(returns(ref))]
pub fn header_limits(db: &dyn Db, program: Program, file: SourceFile) -> Vec<(Limit, TextRange)> {
    resolve_module(db, program, file).header_limits.clone()
}

/// The body `index` of a file's module, which an edit that changes nothing in it leaves as it
/// is, even when the edit moves it, so that the queries that read only it don't run again
/// (goal body-edits-recheck-one-body).
#[salsa::tracked(returns(ref))]
pub fn module_body(db: &dyn Db, program: Program, file: SourceFile, index: u32) -> Arc<Body> {
    Arc::clone(&resolve_module(db, program, file).bodies[index as usize])
}

/// Where each body of a file's module starts in the file, which its positions are relative to.
#[salsa::tracked(returns(ref))]
pub fn body_starts(db: &dyn Db, program: Program, file: SourceFile) -> Vec<TextSize> {
    resolve_module(db, program, file).body_starts.clone()
}

/// The body of a file's module whose code holds `offset`, by its index: the one that starts
/// last at or before it, since no body holds another. A declaration's doc examples start before
/// its own body, in its doc comment, but come after it in [`body_starts`].
#[must_use]
pub fn body_at(db: &dyn Db, program: Program, file: SourceFile, offset: TextSize) -> Option<u32> {
    let starts = body_starts(db, program, file);
    let (index, _) = (0..)
        .zip(starts)
        .filter(|(_, s)| **s <= offset)
        .max_by_key(|(i, s)| (**s, *i))?;
    Some(index)
}

/// A node's first token that isn't trivia: the first of its tokens, where most nodes start, or
/// the first after the doc comments before it.
fn written_first(node: &SyntaxNode) -> Option<SyntaxToken> {
    match node.first_token() {
        Some(t) if !t.kind().is_trivia() => Some(t),
        _ => node
            .descendants_with_tokens()
            .filter_map(rowan::NodeOrToken::into_token)
            .find(|t| !t.kind().is_trivia()),
    }
}

/// `Self`, which only impl and trait blocks define (traits.impl-blocks).
#[derive(Clone, Debug)]
enum SelfKind {
    None,
    Impl(Ty),
    /// A trait's, which takes this many type arguments: 0 for a trait over types
    /// (traits.constructor-traits).
    Trait(u32),
}

/// A member type in scope, as `C.Item` (traits.member-types): the type parameter `param`, the trait
/// of one of its bounds, the name of the trait's parameter, and the type the bound gives it.
#[derive(Clone, Debug)]
struct MemberType {
    param: GenericId,
    trait_item: Item,
    name: Name,
    ty: Ty,
    /// Where a fix gives the bound its argument, for a bound of a trait with this one parameter
    /// written without it: the end of the trait's path, and the end of the generics before
    /// their `>` (traits.member-types).
    unnamed: Option<(TextSize, TextSize)>,
}

/// Where names are being resolved.
#[derive(Clone, Debug)]
struct Ctx {
    self_kind: SelfKind,
    /// Innermost last, as are the next.
    type_params: Vec<(Name, GenericId)>,
    row_vars: Vec<(Name, GenericId)>,
    /// The value parameters in scope, each with its type (generics.value-parameters-in-body).
    value_params: Vec<(Name, GenericId, Ty)>,
    in_loop: bool,
    /// Whether the names being resolved are in a signature that other modules see
    /// (program.private-in-signatures).
    public: bool,
    /// The member types of the type parameters in scope (traits.member-types).
    members: Vec<MemberType>,
    /// The constructor parameters in scope, each with its arity (traits.constructor-parameters).
    constructors: Vec<(GenericId, u32)>,
    /// The packs in scope (variadics.packs).
    packs: Vec<GenericId>,
    /// The arity of the constructor trait whose members, or whose impl's members, are being
    /// resolved, whose receivers write their types, and 0 elsewhere (traits.receiver-types).
    constructor: u32,
    /// Whether the members being resolved are a trait's or a trait impl's, which have the
    /// trait's signatures (traits.where).
    trait_member: bool,
    /// What a function's `where` clause bounds besides its own generics (traits.where): the
    /// member types of its impl block's parameters, each with its bounds, and the member types
    /// that a bound's argument fixes, each with a bound's trait, its arguments and where it is
    /// written.
    assumed: Vec<(GenericId, Vec<TraitRef>)>,
    fixed: Vec<(Ty, Item, Vec<Ty>, TextRange)>,
}

impl Ctx {
    fn module() -> Self {
        Self {
            self_kind: SelfKind::None,
            type_params: Vec::new(),
            row_vars: Vec::new(),
            value_params: Vec::new(),
            in_loop: false,
            public: false,
            members: Vec::new(),
            constructors: Vec::new(),
            packs: Vec::new(),
            constructor: 0,
            trait_member: false,
            assumed: Vec::new(),
            fixed: Vec::new(),
        }
    }
}

/// What a name refers to.
#[derive(Clone, Debug)]
enum Meaning {
    Local(LocalId),
    /// A type parameter.
    Param(GenericId),
    /// A value parameter, with its type (generics.value-parameters-in-body).
    Value(GenericId, Ty),
    SelfType(Ty),
    Item(Item, Entry),
    Namespace(Name),
    /// Nothing: its uses have the error type.
    Broken,
}

impl Meaning {
    fn describe(&self) -> &'static str {
        match self {
            Self::Local(_) => "a variable",
            Self::Param(_) | Self::SelfType(_) => "a type",
            Self::Value(..) => "a value parameter",
            Self::Item(_, entry) => entry.kind.describe(),
            Self::Namespace(_) => "a module",
            Self::Broken => "nothing",
        }
    }

    /// The type a name means, if it means one.
    fn as_type(&self) -> Option<Ty> {
        match self {
            Self::Param(v) => Some(Ty::Param(v.clone())),
            Self::SelfType(t) => Some(t.clone()),
            Self::Item(item, entry) if entry.kind == Kind::Type => {
                Some(Ty::Con(item.clone(), Vec::new()))
            }
            _ => None,
        }
    }
}

struct Resolver<'a> {
    db: &'a dyn Db,
    program: Program,
    map: &'a DefMap,
    module: &'a Module,
    /// The module's own scope.
    own: &'a Scope,
    /// The offset in the file from which the offsets of the tree being resolved count: that of
    /// a doc example's text, and otherwise 0.
    base: TextSize,
    diagnostics: Vec<Diagnostic>,
    /// Inside a body, the E0211 it reported so far, each with its name and its place in
    /// `diagnostics`: the body keeps one for each name (errors.unknown-names). A name without a
    /// place is one that a pattern writes without a module, which type checking reports.
    unknown: Option<Vec<(String, Option<usize>)>>,
    /// Inside a body, the errors of its analyses found where it writes types (views.view-types).
    analysed: Vec<Diagnostic>,
    references: Vec<(Name, TextRange)>,
    bodies: Vec<Body>,
    body_starts: Vec<TextSize>,
    /// The locals of the body being resolved.
    locals: Vec<Local>,
    /// The locals in scope, innermost last; `None` for a binding whose uses have the error type.
    scope: Vec<(Name, Option<LocalId>)>,
    /// Where the module's types and traits are declared, for the fixes that make them public.
    declared: HashMap<Name, TextSize>,
    /// The declaration whose types are being resolved, which owns the type parameters of the
    /// polymorphic function types they write, and how many it has so far
    /// (polymorphism.function-types).
    poly_owner: Option<Owner>,
    next_poly: u32,
    /// The names of those type parameters, in the module.
    poly_names: Vec<(GenericId, Name)>,
    /// The packs that the type inside a spread names so far, while one is being resolved
    /// (variadics.type-spreads).
    spread: Option<Vec<GenericId>>,
    /// The packs declared where none may be, which E0344 reports, and which stand for their
    /// elements wherever they are written, spread or not, so that nothing more is reported
    /// (errors.unknown-names).
    misplaced: Vec<GenericId>,
    /// The type parameters that the open record types of a function's parameters stand for,
    /// while its signature is resolved (records.open-parameter-types).
    hidden: Option<records::Hidden>,
    /// The macros' expansions being resolved, innermost last (macros.expansion).
    regions: Vec<expand::Region>,
    /// The tokens of the written use being resolved (macros.expansion-size).
    budget: expand::Budget,
    /// Where the next expansion's region starts, past every file's text.
    next_virtual: u32,
    /// The number of the body's last expansion, which marks the names its template writes.
    marks: u32,
    /// The expansions of the body being resolved.
    expansions: Vec<crate::hir::Expansion>,
    /// The `unsafe` blocks of the body being resolved (c.unsafe-and-foreign).
    unsafe_blocks: Vec<crate::hir::UnsafeBlock>,
    /// Whether a declaration's templates, or a quote's contents, are being resolved, whose uses
    /// aren't expanded.
    checking: bool,
    /// Inside a quote's contents, the names of the locals of the code around it, which a quote
    /// names through a splice (macros.quote-hygiene).
    quoting: Option<Vec<Name>>,
    /// Whether `main`'s own row is being resolved, which no user-defined effect may reach
    /// (handlers.no-effect-reaches-main).
    main_row: bool,
    /// The names of the value parameters in scope of the function being resolved, which no
    /// binding takes (generics.value-parameters-in-body).
    values_in_scope: Vec<Name>,
    /// The keys of the names that expansions bind, by name and mark ([`Resolver::key`]).
    keys: RefCell<FxHashMap<(Name, u32), Name>>,
    /// What it looked up in other modules ([`Resolver::scope_of`], [`Resolver::named_in`]).
    looked: RefCell<paths::Looked<'a>>,
}

impl<'a> Resolver<'a> {
    fn new(
        db: &'a dyn Db,
        program: Program,
        map: &'a DefMap,
        module: &'a Module,
        file: SourceFile,
    ) -> Self {
        Resolver {
            db,
            program,
            map,
            module,
            own: &module_scope(db, program, file).scope,
            base: TextSize::default(),
            diagnostics: Vec::new(),
            unknown: None,
            analysed: Vec::new(),
            references: Vec::new(),
            bodies: Vec::new(),
            body_starts: Vec::new(),
            locals: Vec::new(),
            scope: Vec::new(),
            declared: HashMap::new(),
            poly_owner: None,
            next_poly: 0,
            poly_names: Vec::new(),
            spread: None,
            misplaced: Vec::new(),
            hidden: None,
            regions: Vec::new(),
            budget: expand::Budget::default(),
            next_virtual: 1 << 31,
            marks: 0,
            expansions: Vec::new(),
            unsafe_blocks: Vec::new(),
            checking: false,
            quoting: None,
            main_row: false,
            values_in_scope: Vec::new(),
            keys: RefCell::default(),
            looked: RefCell::default(),
        }
    }

    /// A span of the tree being resolved, in its file.
    fn in_file(&self, range: TextRange) -> TextRange {
        range + self.base
    }

    fn at_token(&self, token: &SyntaxToken) -> TextRange {
        self.in_file(token.text_range())
    }

    /// The span of a node: from its first token, after any doc comments, to its end.
    fn at(&self, node: &SyntaxNode) -> TextRange {
        let range = node.text_range();
        let first = written_first(node).map_or(range.start(), |t| t.text_range().start());
        self.in_file(TextRange::new(first, range.end()))
    }

    /// The span of a node's first token, after any doc comments.
    fn first_token(&self, node: &SyntaxNode) -> TextRange {
        written_first(node).map_or_else(|| self.at(node), |t| self.at_token(&t))
    }

    fn error(&mut self, code: Code, at: TextRange, message: String) {
        self.diagnostics.push(Diagnostic::new(code, at, message));
    }

    fn ident(&self, token: &SyntaxToken) -> Ident {
        Ident {
            name: Name::from(token.text()),
            at: self.at_token(token),
        }
    }

    fn name(&self, name: Option<ast::Name>, fallback: &SyntaxNode) -> Ident {
        match name.and_then(|n| n.ident()) {
            Some(token) => self.ident(&token),
            None => Ident {
                name: Name::from(""),
                at: self.at(fallback),
            },
        }
    }

    /// The name of a field, of a record pattern or a struct literal written at `fallback`.
    fn field(&self, name: Option<ast::NameRef>, fallback: &SyntaxNode) -> Ident {
        match name.and_then(|n| n.ident()) {
            Some(token) => self.ident(&token),
            None => Ident {
                name: Name::from(""),
                at: self.at(fallback),
            },
        }
    }

    fn path(&self, path: Option<ast::Path>) -> Vec<Ident> {
        path.into_iter()
            .flat_map(|p| p.segments())
            .map(|t| self.ident(&t))
            .collect()
    }
}

/// A type without the parentheses around it, which the tree form doesn't keep
/// (syntax.tree-form.normalizations), so that the type is placed where the type inside them is.
fn bare(t: &ast::Type) -> ast::Type {
    match t {
        ast::Type::ParenType(p) => p.ty().map_or_else(|| t.clone(), |inner| bare(&inner)),
        _ => t.clone(),
    }
}

fn dotted(path: &[Ident]) -> String {
    path.iter().map(|n| &*n.name).collect::<Vec<_>>().join(".")
}
