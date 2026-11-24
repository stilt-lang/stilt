//! Semantic tokens: what each word of a file is, read off its syntax tree and what checking
//! resolved. A keyword is one where the tree has it as one, so a contextual keyword is one only
//! where it acts as one (lexical.contextual-keywords), and those that direct control are marked
//! apart; a built-in effect in a row or after `without` is an effect of the library
//! (facts.implicit-effects; effects.effect-names; facts.capabilities), and an effect a program
//! declares is an effect where it is declared and where a row or a performance names it
//! (handlers.declaring-effect, handlers.effects-in-rows and handlers.performing-operation). A
//! variable is a parameter or a local as its body's types say, marked mutable when `var` binds it
//! or it is an `inout` parameter, and a constant is read-only. A name in a macro's use or template,
//! whose tokens the tree doesn't parse, is read by the tokens around it (macros.uses and
//! macros.templates), and a quote's splices and spreads are marked as a template's fragments are
//! (macros.splices and macros.spreads). Doc comments are documentation, and their examples' code is
//! read as code (tests.prop-lines); a string's escapes, its interpolation braces and their format
//! specs are marked apart from its text (lexical.escapes, lexical.interpolation and
//! lexical.format-specs).

mod control;
mod keywords;
mod pieces;

use std::collections::{HashMap, HashSet};

use stilt_db::{Database, Program, SourceFile};
use stilt_hir::hir::Mode;
use stilt_lsp::modifier::{DECLARATION, LIBRARY, MUTABLE, READONLY};
use stilt_lsp::{Token, TokenSort};
use stilt_syntax::SyntaxKind::{self, *};
use stilt_syntax::{SyntaxNode, SyntaxToken};
use stilt_types::tast::ExprKind;
use stilt_types::tast::PatKind;

use super::typed::{self, Node};

/// What the words of a file may name, beside its variables.
struct Context {
    /// The variables the code names, by their spans: whether each is a parameter, and whether
    /// it is mutable.
    locals: HashMap<(u32, u32), (bool, bool)>,
    traits: HashSet<String>,
    variants: HashSet<String>,
    /// The effects the program declares (handlers.declaring-effect).
    effects: HashSet<String>,
    /// The constants, which are written in capitals (lexical.case).
    constants: HashSet<String>,
    /// The names that `use` binds to modules.
    modules: HashSet<String>,
}

/// The semantic tokens of `file`, in order.
pub fn tokens(db: &Database, program: Program, file: SourceFile) -> Vec<Token> {
    let context = context(db, program, file);
    let root = stilt_db::parse(db, file).syntax();
    let mut found = Vec::new();
    for token in root
        .descendants_with_tokens()
        .filter_map(stilt_syntax::SyntaxElement::into_token)
    {
        classify(&token, &context, &mut found);
    }
    found
}

fn context(db: &Database, program: Program, file: SourceFile) -> Context {
    let mut context = Context {
        locals: locals(db, program, file),
        traits: HashSet::new(),
        variants: HashSet::new(),
        effects: HashSet::new(),
        constants: HashSet::new(),
        modules: HashSet::new(),
    };
    let module = stilt_hir::module_hir(db, program, file);
    context.modules = (module.imports.iter())
        .map(|m| m.rsplit('.').next().unwrap_or(m).to_owned())
        .collect();
    let mut files = vec![file];
    files.extend(super::scope::module_file(db, program, "std.prelude"));
    files.extend((module.imports.iter()).filter_map(|m| super::scope::module_file(db, program, m)));
    for f in files {
        let tree = stilt_db::parse(db, f).syntax();
        for node in tree.descendants() {
            let set = match node.kind() {
                TRAIT => &mut context.traits,
                VARIANT => &mut context.variants,
                EFFECT => &mut context.effects,
                CONST => &mut context.constants,
                _ => continue,
            };
            if let Some(name) = node.children().find(|c| c.kind() == NAME) {
                set.insert(name.text().to_string());
            }
        }
    }
    context
}

/// The variables that the bodies of a file name, by their spans: whether each is a parameter,
/// a function's or a closure's, and whether it is mutable.
fn locals(db: &Database, program: Program, file: SourceFile) -> HashMap<(u32, u32), (bool, bool)> {
    let mut found = HashMap::new();
    for body in typed::bodies(db, program, file) {
        let mutable = body.mutable();
        let mut params: Vec<_> = body.typed.params.iter().map(|(_, v)| *v).collect();
        let inout: Vec<_> = (body.typed.params.iter())
            .filter(|(m, _)| *m == Mode::Inout)
            .map(|(_, v)| *v)
            .collect();
        let nodes = body.nodes();
        for (_, node) in &nodes {
            if let Node::Expr(e) = node
                && let ExprKind::Closure(ps, _) = &e.kind
            {
                params.extend(ps.iter().filter_map(|p| match p.kind {
                    PatKind::Bind(v) => Some(v),
                    _ => None,
                }));
            }
        }
        for (range, node) in &nodes {
            // A value parameter that a body reads (generics.value-parameters-in-body).
            if let Node::Expr(e) = node
                && let ExprKind::ValueParam(_) = e.kind
            {
                found.insert((range.start().into(), range.end().into()), (true, false));
            }
        }
        for (range, node) in nodes {
            let v = match node {
                Node::Expr(e) => match e.kind {
                    ExprKind::Local(v) => v,
                    _ => continue,
                },
                Node::Pat(p) => match p.kind {
                    PatKind::Bind(v) => v,
                    _ => continue,
                },
            };
            let span = (range.start().into(), range.end().into());
            let changes = mutable.contains(&v) || inout.contains(&v);
            found.insert(span, (params.contains(&v), changes));
        }
    }
    found
}

fn classify(token: &SyntaxToken, context: &Context, found: &mut Vec<Token>) {
    let kind = token.kind();
    if let Some((sort, modifiers)) = keywords::keyword(token) {
        return push(found, token, sort, modifiers);
    }
    let sort = match kind {
        COMMENT => TokenSort::Comment,
        DOC_COMMENT => return pieces::doc(token, found),
        STRING | STRING_HEAD | STRING_MID | STRING_TAIL => return pieces::string(token, found),
        FORMAT => TokenSort::FormatSpecifier,
        // A tuple's element, as `pair.0`, is a field.
        INT if parent_is(token, FIELD_EXPR) => TokenSort::Field,
        INT | FLOAT => TokenSort::Number,
        BANG if parent_is(token, MACRO_USE) => TokenSort::Macro,
        DOLLAR if parent_is(token, MACRO_FRAG) => TokenSort::Fragment,
        // A quote's splice or spread, `$x`, `$(e)`, `$..x` (macros.splices and macros.spreads).
        DOLLAR | DOT2 if is_splice(token) => TokenSort::Fragment,
        LOWER_IDENT | UPPER_IDENT => {
            if let Some((sort, modifiers)) = word(token, context) {
                push(found, token, sort, modifiers);
            }
            return;
        }
        _ => return,
    };
    push(found, token, sort, 0);
}

fn push(found: &mut Vec<Token>, token: &SyntaxToken, sort: TokenSort, modifiers: u32) {
    let range = token.text_range();
    found.push(Token {
        start: range.start().into(),
        end: range.end().into(),
        sort,
        modifiers,
    });
}

/// Whether a token is a splice's or a spread's own, in a quote (macros.splices and macros.spreads).
fn is_splice(token: &SyntaxToken) -> bool {
    token.parent().is_some_and(|p| {
        matches!(
            p.kind(),
            SPLICE_EXPR | SPLICE_PAT | SPLICE_TYPE | SPLICE_NAME | SPLICE_SPREAD
        )
    })
}

fn parent_is(token: &SyntaxToken, kind: SyntaxKind) -> bool {
    token.parent().is_some_and(|p| p.kind() == kind)
}

/// What an identifier is, with its modifiers.
fn word(token: &SyntaxToken, context: &Context) -> Option<(TokenSort, u32)> {
    let parent = token.parent()?;
    match parent.kind() {
        NAME => declared(token, &parent, context),
        NAME_REF => named(token, &parent, context),
        PATH => path(token, &parent, context),
        FIELD_EXPR => Some(member(token, &parent, context)),
        ROW_VAR => Some((TokenSort::RowVariable, 0)),
        FIELD_PAT => Some((TokenSort::Field, 0)),
        MACRO_FRAG => Some(fragment(token)),
        _ => Some(raw(token, context)),
    }
}

/// A name where it is declared.
fn declared(token: &SyntaxToken, name: &SyntaxNode, context: &Context) -> Option<(TokenSort, u32)> {
    let decl = name.parent()?;
    let sort = match decl.kind() {
        FN if decl
            .parent()
            .is_some_and(|p| matches!(p.kind(), IMPL | TRAIT)) =>
        {
            TokenSort::Method
        }
        // A procedural macro, which the tree holds as a function (macros.procedural-declarations).
        FN if decl.children_with_tokens().any(|t| t.kind() == MACRO_KW) => TokenSort::Macro,
        FN => TokenSort::Function,
        TYPE_DECL => TokenSort::Type,
        TRAIT => TokenSort::Trait,
        EFFECT => TokenSort::Effect,
        OPERATION => TokenSort::Method,
        VARIANT => TokenSort::Variant,
        FIELD_DEF => TokenSort::Field,
        CONST => return Some((TokenSort::Variable, DECLARATION | READONLY)),
        SYNTAX => TokenSort::Macro,
        TYPE_PARAM => TokenSort::TypeParameter,
        // The type parameter a bound test tests, which it names (meta.bound-tests).
        BOUND_TEST => return Some((TokenSort::TypeParameter, 0)),
        ROW_PARAM => TokenSort::RowVariable,
        // A value parameter is an immutable value of its type (generics.value-parameters-in-body).
        VALUE_PARAM => TokenSort::Parameter,
        PARAM => {
            let inout = decl.children_with_tokens().any(|c| c.kind() == INOUT_KW);
            return Some((
                TokenSort::Parameter,
                DECLARATION | if inout { MUTABLE } else { 0 },
            ));
        }
        BIND_PAT => {
            let (sort, modifiers) = variable(token, context).unwrap_or_else(|| {
                let var = decl.ancestors().any(|a| a.kind() == VAR_STMT);
                (TokenSort::Variable, if var { MUTABLE } else { 0 })
            });
            return Some((sort, modifiers | DECLARATION));
        }
        _ => return Some(raw(token, context)),
    };
    Some((sort, DECLARATION))
}

/// A variable that checking resolved at the token's span, as a parameter or a local.
fn variable(token: &SyntaxToken, context: &Context) -> Option<(TokenSort, u32)> {
    let range = token.text_range();
    let &(param, mutable) = context
        .locals
        .get(&(range.start().into(), range.end().into()))?;
    let sort = if param {
        TokenSort::Parameter
    } else {
        TokenSort::Variable
    };
    Some((sort, if mutable { MUTABLE } else { 0 }))
}

/// A name that an expression writes alone.
fn named(
    token: &SyntaxToken,
    name_ref: &SyntaxNode,
    context: &Context,
) -> Option<(TokenSort, u32)> {
    if let Some(found) = variable(token, context) {
        return Some(found);
    }
    let parent = name_ref.parent()?;
    if parent.kind() == FIELD_INIT && parent.first_child().as_ref() == Some(name_ref) {
        return Some((TokenSort::Field, 0));
    }
    if token.kind() == UPPER_IDENT {
        return Some(upper(token, context));
    }
    if context.modules.contains(token.text()) {
        return Some((TokenSort::Module, 0));
    }
    // A primitive type, as the receiver of its own functions and constants, as `i64.MIN`.
    if stilt_hir::scope::is_primitive(token.text()) {
        return Some((TokenSort::Type, LIBRARY));
    }
    // A lowercase name that is neither a variable nor a module names a function, called or
    // not (lexical.case).
    Some((TokenSort::Function, 0))
}

/// Whether a node is what a call calls.
fn is_callee(node: &SyntaxNode) -> bool {
    node.parent()
        .is_some_and(|p| p.kind() == CALL_EXPR && p.first_child().as_ref() == Some(node))
}

/// A segment of a written path: a module before a `.`, and its last segment by where the path
/// stands.
fn path(token: &SyntaxToken, path: &SyntaxNode, context: &Context) -> Option<(TokenSort, u32)> {
    let holder = path.parent()?.kind();
    if matches!(holder, USE | HEADER) {
        return Some((TokenSort::Module, 0));
    }
    let last = path
        .children_with_tokens()
        .filter_map(stilt_syntax::SyntaxElement::into_token)
        .filter(|t| matches!(t.kind(), LOWER_IDENT | UPPER_IDENT))
        .last();
    if last.as_ref() != Some(token) {
        return Some((TokenSort::Module, 0));
    }
    let lower = token.kind() == LOWER_IDENT;
    Some(match holder {
        MACRO_USE => (TokenSort::Macro, 0),
        NAMED_TYPE if lower && stilt_hir::scope::is_primitive(token.text()) => {
            (TokenSort::Type, LIBRARY)
        }
        // A lowercase type argument that names no type is a value parameter
        // (generics.value-argument-names).
        NAMED_TYPE if lower => (TokenSort::Parameter, 0),
        BOUND | WHERE_BOUND => (TokenSort::Trait, 0),
        _ if lower && stilt_hir::scope::is_primitive(token.text()) => (TokenSort::Type, LIBRARY),
        _ if lower => (TokenSort::Function, 0),
        // A type's name, in a type, as `raise<Empty>` of `type Empty = | Empty(i64)`.
        NAMED_TYPE | ROW_EFFECT | ROW_RAISE => named_type(token.text(), context),
        _ => upper(token, context),
    })
}

/// The name after a `.`: a module's item, a type's variant or function, a method a call calls,
/// or a field.
fn member(token: &SyntaxToken, field: &SyntaxNode, context: &Context) -> (TokenSort, u32) {
    let base = field.first_child();
    if token.kind() == UPPER_IDENT {
        return upper(token, context);
    }
    if base.as_ref().is_some_and(|b| {
        b.kind() == NAME_REF && context.modules.contains(b.text().to_string().as_str())
    }) {
        return (TokenSort::Function, 0);
    }
    if is_callee(field) {
        (TokenSort::Method, 0)
    } else {
        (TokenSort::Field, 0)
    }
}

/// A macro's fragment, `$cond`, or the kind a pattern gives it, `expr`.
fn fragment(token: &SyntaxToken) -> (TokenSort, u32) {
    let after_colon = before(token).is_some_and(|t| t.kind() == COLON);
    if after_colon {
        (TokenSort::Type, LIBRARY)
    } else {
        (TokenSort::Fragment, 0)
    }
}

/// A word the tree doesn't parse, in a macro's use or template or in code with a syntax error,
/// read by the tokens around it.
fn raw(token: &SyntaxToken, context: &Context) -> (TokenSort, u32) {
    if let Some(found) = variable(token, context) {
        return found;
    }
    if token.kind() == UPPER_IDENT {
        return upper(token, context);
    }
    if context.modules.contains(token.text()) {
        return (TokenSort::Module, 0);
    }
    let next = after(token);
    let called = next.as_ref().is_some_and(|t| {
        t.kind() == L_PAREN
            || t.kind() == BANG
            || (t.parent().is_some_and(|p| p.kind() == MACRO_GROUP) && t.text() == "(")
    });
    let dotted = before(token).is_some_and(|t| t.kind() == DOT);
    match (dotted, called) {
        (_, true) if next.is_some_and(|t| t.kind() == BANG) => (TokenSort::Macro, 0),
        (true, true) => (TokenSort::Method, 0),
        (true, false) => (TokenSort::Field, 0),
        (false, true) => (TokenSort::Function, 0),
        (false, false) => (TokenSort::Variable, 0),
    }
}

/// An uppercase name: before a `.`, which a type's or a trait's function or an effect's
/// operation follows, a trait, an effect, a type, or a variant or a constant of none of those
/// names; elsewhere it is a value, so a variant, a constant, a trait, an effect or a type, as
/// `Eq` names a variant in `ast.Eq` and a trait in `Eq.eq(a, b)`.
fn upper(token: &SyntaxToken, context: &Context) -> (TokenSort, u32) {
    let name = token.text();
    let value = || {
        if context.variants.contains(name) {
            Some((TokenSort::Variant, 0))
        } else if context.constants.contains(name) {
            Some((TokenSort::Variable, READONLY))
        } else {
            None
        }
    };
    let next = after(token).map(|t| t.kind());
    // A constructor or a variant's pattern: no type is called (declarations.constructors).
    if next == Some(L_PAREN) {
        return (TokenSort::Variant, 0);
    }
    let receiver = next == Some(DOT);
    let named = || {
        if context.traits.contains(name) {
            Some((TokenSort::Trait, 0))
        } else if context.effects.contains(name) {
            Some((TokenSort::Effect, 0))
        } else {
            None
        }
    };
    let found = if receiver {
        named().or_else(value)
    } else {
        value().or_else(named)
    };
    found.unwrap_or((TokenSort::Type, 0))
}

/// An uppercase name in a type: a trait, an effect or a type.
fn named_type(name: &str, context: &Context) -> (TokenSort, u32) {
    if context.traits.contains(name) {
        (TokenSort::Trait, 0)
    } else if context.effects.contains(name) {
        (TokenSort::Effect, 0)
    } else {
        (TokenSort::Type, 0)
    }
}

/// The token before `token` that isn't trivia.
fn before(token: &SyntaxToken) -> Option<SyntaxToken> {
    let mut t = token.prev_token()?;
    while t.kind().is_trivia() {
        t = t.prev_token()?;
    }
    Some(t)
}

/// The token after `token` that isn't trivia.
fn after(token: &SyntaxToken) -> Option<SyntaxToken> {
    let mut t = token.next_token()?;
    while t.kind().is_trivia() {
        t = t.next_token()?;
    }
    Some(t)
}
