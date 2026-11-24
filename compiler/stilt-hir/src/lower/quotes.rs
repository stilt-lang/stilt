//! Quotes (macros.quote, macros.splices and macros.quote-hygiene): a quote's contents are resolved
//! where it is written, among the bindings it makes and the items and imports of its module, never
//! the locals of the code around it, which its splices name; its splices are that code, resolved
//! there; and the quote keeps its tokens, which a macro's run fills.

use stilt_syntax::ast::{self, AnySplice, AstNode, QuoteForm};
use stilt_syntax::forms::read_tokens;
use stilt_syntax::{SyntaxKind, SyntaxNode, TextRange};

use super::patterns::Binder;
use super::poly::Spot;
use super::{Ctx, Resolver};
use crate::hir::walk::{Visitor, walk_block, walk_expr};
use crate::hir::{CodeForm, Expr, ExprKind, Item, Name, Place, Quote, QuoteTok, Splice};

impl Resolver<'_> {
    /// A quote, whose module is in the meta tier (macros.meta-tier).
    pub(super) fn quote(&mut self, ctx: &Ctx, q: &ast::QuoteExpr, at: TextRange) -> ExprKind {
        let form = match q.form() {
            QuoteForm::Block => CodeForm::Expr,
            QuoteForm::Type => CodeForm::Type,
            QuoteForm::Pattern => CodeForm::Pattern,
            QuoteForm::Field => CodeForm::Field,
        };
        let found = splices_of(q.syntax());
        let names = self.quoted(q);
        let splices = found
            .iter()
            .map(|(place, s)| Splice {
                place: *place,
                spread: matches!(s, AnySplice::Spread(_)),
                at: self.at(s.syntax()),
                value: self.opt_expr(ctx, s.value()),
            })
            .collect();
        let tokens = quote_tokens(q, &found);
        let written = q
            .syntax()
            .text()
            .to_string()
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ");
        ExprKind::Quote(Box::new(Quote {
            home: self.home(at).0,
            form,
            tokens,
            splices,
            written,
            names,
        }))
    }

    /// Resolves a quote's contents in a scope of their own, where the locals of the code around
    /// them are unknown, a `break` or a `continue` may stand, and no use expands, each splice
    /// standing for a form of its place (macros.quote-hygiene). The locals it binds are no locals
    /// of the body. Gives the functions the contents name (macros.expansion-effects).
    fn quoted(&mut self, q: &ast::QuoteExpr) -> Vec<Item> {
        let outer = std::mem::take(&mut self.scope);
        let names: Vec<Name> = outer.iter().map(|(n, _)| *n).collect();
        let quoting = self.quoting.replace(names);
        let checking = std::mem::replace(&mut self.checking, true);
        let locals = self.locals.len();
        let ctx = Ctx {
            in_loop: true,
            ..Ctx::module()
        };
        let mut names = Named(Vec::new());
        match q.form() {
            QuoteForm::Block => walk_block(&mut names, &self.block(&ctx, q.block())),
            QuoteForm::Type => {
                self.ty_in(&ctx, q.ty(), Spot::Local);
            }
            QuoteForm::Pattern => {
                let p = self.pattern(&ctx, &mut Binder::default(), q.pattern());
                names.pat(&p);
            }
            QuoteForm::Field => {
                if let Some(f) = q.field() {
                    names.expr(&self.quoted_field(&ctx, &f));
                }
            }
        }
        self.locals.truncate(locals);
        self.checking = checking;
        self.quoting = quoting;
        self.scope = outer;
        names.0
    }

    /// The field of `quote field { … }`: its value, or the variable its name names.
    fn quoted_field(&mut self, ctx: &Ctx, f: &ast::FieldInit) -> Expr {
        match (f.value(), f.field()) {
            (Some(v), _) => self.expr(ctx, &v),
            (None, Some(name)) => self.expr(ctx, &ast::Expr::NameRef(name)),
            (None, None) => Expr {
                kind: ExprKind::Error,
                at: self.at(f.syntax()),
            },
        }
    }
}

/// The splices of a quote, in the order written, each with its place, but for those of the
/// quotes inside it and of the code its splices hold.
fn splices_of(quote: &SyntaxNode) -> Vec<(Place, AnySplice)> {
    let mut found = Vec::new();
    let mut walk = quote.preorder();
    while let Some(event) = walk.next() {
        let rowan::WalkEvent::Enter(node) = event else {
            continue;
        };
        if node.kind() == SyntaxKind::QUOTE_EXPR && node != *quote {
            walk.skip_subtree();
        } else if let Some(s) = AnySplice::cast(node.clone()) {
            found.push((place_of(&s), s));
            walk.skip_subtree();
        }
    }
    found
}

/// Where a splice stands, by its node and its parent's.
fn place_of(s: &AnySplice) -> Place {
    match s {
        AnySplice::Expr(_) => Place::Expr,
        AnySplice::Pat(_) => Place::Pattern,
        AnySplice::Type(_) => Place::Type,
        AnySplice::Name(_) => Place::Name,
        AnySplice::Spread(n) => match n.syntax().parent().map(|p| p.kind()) {
            Some(SyntaxKind::RECORD_EXPR | SyntaxKind::STRUCT_EXPR | SyntaxKind::QUOTE_EXPR) => {
                Place::Fields
            }
            _ => Place::Elements,
        },
    }
}

/// A quote's tokens, between the braces that hold its contents, as the parser reads them, each
/// splice's tokens one [`QuoteTok::Splice`].
fn quote_tokens(q: &ast::QuoteExpr, splices: &[(Place, AnySplice)]) -> Vec<QuoteTok> {
    let Some((open, close)) = q.brackets() else {
        return Vec::new();
    };
    let start = open.text_range().end();
    let end = close.text_range().start();
    let Some(text) = q
        .syntax()
        .ancestors()
        .last()
        .map(|root| root.text().slice(TextRange::new(start, end)).to_string())
    else {
        return Vec::new();
    };
    let Some(read) = read_tokens(&text) else {
        return Vec::new();
    };
    let ranges: Vec<TextRange> = splices
        .iter()
        .map(|(_, s)| s.syntax().text_range() - start)
        .collect();
    let mut tokens = Vec::with_capacity(read.len());
    let mut last = None;
    let mut read = read.into_iter().peekable();
    while let Some((kind, range)) = read.next() {
        let in_splice = |at: TextRange| ranges.iter().any(|r| r.contains(at.start()));
        if kind == SyntaxKind::MINUS
            && let Some(&(number @ (SyntaxKind::INT | SyntaxKind::FLOAT), digits)) = read.peek()
            && digits.start() == range.end()
            && !in_splice(range)
            && !in_splice(digits)
        {
            tokens.push(QuoteTok::Negative(number, Name::from(&text[digits])));
            read.next();
            last = None;
            continue;
        }
        match ranges.iter().position(|r| r.contains(range.start())) {
            Some(i) if last == Some(i) => {}
            Some(i) => {
                tokens.push(QuoteTok::Splice(u32::try_from(i).unwrap_or(u32::MAX)));
                last = Some(i);
            }
            None => {
                let spelled = if kind == SyntaxKind::SEP {
                    ";"
                } else {
                    &text[range]
                };
                tokens.push(QuoteTok::Token(kind, Name::from(spelled)));
                last = None;
            }
        }
    }
    tokens
}

/// The functions that a quote's contents name, each once, with those of the quotes inside them.
struct Named(Vec<Item>);

impl Named {
    fn add(&mut self, item: &Item) {
        if !self.0.contains(item) {
            self.0.push(item.clone());
        }
    }
}

impl Visitor for Named {
    fn expr(&mut self, e: &Expr) {
        match &e.kind {
            ExprKind::Func(item) => self.add(item),
            ExprKind::Quote(q) => {
                for item in &q.names {
                    self.add(item);
                }
            }
            _ => {}
        }
        walk_expr(self, e);
    }
}
