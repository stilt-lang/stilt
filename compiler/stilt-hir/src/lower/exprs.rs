//! Expressions.

use stilt_diag::{Diagnostic, Edit, Fix, codes};
use stilt_syntax::ast::{self, AstNode};
use stilt_syntax::text::{number_text, string_value};
use stilt_syntax::{SyntaxKind as K, TextRange};

use super::control::in_loop;
use super::{Ctx, Meaning, Resolver};
use crate::hir::{
    Arg, BinaryOp, Expr, ExprKind, FieldInit, Ident, MemberOwner, Name, Segment, TypeRef, UnaryOp,
};
use crate::scope::{Kind, Namespace};

impl Resolver<'_> {
    /// The expression a path stands for: what its names refer to, then fields. In
    /// `Name.member`, `Name` is a type when it can be (declarations.name-lookup).
    fn value_path(&mut self, ctx: &Ctx, at: TextRange, path: &[Ident]) -> Expr {
        let expr = |kind| Expr { kind, at };
        let (m, last) = self.walk(ctx, Namespace::Values, "a value", true, path);
        let mut fields = &path[last + 1..];
        let as_type = m.as_type();
        let base = match (m, as_type, fields.split_first()) {
            (Meaning::Broken, ..) => return expr(ExprKind::Error),
            (Meaning::Local(v), ..) => ExprKind::Local(v),
            (Meaning::Value(g, t), ..) => ExprKind::ValueParam(g, t),
            (Meaning::Item(item, entry), ..)
                if !entry.kind.is_type() && !matches!(entry.kind, Kind::Macro | Kind::Proc) =>
            {
                match entry.kind {
                    Kind::Fn => ExprKind::Func(item),
                    Kind::Const => ExprKind::Const(item),
                    _ => ExprKind::Variant(item),
                }
            }
            (Meaning::Item(item, entry), _, Some((member, rest))) if entry.kind == Kind::Trait => {
                fields = rest;
                ExprKind::Member(MemberOwner::Trait(item), member.clone())
            }
            // handlers.performing-operation: an operation of an effect, which a call performs.
            (Meaning::Item(item, entry), _, Some((member, rest))) if entry.kind == Kind::Effect => {
                fields = rest;
                ExprKind::Perform(item, member.clone())
            }
            (_, Some(ty), Some((member, rest))) => {
                let ty = TypeRef {
                    ty,
                    at: path[last].at,
                };
                fields = rest;
                ExprKind::Member(MemberOwner::Type(ty), member.clone())
            }
            (m, ..) => {
                self.names_no_value(&m, &path[last]);
                return expr(ExprKind::Error);
            }
        };
        // Each part of the path but the whole spans its names, from the first.
        let part = |kind, upto: &Ident| Expr {
            kind,
            at: TextRange::new(path[0].at.start(), upto.at.end()),
        };
        let Some((outermost, inner)) = fields.split_last() else {
            return expr(base);
        };
        let names = path.len() - fields.len() - 1;
        let base = part(base, &path[names]);
        let inner = inner.iter().fold(base, |base, field| {
            part(ExprKind::Field(Box::new(base), field.clone()), field)
        });
        expr(ExprKind::Field(Box::new(inner), outermost.clone()))
    }

    /// The names of a path of identifiers, such as `fs.read` or `Self.new`.
    pub(super) fn path_of(&self, e: &ast::Expr) -> Option<Vec<Ident>> {
        match e {
            ast::Expr::NameRef(n) => Some(vec![self.ident(&n.ident()?)]),
            ast::Expr::SelfTypeExpr(s) => {
                let token = s.syntax().first_token()?;
                Some(vec![Ident {
                    name: Name::from("Self"),
                    at: self.at_token(&token),
                }])
            }
            ast::Expr::FieldExpr(f) => {
                let mut path = self.path_of(&f.base()?)?;
                path.push(self.ident(&f.member()?));
                Some(path)
            }
            ast::Expr::ParenExpr(p) => self.path_of(&p.expr()?),
            _ => None,
        }
    }

    pub(super) fn opt_expr(&mut self, ctx: &Ctx, e: Option<ast::Expr>) -> Expr {
        match e {
            Some(e) => self.expr(ctx, &e),
            None => Expr {
                kind: ExprKind::Error,
                at: TextRange::default(),
            },
        }
    }

    pub(super) fn boxed(&mut self, ctx: &Ctx, e: Option<ast::Expr>) -> Box<Expr> {
        Box::new(self.opt_expr(ctx, e))
    }

    /// The record an update copies (records.update). A key path there, as JavaScript's spread
    /// `{ ...p }` reads, is E0324, which says how Stilt spreads a record.
    fn update_base(&mut self, ctx: &Ctx, e: Option<ast::Expr>) -> Expr {
        let Some(ast::Expr::KeyPathExpr(k)) = &e else {
            return self.opt_expr(ctx, e);
        };
        let at = self.at(k.syntax());
        let message = "Stilt spreads a record with two dots, as `{ ..p, x: 3 }`".to_owned();
        let dot = TextRange::at(at.start(), 1.into());
        let d = Diagnostic::new(codes::E0324, at, message)
            .with_help("An update copies the record after `..` with the fields written changed.")
            .with_fix(Fix::new("write `..`", vec![Edit::delete(dot)]));
        self.diagnostics.push(d);
        Expr {
            kind: ExprKind::Error,
            at,
        }
    }

    /// `!e` or `-e`.
    fn prefix(&mut self, ctx: &Ctx, p: &ast::PrefixExpr) -> ExprKind {
        let not = p.op().is_some_and(|t| t.kind() == K::BANG);
        let op = if not { UnaryOp::Not } else { UnaryOp::Neg };
        ExprKind::Unary(op, self.boxed(ctx, p.expr()))
    }
}

impl Resolver<'_> {
    pub(super) fn expr(&mut self, ctx: &Ctx, e: &ast::Expr) -> Expr {
        use ast::Expr as E;
        if let E::ParenExpr(p) = e {
            return self.opt_expr(ctx, p.expr());
        }
        let at = self.at(e.syntax());
        if let Some(path) = self.path_of(e) {
            let missing = self.missing_value(ctx, e, &path);
            return missing.unwrap_or_else(|| self.value_path(ctx, at, &path));
        }
        let kind = match e {
            E::Literal(l) => literal(l),
            E::Interp(i) => self.interpolated(ctx, i),
            E::SelfExpr(_) => self.self_value(at),
            E::FieldExpr(f) => self.field_of(ctx, f),
            E::KeyPathExpr(k) => self.key_path(k, at),
            E::HoleExpr(_) => ExprKind::Hole,
            E::TupleExpr(t) => ExprKind::Tuple(self.exprs(ctx, t.exprs())),
            E::ListExpr(l) => ExprKind::List(self.exprs(ctx, l.exprs())),
            E::CallExpr(c) => self.call(ctx, c),
            E::IndexExpr(i) => {
                ExprKind::Index(self.boxed(ctx, i.base()), self.boxed(ctx, i.index()))
            }
            E::StructExpr(s) => self.struct_literal(ctx, s),
            E::RecordExpr(r) => self.record_literal(ctx, r, at),
            E::SpreadExpr(s) => ExprKind::Spread(self.boxed(ctx, s.expr())),
            E::PrefixExpr(p) => self.prefix(ctx, p),
            E::BinaryExpr(b) => self.binary(ctx, b),
            E::ElseExpr(x) => {
                let lhs = self.boxed(ctx, x.lhs());
                ExprKind::Else(lhs, self.boxed(ctx, x.rhs()))
            }
            E::TryExpr(t) => self.try_expr(ctx, t),
            E::RaiseExpr(r) => ExprKind::Raise(self.boxed(ctx, r.expr())),
            E::ReturnExpr(r) => ExprKind::Return(r.expr().map(|e| Box::new(self.expr(ctx, &e)))),
            E::BreakExpr(_) => self.jump(ctx, at, "break", ExprKind::Break),
            E::ContinueExpr(_) => self.jump(ctx, at, "continue", ExprKind::Continue),
            E::ClosureExpr(c) => self.closure(ctx, c),
            E::Block(b) => ExprKind::Block(self.block(ctx, Some(b.clone()))),
            E::IfExpr(i) => self.if_expr(ctx, i),
            E::MatchExpr(m) => self.match_expr(ctx, m),
            E::LoopExpr(l) => ExprKind::Loop(self.block(&in_loop(ctx), l.body())),
            E::WhileExpr(w) => self.while_loop(ctx, w),
            E::ForExpr(f) => self.for_loop(ctx, f),
            E::MacroUse(m) => return self.macro_expr(ctx, m, at),
            E::HandlerExpr(h) => self.handler_expr(ctx, h),
            E::WithExpr(w) => self.with_expr(ctx, w),
            E::ResumeExpr(r) => self.resume_expr(ctx, r),
            E::WhenExpr(w) => self.when_expr(ctx, w),
            // A staging annotation on its form (meta.staging-annotations), which the parser gives
            // only an `if`, a `match` or a `for`.
            E::ComptimeExpr(c) => ExprKind::Comptime(Box::new(self.opt_expr(ctx, c.form()))),
            E::QuoteExpr(q) => self.quote(ctx, q, at),
            E::UnsafeExpr(u) => self.unsafe_block(ctx, u, at),
            // A splice stands only in a quote, whose contents [`Resolver::quote`] reads.
            E::SpliceExpr(_)
            | E::SpliceSpread(_)
            | E::NameRef(_)
            | E::SelfTypeExpr(_)
            | E::ParenExpr(_) => ExprKind::Error,
        };
        Expr { kind, at }
    }

    /// E0212 at a name that a path ends with, which names no value: a procedural macro's is
    /// used only through `meta use` (macros.meta-use).
    fn names_no_value(&mut self, m: &Meaning, name: &Ident) {
        let message = match m {
            Meaning::Item(_, entry) if entry.kind == Kind::Proc => format!(
                "`{0}` is a procedural macro, used as `m.{0}!(…)` where `meta use` names its \
                 module `m`",
                name.name
            ),
            _ => format!("`{}` is {}, not a value", name.name, m.describe()),
        };
        self.error(codes::E0212, name.at, message);
    }

    /// A field of a value that isn't a path.
    fn field_of(&mut self, ctx: &Ctx, f: &ast::FieldExpr) -> ExprKind {
        let base = self.boxed(ctx, f.base());
        f.member()
            .map_or(ExprKind::Error, |m| ExprKind::Field(base, self.ident(&m)))
    }

    /// The start of a key path, a field of its root.
    fn key_path(&self, k: &ast::KeyPathExpr, at: TextRange) -> ExprKind {
        k.member().map_or(ExprKind::Error, |m| {
            let root = Box::new(Expr {
                kind: ExprKind::KeyRoot,
                at,
            });
            ExprKind::Field(root, self.ident(&m))
        })
    }

    fn exprs(&mut self, ctx: &Ctx, es: impl Iterator<Item = ast::Expr>) -> Vec<Expr> {
        es.map(|e| self.expr(ctx, &e)).collect()
    }

    fn interpolated(&mut self, ctx: &Ctx, i: &ast::Interp) -> ExprKind {
        let segments = i.parts().into_iter().filter_map(|part| match part {
            ast::InterpPart::Text(text) if text.is_empty() => None,
            ast::InterpPart::Text(text) => Some(Segment::Text(text)),
            ast::InterpPart::Splice(s) => {
                Some(Segment::Splice(self.opt_expr(ctx, s.expr()), s.spec()))
            }
        });
        ExprKind::Interpolated(segments.collect())
    }

    /// `self`, which only methods bind (traits.methods).
    fn self_value(&mut self, at: TextRange) -> ExprKind {
        match self.scope.iter().rev().find(|(n, _)| &**n == "self") {
            Some((_, Some(v))) => ExprKind::Local(*v),
            Some((_, None)) => ExprKind::Error,
            None => {
                self.error(codes::E0215, at, "`self` exists only in methods".to_owned());
                ExprKind::Error
            }
        }
    }

    fn call(&mut self, ctx: &Ctx, c: &ast::CallExpr) -> ExprKind {
        let callee = match self.foreign_callee(ctx, c) {
            Some(callee) => Box::new(callee),
            None => self.boxed(ctx, c.callee()),
        };
        let args = c
            .args()
            .map(|a| Arg {
                inout: a.is_inout(),
                value: self.opt_expr(ctx, a.expr()),
                at: self.at(a.syntax()),
            })
            .collect();
        ExprKind::Call(callee, args)
    }

    /// A struct literal, or an update of a declared record (records.update). A field without a
    /// value is the variable of its own name.
    fn struct_literal(&mut self, ctx: &Ctx, s: &ast::StructExpr) -> ExprKind {
        let path = self.path(s.path());
        let ty = self.record_ty(ctx, &path);
        let base = s.base().map(|b| Box::new(self.update_base(ctx, b.expr())));
        let fields = self.field_inits(ctx, s.fields());
        match base {
            Some(base) => ExprKind::Update(Some(ty), base, fields),
            None => ExprKind::Struct(ty, fields),
        }
    }

    /// An anonymous record literal, whose type is the anonymous record type of its fields' names,
    /// its types those of the values (records.anonymous-literals), or an update without a type
    /// (records.update).
    fn record_literal(&mut self, ctx: &Ctx, r: &ast::RecordExpr, at: TextRange) -> ExprKind {
        let base = r.base().map(|b| Box::new(self.update_base(ctx, b.expr())));
        let fields = self.field_inits(ctx, r.fields());
        if let Some(base) = base {
            return ExprKind::Update(None, base, fields);
        }
        let mut names: Vec<Name> = fields.iter().map(|f| f.field.name).collect();
        names.sort_by(|a, b| a.as_bytes().cmp(b.as_bytes()));
        names.dedup();
        let ty = TypeRef {
            ty: crate::hir::Ty::Con(crate::hir::Item::record(&names), Vec::new()),
            at,
        };
        ExprKind::Struct(ty, fields)
    }

    fn field_inits(
        &mut self,
        ctx: &Ctx,
        fields: impl Iterator<Item = ast::FieldInit>,
    ) -> Vec<FieldInit> {
        fields
            .map(|f| {
                let field = self.field(f.field(), f.syntax());
                let value = match f.value() {
                    Some(v) => self.expr(ctx, &v),
                    None => self.value_path(ctx, field.at, std::slice::from_ref(&field)),
                };
                FieldInit { field, value }
            })
            .collect()
    }

    fn binary(&mut self, ctx: &Ctx, b: &ast::BinaryExpr) -> ExprKind {
        let lhs = self.boxed(ctx, b.lhs());
        let rhs = self.boxed(ctx, b.rhs());
        match b.op().and_then(|t| binary_op(t.kind())) {
            Some(op) => ExprKind::Binary(op, lhs, rhs),
            None => ExprKind::Error,
        }
    }
}

/// A literal's value.
fn literal(l: &ast::Literal) -> ExprKind {
    match l.token() {
        Some(t) if t.kind() == K::INT => ExprKind::Int(number_text(&t)),
        Some(t) if t.kind() == K::FLOAT => ExprKind::Float(number_text(&t)),
        Some(t) if t.kind() == K::STRING => ExprKind::Str(string_value(&t)),
        Some(t) => ExprKind::Bool(t.kind() == K::TRUE_KW),
        None => ExprKind::Error,
    }
}

fn binary_op(kind: K) -> Option<BinaryOp> {
    use BinaryOp as B;
    Some(match kind {
        K::PLUS => B::Add,
        K::MINUS => B::Sub,
        K::STAR => B::Mul,
        K::SLASH => B::Div,
        K::PERCENT => B::Rem,
        K::PLUS_PERCENT => B::AddWrap,
        K::MINUS_PERCENT => B::SubWrap,
        K::STAR_PERCENT => B::MulWrap,
        K::EQ2 => B::Eq,
        K::NEQ => B::Ne,
        K::L_ANGLE => B::Lt,
        K::LTEQ => B::Le,
        K::R_ANGLE => B::Gt,
        K::GTEQ => B::Ge,
        K::AMP2 => B::And,
        K::PIPE2 => B::Or,
        K::AMP => B::BitAnd,
        K::PIPE => B::BitOr,
        K::CARET => B::BitXor,
        K::SHL => B::Shl,
        K::SHR => B::Shr,
        _ => return None,
    })
}
