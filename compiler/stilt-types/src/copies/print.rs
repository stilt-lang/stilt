//! The print of a typed body, which two bodies share exactly when they are the same body
//! (docs.same-body): each construct with its literals, operators, fields, modes of arguments
//! and format specs; each declaration it names; each local by its number, in the order the
//! body binds them, its parameters first, with its type; and each literal's and type
//! argument's type, type parameters by name and function types without their rows.

use std::collections::HashMap;
use std::fmt::Write as _;

use stilt_hir::hir::{GenericId, Item, ListRest, LocalId, Name};

use crate::tast::{
    Arg, Arm, Binding, Block, Callee, Catch, Expr, ExprKind, Iterable, Pat, PatKind, Segment,
    StmtKind, TypedBody,
};
use crate::ty::Ty;

mod handlers;

/// Writes the print of a body.
struct Printer<'a> {
    out: String,
    locals: HashMap<LocalId, usize>,
    names: &'a dyn Fn(&GenericId) -> Name,
}

/// The print of a function's typed body, whose block is `block`.
pub(super) fn print(body: &TypedBody, block: &Block, names: &dyn Fn(&GenericId) -> Name) -> String {
    let mut p = Printer {
        out: String::new(),
        locals: HashMap::new(),
        names,
    };
    for &(_, local) in &body.params {
        p.local(local);
    }
    p.block(block);
    p.out
}

impl Printer<'_> {
    fn tag(&mut self, tag: &str) {
        self.out.push_str(tag);
        self.out.push(' ');
    }

    fn local(&mut self, id: LocalId) {
        let next = self.locals.len();
        let n = *self.locals.entry(id).or_insert(next);
        let _ = write!(self.out, "l{n} ");
    }

    fn item(&mut self, item: &Item) {
        let _ = write!(self.out, "{}.{} ", item.home, item.name);
    }

    fn text(&mut self, text: &str) {
        let _ = write!(self.out, "{text:?} ");
    }

    fn ty(&mut self, ty: &Ty) {
        match ty {
            Ty::Con(item, args) => {
                self.item(item);
                self.tys(args);
            }
            Ty::Param(id) => {
                let name = (self.names)(id);
                let _ = write!(self.out, "'{name} ");
            }
            Ty::SelfTy => self.tag("Self"),
            Ty::Value(v) => {
                let _ = write!(self.out, "#{v} ");
            }
            Ty::App(head, args) => {
                self.tag("app");
                self.ty(head);
                self.tys(args);
            }
            Ty::Tuple(items) => {
                self.tag("tuple");
                self.tys(items);
            }
            Ty::Fn(f) => {
                self.tag("fn");
                for (mode, param) in &f.params {
                    let _ = write!(self.out, "{mode:?} ");
                    self.ty(param);
                }
                self.tag("->");
                self.ty(&f.ret);
            }
            Ty::Spread(s) => {
                self.tag("..");
                self.ty(&s.pack);
                let name = (self.names)(&s.of);
                let _ = write!(self.out, "'{name} ");
                self.ty(&s.elem);
            }
            Ty::Handler(h) => {
                self.tag("handler");
                self.item(&h.effect);
                self.tys(&h.args);
                if let Some(answer) = &h.answer {
                    self.tag("->");
                    self.ty(answer);
                }
            }
            Ty::Var(_) => self.tag("_"),
            Ty::Error => self.tag("!"),
        }
    }

    fn tys(&mut self, tys: &[Ty]) {
        self.tag("<");
        for ty in tys {
            self.ty(ty);
        }
        self.tag(">");
    }

    fn callee(&mut self, callee: &Callee) {
        match callee {
            Callee::Function(item) => self.item(item),
            Callee::Member(item, name) => {
                self.item(item);
                self.text(name);
            }
            Callee::TraitMethod(item, name, ty) => {
                self.item(item);
                self.text(name);
                self.ty(ty);
            }
            Callee::Operation(item, name) => {
                self.tag("perform");
                self.item(item);
                self.text(name);
            }
        }
    }

    fn block(&mut self, block: &Block) {
        self.tag("{");
        for stmt in block {
            match &stmt.kind {
                StmtKind::Let(b) => self.binding("let", b),
                StmtKind::Var(b) => self.binding("var", b),
                StmtKind::Assign(op, place, value) => {
                    let _ = write!(self.out, "assign {op:?} ");
                    self.expr(place);
                    self.expr(value);
                }
                StmtKind::Assert(e) => {
                    self.tag("assert");
                    self.expr(e);
                }
                StmtKind::Yield(e) => {
                    self.tag("yield");
                    self.expr(e);
                }
                StmtKind::Expr(e) => self.expr(e),
            }
        }
        self.tag("}");
    }

    fn binding(&mut self, tag: &str, b: &Binding) {
        self.tag(tag);
        self.expr(&b.value);
        self.pat(&b.pattern);
        if let Some(otherwise) = &b.otherwise {
            self.tag("else");
            self.expr(otherwise);
        }
    }

    fn exprs(&mut self, exprs: &[Expr]) {
        self.tag("(");
        for e in exprs {
            self.expr(e);
        }
        self.tag(")");
    }

    fn args(&mut self, args: &[Arg]) {
        self.tag("(");
        for arg in args {
            let _ = write!(self.out, "{:?} ", arg.mode);
            self.expr(&arg.value);
        }
        self.tag(")");
    }

    fn expr(&mut self, e: &Expr) {
        match &e.kind {
            ExprKind::Int(text) | ExprKind::Float(text) => {
                self.text(&text.replace('_', ""));
                self.ty(&e.ty);
            }
            ExprKind::Str(text) => self.text(text),
            ExprKind::Interpolated(segments) => self.segments(segments),
            ExprKind::Bool(b) => self.tag(if *b { "true" } else { "false" }),
            ExprKind::Local(id) => {
                self.local(*id);
                self.ty(&e.ty);
            }
            ExprKind::Instantiate(value, tys) => {
                self.tag("instantiate");
                self.expr(value);
                self.tys(tys);
            }
            _ => self.compound(e),
        }
    }

    fn segments(&mut self, segments: &[Segment]) {
        self.tag("\"");
        for segment in segments {
            match segment {
                Segment::Text(text) => self.text(text),
                Segment::Splice(e, spec) => {
                    self.expr(e);
                    self.text(spec.as_deref().unwrap_or(""));
                }
            }
        }
        self.tag("\"");
    }

    fn compound(&mut self, e: &Expr) {
        match &e.kind {
            ExprKind::Constant(item) => {
                self.tag("const");
                self.item(item);
            }
            ExprKind::MemberConstant(item, name, tys) => {
                self.tag("member");
                self.item(item);
                self.text(name);
                self.tys(tys);
            }
            ExprKind::Callee(callee, tys) => {
                self.tag("fnval");
                self.callee(callee);
                self.tys(tys);
            }
            ExprKind::Constructor(item, tys) => {
                self.tag("ctor");
                self.item(item);
                self.tys(tys);
            }
            ExprKind::Construct(item, tys, args) => {
                self.tag("construct");
                self.item(item);
                self.tys(tys);
                self.exprs(args);
            }
            ExprKind::Record(item, tys, fields) => {
                self.tag("record");
                self.item(item);
                self.tys(tys);
                for (name, value) in fields {
                    self.text(name);
                    self.expr(value);
                }
                self.tag("end");
            }
            ExprKind::Tuple(items) => {
                self.tag("tuple");
                self.exprs(items);
            }
            ExprKind::List(items) => {
                self.tag("list");
                self.exprs(items);
            }
            ExprKind::Field(of, name) => {
                self.tag("field");
                self.expr(of);
                self.text(name);
            }
            ExprKind::TupleField(of, n) => {
                let _ = write!(self.out, "field{n} ");
                self.expr(of);
            }
            _ => self.call_or_control(e),
        }
    }

    fn call_or_control(&mut self, e: &Expr) {
        match &e.kind {
            ExprKind::Call(callee, tys, args, _) => {
                self.tag("call");
                self.callee(callee);
                self.tys(tys);
                self.args(args);
            }
            ExprKind::Project(callee, tys, args, _) => {
                self.tag("project");
                self.callee(callee);
                self.tys(tys);
                self.args(args);
            }
            ExprKind::CallValue(f, args) => {
                self.tag("callvalue");
                self.expr(f);
                self.args(args);
            }
            ExprKind::Index(of, at) => {
                self.tag("index");
                self.expr(of);
                self.expr(at);
            }
            ExprKind::Unary(op, operand) => {
                let _ = write!(self.out, "{op:?} ");
                self.expr(operand);
            }
            ExprKind::Binary(op, left, right) => {
                let _ = write!(self.out, "{op:?} ");
                self.expr(left);
                self.expr(right);
            }
            ExprKind::Else(value, otherwise) => {
                self.tag("else");
                self.expr(value);
                self.expr(otherwise);
            }
            ExprKind::Try(operand, catch) => {
                self.tag("try");
                self.expr(operand);
                if let Some(catch) = catch {
                    self.catch(catch);
                }
                self.tag("end");
            }
            ExprKind::Raise(value) => {
                self.tag("raise");
                self.expr(value);
            }
            ExprKind::Return(value) => {
                self.tag("return");
                if let Some(value) = value {
                    self.expr(value);
                }
                self.tag("end");
            }
            _ => self.control(e),
        }
    }

    fn control(&mut self, e: &Expr) {
        match &e.kind {
            ExprKind::Break => self.tag("break"),
            ExprKind::Continue => self.tag("continue"),
            ExprKind::Closure(params, body) => {
                self.tag("closure");
                for p in params {
                    self.pat(p);
                }
                self.expr(body);
            }
            ExprKind::Block(block) => self.block(block),
            ExprKind::If(cond, then, otherwise) => {
                self.tag("if");
                self.expr(cond);
                self.branches(then, otherwise.as_deref());
            }
            ExprKind::IfLet(pat, scrutinee, then, otherwise) => {
                self.tag("iflet");
                self.expr(scrutinee);
                self.pat(pat);
                self.branches(then, otherwise.as_deref());
            }
            ExprKind::Match(scrutinee, arms) => {
                self.tag("match");
                self.expr(scrutinee);
                self.arms(arms);
            }
            ExprKind::Loop(block) => {
                self.tag("loop");
                self.block(block);
            }
            ExprKind::While(cond, block) => {
                self.tag("while");
                self.expr(cond);
                self.block(block);
            }
            ExprKind::For(pat, iterable, block) => {
                self.tag("for");
                match &**iterable {
                    Iterable::Iter(e) => self.expr(e),
                    Iterable::Range(from, to, inclusive) => {
                        let _ = write!(self.out, "range{inclusive} ");
                        self.expr(from);
                        self.expr(to);
                    }
                }
                self.pat(pat);
                self.block(block);
            }
            ExprKind::Hole => self.tag("?"),
            _ => self.handling(e),
        }
    }

    /// The block of an `if` or an `if let`, then its `else`.
    fn branches(&mut self, then: &Block, otherwise: Option<&Expr>) {
        self.block(then);
        if let Some(otherwise) = otherwise {
            self.tag("else");
            self.expr(otherwise);
        }
        self.tag("end");
    }

    fn catch(&mut self, catch: &Catch) {
        self.tag("catch");
        self.ty(&catch.error);
        self.arms(&catch.arms);
    }

    fn arms(&mut self, arms: &[Arm]) {
        for arm in arms {
            self.tag("arm");
            self.pat(&arm.pattern);
            if let Some(guard) = &arm.guard {
                self.tag("if");
                self.expr(guard);
            }
            self.tag(if arm.because { "because" } else { "=>" });
            self.expr(&arm.body);
        }
        self.tag("end");
    }

    fn pats(&mut self, pats: &[Pat]) {
        self.tag("(");
        for p in pats {
            self.pat(p);
        }
        self.tag(")");
    }

    fn pat(&mut self, p: &Pat) {
        match &p.kind {
            PatKind::Wild => self.tag("_"),
            PatKind::Bind(id) => {
                self.local(*id);
                self.ty(&p.ty);
            }
            PatKind::Int(text) => {
                self.text(&text.replace('_', ""));
                self.ty(&p.ty);
            }
            PatKind::Str(text) => self.text(text),
            PatKind::Bool(b) => self.tag(if *b { "true" } else { "false" }),
            PatKind::Tuple(items) => {
                self.tag("tuple");
                self.pats(items);
            }
            PatKind::Const(e) => {
                self.tag("const");
                self.expr(e);
            }
            PatKind::Variant(item, payload) => {
                self.tag("variant");
                self.item(item);
                self.pats(payload);
            }
            PatKind::Record(fields) => {
                self.tag("record");
                for (name, field) in fields {
                    self.text(name);
                    self.pat(field);
                }
                self.tag("end");
            }
            PatKind::List(items, rest) => {
                self.tag("list");
                self.pats(items);
                match rest {
                    ListRest::Exact => self.tag("exact"),
                    ListRest::Rest => self.tag(".."),
                    ListRest::Bind(id) => {
                        self.tag("..");
                        self.local(*id);
                    }
                }
            }
            PatKind::Or(alternatives) => {
                self.tag("or");
                self.pats(alternatives);
            }
            PatKind::Error => self.tag("!"),
        }
    }
}
