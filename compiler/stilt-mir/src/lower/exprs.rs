//! Expressions that compute a value without deciding what runs next: literals, locals,
//! constants, constructions, fields, indexing and operators. Each gives the words of
//! its value's layout (`crate::layout`).

use stilt_hir::decls::Lookup;
use stilt_hir::hir::{BinaryOp, Item, UnaryOp};
use stilt_types::tast::{Expr, ExprKind};
use stilt_types::ty::Ty;
use stilt_types::verify::Check;

use super::numeric::{float_literal, int_literal};
use super::words::word;
use super::{Lower, projections};
use crate::FnRef;
use crate::mir::{Const, Heapness, NumKind, Operand, Prim, Repr, Runtime, Rvalue, Terminator};
use crate::repr::num_kind;

/// The value of a variant without a payload, and the tag of every variant held inline: an
/// immediate.
pub(crate) const fn immediate(index: u32) -> u64 {
    (index as u64) << 1 | 1
}

impl Lower<'_> {
    /// Lowers an expression, and returns the words of its value. After an expression of type
    /// `Never`, the code being built is unreachable, and the value is a placeholder.
    pub(crate) fn expr(&mut self, e: &Expr) -> Vec<Operand> {
        // A value evaluated before the projections of its construct opened (`projections`).
        if let Some((words, _)) = self.evaluated.get(&projections::node(e)) {
            return words.clone();
        }
        match &e.kind {
            ExprKind::Int(text) => {
                vec![Operand::Const(Const::Word(int_literal(text, false, &e.ty)))]
            }
            ExprKind::Float(text) => vec![Operand::Const(Const::Word(float_literal(text, &e.ty)))],
            ExprKind::Str(s) => vec![Operand::Const(Const::Str(s.as_str().into()))],
            ExprKind::Bool(b) => vec![Operand::word(u64::from(*b))],
            ExprKind::Interpolated(segments) => vec![self.interpolated(segments)],
            ExprKind::Local(id) => self.read_var(*id, &e.ty),
            ExprKind::Constant(item) => self.constant(&FnRef::Const(item.clone()), &e.ty, e),
            ExprKind::MemberConstant(owner, name, _) => self.member_constant(owner, name, e),
            ExprKind::ValueParam(g) => vec![self.value_param(&Ty::Param(g.clone()))],
            // A generic function given for a polymorphic function type (polymorphism.arguments).
            ExprKind::Callee(callee, targs) if e.ty.is_poly() => {
                vec![self.poly_function_value(callee, targs, e)]
            }
            ExprKind::Callee(callee, targs) => vec![self.function_value(callee, targs, e)],
            ExprKind::Instantiate(f, targs) => vec![self.instantiated_value(f, targs, e)],
            ExprKind::Constructor(item, targs) => vec![self.constructor_value(item, targs)],
            ExprKind::Construct(item, _, args) => self.construct(item, args, &e.ty),
            ExprKind::Record(_, _, fields) => self.record(fields, &e.ty),
            ExprKind::Update(base, fields) => self.update(base, fields, &e.ty),
            ExprKind::Spread(_) => self.stray_spread(),
            ExprKind::Tuple(es) => self.tuple(es, &e.ty),
            ExprKind::List(es) => self.list(es, &e.ty),
            ExprKind::Field(base, name) => self
                .read_element_part(e)
                .unwrap_or_else(|| self.field(base, name)),
            ExprKind::TupleField(base, i) => self
                .read_element_part(e)
                .unwrap_or_else(|| self.tuple_field(base, *i)),
            ExprKind::Call(_, _, args, _) | ExprKind::CallValue(_, args)
                if projections::Plan::needs(self, args) =>
            {
                self.call_through(args, e)
            }
            ExprKind::Call(callee, targs, args, row) => self.call(callee, targs, args, row, e),
            // A value of a polymorphic function type is called at its instantiation.
            ExprKind::CallValue(f, args) => match &f.kind {
                ExprKind::Instantiate(g, targs) if g.ty.is_poly() => {
                    self.call_poly(g, targs, args, e)
                }
                _ => self.call_value(f, args, e),
            },
            ExprKind::Project(..) => self.project_read(e),
            ExprKind::Index(container, key) => self.index(container, key, e),
            ExprKind::Unary(op, x) => vec![self.unary(*op, x, e)],
            ExprKind::Binary(op, a, b) => vec![self.binary(*op, a, b, e)],
            ExprKind::Reflect(..) | ExprKind::Bound(..) => self.reflection(e),
            ExprKind::Quote(q) => self.quote(q),
            ExprKind::Hole => vec![self.panic(8, None, self.loc_at(e.at))],
            ExprKind::Error => {
                self.b.terminate(Terminator::Unreachable);
                vec![Operand::word(0)]
            }
            _ => self.control(e),
        }
    }

    /// A quote outside a macro's run, which evaluates its splices, left to right, and makes its
    /// code, whatever their values (macros.outside-run). No observable of a run shows code, so it
    /// is held as the quote's text.
    fn quote(&mut self, q: &stilt_types::tast::Quote) -> Vec<Operand> {
        for s in &q.splices {
            self.expr(&s.value);
        }
        vec![Operand::Const(Const::Str(q.written.as_str().into()))]
    }

    /// Lowers an expression whose value is one word, and returns it.
    pub(crate) fn expr1(&mut self, e: &Expr) -> Operand {
        word(&self.expr(e), 0)
    }

    /// Ends the code here with a panic of the runtime's kind number `kind`.
    pub(crate) fn panic(&mut self, kind: u64, detail: Option<Operand>, loc: Operand) -> Operand {
        self.b.terminate(Terminator::Panic { kind, detail, loc });
        Operand::word(0)
    }

    /// A constant's value, computed where it is first used (declarations.constant-evaluation),
    /// which the program keeps in the words of its layout.
    fn constant(&mut self, f: &FnRef, ty: &Ty, e: &Expr) -> Vec<Operand> {
        let loc = self.loc_at(e.at);
        let layout: std::sync::Arc<[Repr]> = self.layout(ty).into();
        let safe = super::constants::cannot_panic(self.cx, f);
        (0..layout.len())
            .map(|k| {
                let k32 = u32::try_from(k).expect("under 4G words");
                let word = Rvalue::Constant(f.clone(), loc.clone(), k32, layout.clone(), safe);
                self.b.define_op(layout[k], word)
            })
            .collect()
    }

    fn member_constant(&mut self, owner: &Item, name: &str, e: &Expr) -> Vec<Operand> {
        let kind = num_kind(&Ty::Con(owner.clone(), Vec::new()));
        let w = match (kind, name) {
            (Some(NumKind::F32), "NAN") => u64::from(f32::NAN.to_bits()),
            (Some(NumKind::F32), "INFINITY") => u64::from(f32::INFINITY.to_bits()),
            (Some(_), "NAN") => f64::NAN.to_bits(),
            (Some(_), "INFINITY") => f64::INFINITY.to_bits(),
            _ => return self.constant(&FnRef::MemberConst(owner.clone(), name.into()), &e.ty, e),
        };
        vec![Operand::word(w)]
    }

    /// A data object, or a static one when every field is a constant.
    pub(crate) fn alloc(&mut self, tag: u16, fields: Vec<(Operand, Heapness)>) -> Operand {
        let constant: Option<Vec<(Const, bool)>> = fields
            .iter()
            .map(|(v, h)| match (v, h) {
                (Operand::Const(c), Heapness::Static(heap)) => Some((c.clone(), *heap)),
                _ => None,
            })
            .collect();
        match constant {
            Some(fields) => Operand::Const(Const::Data(tag, fields)),
            None => self.b.define_op(Repr::Heap, Rvalue::Alloc(tag, fields)),
        }
    }

    /// The index of a variant among its type's variants.
    pub(crate) fn variant_index(&self, variant: &Item) -> u32 {
        self.decls().variant(variant).map_or(0, |v| v.index)
    }

    fn construct(&mut self, item: &Item, args: &[Expr], ty: &Ty) -> Vec<Operand> {
        let index = self.variant_index(item) as usize;
        let values = args.iter().map(|a| self.expr(a)).collect();
        self.build(ty, index, values)
    }

    /// The fields of a record type, in declaration order.
    pub(crate) fn field_names(&self, item: &Item) -> Vec<stilt_hir::hir::Name> {
        match self.decls().type_info(item).map(|t| &t.def) {
            Some(stilt_hir::decls::TypeDefInfo::Record(fields)) => {
                fields.iter().map(|(n, _)| *n).collect()
            }
            // A view's words, which a debugger shows by these names (`crate::layout`).
            Some(stilt_hir::decls::TypeDefInfo::Builtin)
                if stilt_types::ty::is_view_type(item, "View") =>
            {
                ["source", "start", "end"]
                    .map(stilt_hir::hir::Name::from)
                    .to_vec()
            }
            _ => Vec::new(),
        }
    }

    /// The position of a field among its record's.
    pub(crate) fn field_index(&self, ty: &Ty, name: &str) -> usize {
        match ty {
            Ty::Con(item, _) => self
                .field_names(item)
                .iter()
                .position(|n| &**n == name)
                .unwrap_or(0),
            _ => 0,
        }
    }

    /// Evaluated as written, stored as declared (values.left-to-right).
    fn record(&mut self, given: &[(stilt_hir::hir::Name, Expr)], ty: &Ty) -> Vec<Operand> {
        let values: Vec<(stilt_hir::hir::Name, Vec<Operand>)> =
            given.iter().map(|(n, x)| (*n, self.expr(x))).collect();
        let declared = match ty {
            Ty::Con(item, _) => self.field_names(item),
            _ => Vec::new(),
        };
        let in_order = declared
            .iter()
            .map(|n| {
                values
                    .iter()
                    .find(|(m, _)| m == n)
                    .map_or_else(|| vec![Operand::word(0)], |(_, v)| v.clone())
            })
            .collect();
        self.build(ty, 0, in_order)
    }

    /// Each spread among the elements gives one for each of its pack's
    /// (variadics.spread-expressions).
    fn tuple(&mut self, es: &[Expr], ty: &Ty) -> Vec<Operand> {
        if super::packs::is_dynamic_tuple(ty) {
            return self.dynamic_tuple(es);
        }
        let values: Vec<Vec<Operand>> = self
            .element_values(es)
            .into_iter()
            .map(|(v, _)| v)
            .collect();
        if values.is_empty() {
            return vec![Operand::word(0)];
        }
        self.build(ty, 0, values)
    }

    /// A list literal: a list, or where an array is expected, an array (generics.array-literals).
    fn list(&mut self, es: &[Expr], ty: &Ty) -> Vec<Operand> {
        if ty.arrayed().is_some() {
            return self.array_literal(es, ty);
        }
        if self.spreads_dynamic(es) {
            return vec![self.dynamic_list(es, ty)];
        }
        let values = self
            .element_values(es)
            .into_iter()
            .map(|(v, _)| v)
            .collect();
        vec![self.list_literal(values, ty)]
    }

    fn field(&mut self, base: &Expr, name: &str) -> Vec<Operand> {
        let b = self.expr(base);
        let j = self.field_index(&base.ty, name);
        let fields = self.fields_of(&base.ty, 0);
        self.field_words(&b, &fields, j)
    }

    fn tuple_field(&mut self, base: &Expr, i: usize) -> Vec<Operand> {
        let b = self.expr(base);
        let fields = self.fields_of(&base.ty, 0);
        self.field_words(&b, &fields, i)
    }

    /// `c[k]`, of a list, a map or an array (std.lists and std.maps; generics.array-elements).
    fn index(&mut self, container: &Expr, key: &Expr, e: &Expr) -> Vec<Operand> {
        if container.ty.viewed().is_some() {
            return self.view_index(container, key, e);
        }
        if container.ty.arrayed().is_some() {
            return self.array_index(container, key, e);
        }
        let c = self.expr1(container);
        let k = self.expr(key);
        let loc = if container.ty.is_prelude("List") {
            self.proved_at(e.at, &[Check::Bounds])
        } else {
            self.loc_at(e.at)
        };
        self.index_value(&container.ty, c, k, loc, &e.ty)
    }

    /// The element of a list, or the value of a map, at a key, borrowed.
    pub(crate) fn index_value(
        &mut self,
        cty: &Ty,
        c: Operand,
        k: Vec<Operand>,
        loc: Operand,
        ty: &Ty,
    ) -> Vec<Operand> {
        if !cty.is_prelude("Map") {
            return self.list_index(c, word(&k, 0), loc, ty);
        }
        let key_ty = super::places::key_ty(cty);
        let k = self.map_word(k, &key_ty);
        let (eq, hash) = self.key_dicts(&key_ty);
        let at = self.b.define_op(
            Repr::Scalar,
            Rvalue::Runtime(Runtime::MapIndex, vec![loc, eq, hash, c.clone(), k]),
        );
        self.map_words(&c, &at, ty, true)
    }

    fn unary(&mut self, op: UnaryOp, x: &Expr, e: &Expr) -> Operand {
        if let (UnaryOp::Neg, ExprKind::Int(text)) = (op, &x.kind) {
            return Operand::word(int_literal(text, true, &e.ty));
        }
        let v = self.expr1(x);
        let loc = self.proved_at(e.at, &[Check::Overflow]);
        let prim = match (op, num_kind(&e.ty)) {
            (UnaryOp::Neg, Some(k)) => Prim::Neg(k),
            (UnaryOp::Not, Some(k)) => Prim::Not(k),
            (UnaryOp::Not, None) => Prim::BoolNot,
            (UnaryOp::Neg, None) => return v,
        };
        self.b
            .define_op(self.repr(&e.ty), Rvalue::Prim(prim, vec![v], loc))
    }

    fn binary(&mut self, op: BinaryOp, left: &Expr, right: &Expr, e: &Expr) -> Operand {
        match op {
            BinaryOp::And => return self.short_circuit(left, right, false),
            BinaryOp::Or => return self.short_circuit(left, right, true),
            _ => {}
        }
        let l = self.expr(left);
        let r = self.expr(right);
        let loc = self.proved_at(e.at, &[Check::DivideByZero, Check::Overflow]);
        self.binary_values(op, &left.ty, l, r, loc)
    }

    /// `a && b` evaluates `b` only when `a` is `true`, and `a || b` only when it is `false`
    /// (expressions.conditions).
    fn short_circuit(&mut self, a: &Expr, b: &Expr, or: bool) -> Operand {
        let result = self.b.temp(Repr::Scalar);
        let x = self.expr1(a);
        let (rhs, done) = (self.b.new_block(), self.b.new_block());
        self.b.assign(result, Rvalue::Use(x.clone()));
        if or {
            self.b.branch(x, done, rhs);
        } else {
            self.b.branch(x, rhs, done);
        }
        self.b.switch_to(rhs);
        let y = self.expr1(b);
        self.b.assign(result, Rvalue::Use(y));
        self.b.goto(done);
        self.b.switch_to(done);
        Operand::Local(result)
    }
}
