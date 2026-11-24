//! Calls (facts.analysis-order, facts.writes-through-calls and facts.proved-indexes): their
//! arguments in order, the checks of facts.proved-indexes's table where each reads its receiver,
//! and what each call writes to its `inout` arguments.

use stilt_hir::hir::{LocalId, Mode};

use super::Check;
use super::dbm::{Key, Term, ZERO};
use super::exprs::bounds_of;
use super::places::{Place, Reach};
use super::scan::Kind;
use super::state::State;
use super::values::Value;
use super::walker::{MAX_LEN, Walker};
use crate::tast::{Arg, Callee, Expr, ExprKind};
use crate::ty::{Row, Tail, is_numeric, is_prelude};

/// An argument once evaluated: a value, with the key it is and the length of the list binding
/// it names, or an `inout` argument's place, whose index expressions are evaluated.
#[derive(Clone, Debug)]
pub(crate) enum Evaluated {
    Value {
        value: Option<Value>,
        key: Option<Key>,
        len: Option<Term>,
    },
    Place(Place),
}

impl Evaluated {
    fn held(&self) -> Vec<Term> {
        match self {
            Evaluated::Value { value, key, len } => value
                .iter()
                .map(|v| v.term)
                .chain(*len)
                .chain(match key {
                    Some(Key::Form(t, _) | Key::Version(t)) => Some(*t),
                    _ => None,
                })
                .collect(),
            Evaluated::Place(p) => p.held(),
        }
    }

    pub(crate) fn value(&self) -> Option<Value> {
        match self {
            Evaluated::Value { value, .. } => *value,
            Evaluated::Place(_) => None,
        }
    }
}

/// The prelude's `List` or `Map` method that a callee is, by its name.
fn method<'c>(c: &'c Callee, owner: &str) -> Option<&'c str> {
    match c {
        Callee::Member(item, name) if is_prelude(item, owner) => Some(name),
        _ => None,
    }
}

impl Walker<'_> {
    /// A call by name, or a projection's call.
    pub(crate) fn call(&mut self, st: &mut State, e: &Expr) -> Option<Value> {
        let (ExprKind::Call(c, _, args, row) | ExprKind::Project(c, _, args, row)) = &e.kind else {
            return None;
        };
        if let Some(v) = self.linear_call(st, c, args, e) {
            return Some(v);
        }
        let evaluated = self.arguments(st, args);
        let held: Vec<Term> = evaluated.iter().flat_map(Evaluated::held).collect();
        self.holding(&held, |w| {
            w.starts(st, e, c, &evaluated);
            w.changes(st, c, args, &evaluated);
        });
        let effects = matches!(c, Callee::Operation(..)) || Self::effectful(row);
        self.leaves(st, row.raise.as_deref(), effects);
        self.opaque(st, &e.ty)
    }

    /// A call through a function value of type `f`: its arguments, what it writes to its
    /// `inout` ones, and where it may raise or end a `with`, as its type's row says.
    pub(crate) fn call_value(
        &mut self,
        st: &mut State,
        f: &crate::ty::Ty,
        args: &[Arg],
        e: &Expr,
    ) -> Option<Value> {
        let evaluated = self.arguments(st, args);
        let held: Vec<Term> = evaluated.iter().flat_map(Evaluated::held).collect();
        self.holding(&held, |w| {
            for ev in &evaluated {
                if let Evaluated::Place(p) = ev {
                    w.check_place(st, p, false);
                }
            }
            for ev in &evaluated {
                if let Evaluated::Place(p) = ev {
                    w.inout(st, p);
                }
            }
        });
        if let crate::ty::Ty::Fn(f) = f {
            let raise = f.row.raise.as_deref().cloned();
            let effects = Self::effectful(&f.row);
            self.leaves(st, raise.as_ref(), effects);
        }
        self.opaque(st, &e.ty)
    }

    /// Whether a call's row holds an effect or a row variable, so that a handler's operation
    /// may end a `with` around it (facts.paths-that-leave).
    fn effectful(row: &Row) -> bool {
        !row.effects.is_empty() || !matches!(row.tail, Tail::Closed)
    }

    /// Evaluates the arguments in order, holding each one's value for the rest
    /// (values.left-to-right).
    pub(crate) fn arguments(&mut self, st: &mut State, args: &[Arg]) -> Vec<Evaluated> {
        let mut out = Vec::new();
        let mut held = Vec::new();
        for a in args {
            let ev = self.holding(&held, |w| {
                if a.mode == Mode::Inout {
                    return Evaluated::Place(w.eval_place(st, &a.value));
                }
                let key = w.key_of(st, &a.value);
                let value = w.eval(st, &a.value);
                let len = match a.value.kind {
                    ExprKind::Local(v) if w.info.kind(v) == Kind::List => st.lens.get(&v).copied(),
                    _ => None,
                };
                Evaluated::Value { value, key, len }
            });
            held.extend(ev.held());
            out.push(ev);
        }
        out
    }

    /// Where the call starts: the reads of its `inout` arguments' places and the checks of
    /// facts.proved-indexes's table.
    fn starts(&mut self, st: &State, e: &Expr, c: &Callee, evaluated: &[Evaluated]) {
        for ev in evaluated {
            if let Evaluated::Place(p) = ev {
                self.check_place(st, p, false);
            }
        }
        if let Some(name) = method(c, "List") {
            self.table(st, e, name, evaluated);
        }
    }

    /// facts.proved-indexes's table: a call of `insert`, `remove`, `slice` or `swap` on a list
    /// binding, whose only panic is `bounds` on its arguments.
    fn table(&mut self, st: &State, call: &Expr, name: &str, evaluated: &[Evaluated]) {
        // `slice` takes `self`, read where it is evaluated; the others `inout self`, read where
        // the call starts (facts.analysis-order).
        let len = match (name, evaluated.first()) {
            ("slice", Some(Evaluated::Value { len, .. })) => *len,
            (
                _,
                Some(Evaluated::Place(Place {
                    root: Some(root),
                    steps,
                })),
            ) if steps.is_empty() => st.lens.get(root).copied(),
            _ => None,
        };
        let into = len.map_or(Reach::Unknown, Reach::Length);
        let arg = |index: usize| evaluated.get(index).and_then(Evaluated::value);
        let within = |index: usize, strict: bool| {
            let (lower, upper) = Self::in_range(st, arg(index), into, strict);
            lower && upper
        };
        let holds = match name {
            "insert" => within(1, false),
            "remove" => within(1, true),
            "swap" => within(1, true) && within(2, true),
            "slice" => {
                let ordered = match (arg(1), arg(2)) {
                    (Some(low), Some(high)) => st.facts.gives(low.term, high.term, high.d - low.d),
                    _ => st.is_bottom(),
                };
                Self::in_range(st, arg(1), into, false).0
                    && ordered
                    && Self::in_range(st, arg(2), into, false).1
            }
            _ => return,
        };
        self.prove(call.at, Check::Bounds, holds);
    }

    /// What a call writes to its `inout` arguments (facts.writes-through-calls and facts.map-keys),
    /// from the lengths and versions where it starts.
    fn changes(&mut self, st: &mut State, c: &Callee, args: &[Arg], evaluated: &[Evaluated]) {
        for (i, (a, ev)) in args.iter().zip(evaluated).enumerate() {
            let (Mode::Inout, Evaluated::Place(p)) = (a.mode, ev) else {
                continue;
            };
            let whole = p.steps.is_empty();
            match (i, p.root) {
                (0, Some(v)) if whole && method(c, "List").is_some() => {
                    self.list_method(st, v, method(c, "List").unwrap_or_default());
                }
                (0, Some(v)) if whole && method(c, "Map").is_some() => {
                    let key = match evaluated.get(1) {
                        Some(Evaluated::Value { key, .. }) => key.clone(),
                        _ => None,
                    };
                    self.map_method(st, v, method(c, "Map").unwrap_or_default(), key);
                }
                _ => self.inout(st, p),
            }
        }
    }

    /// facts.writes-through-calls's table, for a list binding passed as `inout self`.
    fn list_method(&mut self, st: &mut State, v: LocalId, name: &str) {
        let Some(&old) = st.lens.get(&v) else {
            return self.inout(
                st,
                &Place {
                    root: Some(v),
                    steps: Vec::new(),
                },
            );
        };
        let ver = self.fresh();
        st.vers.insert(v, ver);
        if name == "swap" {
            return;
        }
        let new = self.term(st, Some(0), Some(MAX_LEN));
        let (lo, hi) = match name {
            "push" | "insert" => (Some(1), Some(1)),
            "remove" => (Some(-1), Some(-1)),
            "pop" if st.facts.gives(ZERO, old, -1) => (Some(-1), Some(-1)),
            "pop" => (None, Some(0)),
            "clear" => {
                st.lens.insert(v, new);
                st.facts.assume(new, ZERO, 0);
                return;
            }
            _ => (None, None),
        };
        // ℓ' − ℓ lies within `lo` and `hi`.
        if let Some(lo) = lo {
            st.facts.assume(old, new, -lo);
        }
        if let Some(hi) = hi {
            st.facts.assume(new, old, hi);
        }
        st.lens.insert(v, new);
    }

    /// facts.map-keys, for a map binding passed as `inout self`: `insert` and `get_or_insert` make
    /// `k` present with the keys already present, and every other call makes none present.
    fn map_method(&mut self, st: &mut State, v: LocalId, name: &str, key: Option<Key>) {
        let Some(&old) = st.vers.get(&v) else {
            return;
        };
        let ver = self.fresh();
        st.vers.insert(v, ver);
        if !matches!(self.info.kind(v), Kind::Map(true)) {
            return;
        }
        if matches!(name, "insert" | "get_or_insert") {
            Self::keep_keys(st, old, ver);
            if let Some(k) = key {
                st.facts.present.insert((ver, k));
            }
        }
    }

    /// An `inout` argument other than facts.writes-through-calls's table: its root takes a new
    /// length, term or version with its bounds only, but for a place through `m[k]`, at whose new
    /// version the keys stay present (facts.writes-through-calls and facts.map-keys).
    pub(crate) fn inout(&mut self, st: &mut State, p: &Place) {
        let Some(root) = p.root else {
            return;
        };
        match self.info.kind(root) {
            Kind::Map(true) if !p.steps.is_empty() => self.write_place(st, p, false),
            _ => self.havoc(st, root),
        }
    }

    /// The forms of facts.linear-forms that are calls: `xs.len()`, an array place's `len()`, and
    /// `x.to_T()` whose result isn't an `Option`.
    fn linear_call(
        &mut self,
        st: &mut State,
        callee: &Callee,
        args: &[Arg],
        expr: &Expr,
    ) -> Option<Value> {
        let Callee::Member(owner, name) = callee else {
            return None;
        };
        let [receiver] = args else {
            return None;
        };
        if is_prelude(owner, "List") && &**name == "len" {
            let ExprKind::Local(binding) = receiver.value.kind else {
                return None;
            };
            let &len = st.lens.get(&binding)?;
            return Some(Walker::linear(st, len, 0));
        }
        if crate::ty::is_array(owner) && &**name == "len" && self.simple_place(st, &receiver.value)
        {
            let size = self.size(&receiver.value.ty)?;
            self.eval(st, &receiver.value);
            return Some(match size {
                super::places::Size::Term(term) => Walker::linear(st, term, 0),
                super::places::Size::Number(number) => Walker::linear(st, ZERO, number),
            });
        }
        if is_numeric(owner) && name.starts_with("to_") && bounds_of(&expr.ty).is_some() {
            let value = self.eval(st, &receiver.value)?;
            return match value.form() {
                Some((term, offset)) => Some(Walker::linear(st, term, offset)),
                None => self.opaque(st, &expr.ty),
            };
        }
        None
    }

    /// Whether an expression is a binding with fields and indexes after it, whose indexes are
    /// linear forms, so that evaluating it changes nothing (facts.linear-forms).
    fn simple_place(&self, st: &State, e: &Expr) -> bool {
        match &e.kind {
            ExprKind::Local(_) => true,
            ExprKind::Field(b, _) | ExprKind::TupleField(b, _) => self.simple_place(st, b),
            ExprKind::Index(b, k) => self.simple_place(st, b) && self.form_of(st, k).is_some(),
            _ => false,
        }
    }

    /// The linear form an expression's value is, read from the bindings' current terms, if it
    /// is one (facts.linear-forms).
    pub(crate) fn form_of(&self, st: &State, expr: &Expr) -> Option<(Term, i128)> {
        bounds_of(&expr.ty)?;
        if let Some(number) = self.number(expr) {
            return Some((ZERO, number));
        }
        match &expr.kind {
            ExprKind::Local(binding) if matches!(self.info.kind(*binding), Kind::Int(..)) => {
                st.ints.get(binding).map(|term| (*term, 0))
            }
            ExprKind::ValueParam(id) => self.values.get(id).map(|term| (*term, 0)),
            ExprKind::Binary(stilt_hir::hir::BinaryOp::Add, left, right) => {
                if let (Some((term, offset)), Some(more)) =
                    (self.form_of(st, left), self.number(right))
                {
                    return Some((term, offset + more));
                }
                let (term, offset) = self.form_of(st, right)?;
                Some((term, offset + self.number(left)?))
            }
            ExprKind::Binary(stilt_hir::hir::BinaryOp::Sub, left, right) => {
                let (term, offset) = self.form_of(st, left)?;
                Some((term, offset - self.number(right)?))
            }
            ExprKind::Call(Callee::Member(owner, name), _, args, _) => match args.as_slice() {
                [receiver] if is_prelude(owner, "List") && &**name == "len" => {
                    let ExprKind::Local(binding) = receiver.value.kind else {
                        return None;
                    };
                    st.lens.get(&binding).map(|term| (*term, 0))
                }
                [receiver] if crate::ty::is_array(owner) && &**name == "len" => {
                    match self
                        .simple_place(st, &receiver.value)
                        .then(|| self.size(&receiver.value.ty))??
                    {
                        super::places::Size::Term(term) => Some((term, 0)),
                        super::places::Size::Number(number) => Some((ZERO, number)),
                    }
                }
                [receiver] if is_numeric(owner) && name.starts_with("to_") => {
                    self.form_of(st, &receiver.value)
                }
                _ => None,
            },
            _ => None,
        }
    }
}
