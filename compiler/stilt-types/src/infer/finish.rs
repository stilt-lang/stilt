//! The end of a body: the rules whose answer needs every type of the body, decided once
//! inference is done.

use std::collections::HashMap;

use stilt_diag::{Edit, Fix, codes};
use stilt_hir::hir::Item;
use stilt_syntax::TextRange;
use stilt_syntax::format_spec;

use super::{Leading, Receiver, Rule, State, UnitSite};
use crate::implements::{Answer, Traits};
use crate::literal;
use crate::ty::{FLOAT_TYPES, Kind, Ty};

impl State<'_> {
    /// Decides the rules that wait for every type of the body.
    pub(super) fn finish(&mut self) {
        // effects.catch: a `catch` whose operand raises nothing catches `Never`.
        for t in std::mem::take(&mut self.catch_errors) {
            if self.table.unsolved(&t).is_some() {
                self.table.solve(&t, Ty::never());
            }
        }
        self.settle_args();
        // numbers.literal-defaults
        for l in self.literals.clone() {
            match self.table.unsolved(&l.ty).map(|v| v.kind) {
                Some(Kind::IntLiteral) => self.table.solve(&l.ty, Ty::i64()),
                Some(Kind::FloatLiteral) => self.table.solve(&l.ty, Ty::f64()),
                _ => {}
            }
        }
        self.settle_args();
        self.unit_sites();
        self.literal_ranges();
        self.c_elements();
        // patterns.floats
        for (ty, at) in self.int_patterns.clone() {
            if self.holds_float(&ty) {
                let message = "a float can't be matched by a pattern";
                self.error(codes::E0328, at, message.to_owned());
            }
        }
        // numbers.no-implicit-conversions, numbers.bitwise-operators and numbers.comparisons, and
        // expressions.no-string-plus: the operators whose operand type was open where they were
        // checked.
        for (ty, rule, at) in self.operators.clone() {
            if self.supports(&ty, rule) == Some(false) {
                self.unsupported(&ty, rule, at);
            }
        }
        // numbers.shift-amounts: the shift amounts whose type was open.
        for (ty, at) in self.amounts.clone() {
            if self.supports(&ty, Rule::Integer) == Some(false) {
                self.not_an_amount(&ty, at);
            }
        }
        self.missing_impls();
        self.format_specs();
        self.unknown_types();
    }

    /// expressions.statements and expressions.if.
    fn unit_sites(&mut self) {
        for (ty, site, at) in self.units.clone() {
            let valued = match &self.table.shape(&ty) {
                Ty::Tuple(ts) if ts.is_empty() => false,
                Ty::Error | Ty::Var(_) => false,
                // tasks.std-task, Required tests: a task that is never awaited, whose handle a
                // statement drops, still runs.
                Ty::Con(item, _) if &*item.home == "std.task" && &*item.name == "Task" => false,
                t => *t != Ty::never(),
            };
            match site {
                UnitSite::Statement(leading, receiver) if valued => {
                    self.unused_value(&ty, (leading, receiver), at);
                }
                UnitSite::IfWithoutElse(_) if valued => {
                    let message = format!(
                        "an `if` without `else` can't have a value of type `{}`",
                        self.show(&ty)
                    );
                    self.error(codes::E0323, at, message);
                }
                UnitSite::IfWithoutElse(if_ty) => {
                    if !self.table.unify(&if_ty, &Ty::unit()) {
                        let message = format!("expected `{}`, found `()`", self.show(&if_ty));
                        self.error(codes::E0311, at, message);
                    }
                }
                UnitSite::Statement(..) => {}
            }
        }
    }

    /// expressions.unused-values. When the next statement is a closure that starts with `||`, the
    /// value is more likely the left side of an `||` that was written at the start of the next
    /// line, which lexical.terminator-insertion makes a closure.
    fn unused_value(
        &mut self,
        ty: &Ty,
        (leading, receiver): (Option<Leading>, Option<Receiver>),
        at: TextRange,
    ) {
        let discard = Fix::new(
            "discard it on purpose",
            vec![Edit::insert(at.start(), "let _ = ")],
        );
        let mut message = format!("this value of type `{}` is unused", self.show(ty));
        let mut fixes = vec![discard];
        if let Some(fix) = receiver.and_then(|r| self.kept(ty, r, at)) {
            fixes.insert(0, fix);
        }
        if let Some(Leading { closure, operator }) = leading {
            message.push_str(", and the next line starts a closure with `||`");
            let moved = Fix::new(
                "move `||` to the end of the line before",
                vec![Edit::insert(at.end(), " ||"), Edit::delete(operator)],
            );
            fixes = vec![moved, fixes.pop().expect("the fix that discards it")];
            for d in &mut self.errors {
                if d.code == codes::E0311 && d.range == closure {
                    d.label = Some("a line that starts with `||` begins a closure".into());
                }
            }
        }
        self.error_fixed(codes::E0322, at, message, fixes);
    }

    /// The fix that keeps an unused value of the type of the local whose method made it, as
    /// `xs.reversed()` makes a new `xs`: assigned to the local where it can be changed
    /// (modes.what-can-be-modified), or bound to its name again otherwise
    /// (expressions.shadowing).
    fn kept(&mut self, ty: &Ty, receiver: Receiver, at: TextRange) -> Option<Fix> {
        let local = self.locals.get(&receiver.local)?.clone();
        if self.table.freeze(&local) != self.table.freeze(ty) {
            return None;
        }
        let name = *self.local_names.get(receiver.local.0 as usize)?;
        let (title, text) = if self.modifiable.contains(&receiver.local) {
            (format!("assign it to `{name}`"), format!("{name} = "))
        } else {
            (format!("keep it as `{name}`"), format!("let {name} = "))
        };
        Some(Fix::new(title, vec![Edit::insert(at.start(), text)]))
    }

    /// numbers.integer-literals, numbers.float-literals and numbers.negative-literals.
    fn literal_ranges(&mut self) {
        for l in self.literals.clone() {
            let Some(name) = self.table.numeric_name(&l.ty) else {
                continue;
            };
            let fits = if l.float {
                literal::float_fits(&l.text, &name)
            } else if FLOAT_TYPES.contains(&name.as_str()) {
                literal::int_exact_in(&l.text, &name)
            } else {
                literal::int_fits(&l.text, l.negative, &name)
            };
            if !fits {
                let sign = if l.negative { "-" } else { "" };
                let message = format!("{sign}{} doesn't fit in `{name}`", l.text);
                self.error(codes::E0320, l.at, message);
            }
        }
    }

    /// traits.unsatisfied-bounds, and traits.bound-reported-once: each type and trait once per
    /// body, at its first use in source order, and the traits missing at one use in one diagnostic.
    fn missing_impls(&mut self) {
        let traits = Traits {
            decls: self.env.decls,
            scope: &self.env.bound_args,
            table: &self.table,
        };
        // A pack's obligation is each of its elements' (variadics.packs).
        let obligations: Vec<(Ty, Item, TextRange)> = self
            .obligations
            .iter()
            .flat_map(|(ty, t, at)| {
                let frozen = self.table.freeze(ty);
                let each = self.table.elements(std::slice::from_ref(&frozen));
                each.into_iter().map(move |e| (e, t.clone(), *at))
            })
            .collect();
        let mut missing: Vec<(String, Item, TextRange, Ty)> = obligations
            .iter()
            .filter(|(ty, t, _)| traits.implements(&self.env.bounds, ty, t) == Answer::No)
            .map(|(ty, t, at)| (self.show(ty), t.clone(), *at, ty.clone()))
            .collect();
        missing.sort_by_key(|(_, _, at, _)| at.start());
        let mut firsts: Vec<(String, Item, TextRange, Ty)> = Vec::new();
        for use_ in missing {
            // The rigid types of two values checked against polymorphic function types are
            // two types, though shown alike (polymorphism.rigid-types).
            let rigid = |t: &Ty| {
                let mut found = Vec::new();
                super::poly::rigid_params(&self.table.freeze(t), &mut found);
                found
            };
            if !firsts.iter().any(|(t, tr, _, ty)| {
                *t == use_.0 && tr.name == use_.1.name && rigid(ty) == rigid(&use_.3)
            }) {
                firsts.push(use_);
            }
        }
        while let Some((shown, _, at, ty)) = firsts.first().cloned() {
            let (here, rest): (Vec<_>, Vec<_>) = firsts
                .into_iter()
                .partition(|(t, _, a, _)| *t == shown && a.start() == at.start());
            let needed: Vec<Item> = here.into_iter().map(|(_, t, _, _)| t).collect();
            let listed: Vec<String> = needed.iter().map(|t| format!("`{}`", t.name)).collect();
            let message = format!("`{shown}` doesn't implement {}", listed.join(" or "));
            let fix = self.bound_fix(&ty, &needed);
            self.error_fixed(codes::E0318, at, message, fix.into_iter().collect());
            firsts = rest;
        }
    }

    /// std.width-fill-and-alignment, std.precision, std.integer-kinds, std.scientific-notation,
    /// std.format-special-values and std.invalid-specs: which types a format spec applies to.
    fn format_specs(&mut self) {
        for (ty, spec, at) in self.specs.clone() {
            // A doc example of a part with a syntax error is inferred anyway, and its malformed
            // spec is the part's E0007 (lexical.format-specs; program.doc-examples).
            let Some(parsed) = format_spec::parse(&spec) else {
                continue;
            };
            let precision = parsed.precision.is_some();
            let integer = self.table.integer_name(&ty).is_some();
            let floating = self.table.numeric_name(&ty).is_some() && !integer;
            let ok = match &self.table.shape(&ty) {
                Ty::Error | Ty::Var(_) => true,
                _ => match parsed.kind {
                    Some('x' | 'X' | 'o' | 'b') => integer && !precision,
                    Some('e') => floating,
                    _ => !precision || floating,
                },
            };
            if !ok {
                let message = format!(
                    "the format spec `{spec}` doesn't apply to `{}`",
                    self.show(&ty)
                );
                self.error(codes::E0325, at, message);
            }
        }
    }

    /// Types that inference didn't decide, when nothing else is wrong: each at the first
    /// expression, in source order, whose type holds it, and once per expression
    /// (types.undecided-types). Variables that inference made one take the earliest origin of any
    /// of them.
    fn unknown_types(&mut self) {
        if !self.errors.is_empty() || self.broken {
            return;
        }
        let mut first: HashMap<_, TextRange> = HashMap::new();
        for v in &self.vars {
            if let (Some(own), Some(info)) = (self.table.origin(v), self.table.unsolved(v))
                && !info.tainted
                && !self.unknown.contains(&info.id)
            {
                first
                    .entry(info.id)
                    .and_modify(|origin| {
                        if own.start() < origin.start() {
                            *origin = own;
                        }
                    })
                    .or_insert(own);
            }
        }
        let mut origins: Vec<TextRange> = first.into_values().collect();
        origins.sort_by_key(|at| (at.start(), at.end()));
        origins.dedup_by_key(|at| at.start());
        for origin in origins {
            let message = "the type of this expression can't be inferred; add an annotation";
            self.error(codes::E0312, origin, message.to_owned());
        }
    }
}
