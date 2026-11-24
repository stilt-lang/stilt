//! Removes left recursion, which GBNF cannot express, by the standard substitution: a rule
//! `A = A a | b` becomes `A = b { a }`, and in a cycle of rules that begin with one another,
//! each rule first begins with the alternatives of the rules before it. Only the productions
//! of `reference/03-syntax.md` that recurse on the left change, among them the binary operators and
//! the postfix forms.

use std::collections::{BTreeMap, BTreeSet};

use crate::ebnf::Expr;
use crate::expand::Grammar;

/// Rewrites every cycle of rules that begin with one another, and fails if one remains.
pub(crate) fn eliminate(grammar: &mut Grammar) -> Result<(), String> {
    for cycle in left_cycles(grammar) {
        for (at, rule) in cycle.iter().enumerate() {
            for earlier in &cycle[..at] {
                substitute(grammar, rule, earlier);
            }
            remove_immediate(grammar, rule)?;
        }
    }
    match left_cycles(grammar).first() {
        None => Ok(()),
        Some(cycle) => Err(format!("left recursion remains in {}", cycle.join(", "))),
    }
}

/// The elements of a branch.
fn items(branch: &Expr) -> Vec<Expr> {
    match branch {
        Expr::Seq(items) => items.clone(),
        other => vec![other.clone()],
    }
}

fn branches(body: &Expr) -> Vec<Expr> {
    match body {
        Expr::Alt(items) => items.clone(),
        other => vec![other.clone()],
    }
}

fn one_or_alt(mut branches: Vec<Expr>) -> Expr {
    if branches.len() == 1 {
        branches.remove(0)
    } else {
        Expr::Alt(branches)
    }
}

fn begins_with(branch: &Expr, rule: &str) -> bool {
    matches!(items(branch).first(), Some(Expr::Ref(name)) if name == rule)
}

/// Replaces each branch of `rule` that begins with `earlier` by the branches of `earlier`,
/// each followed by the rest of the branch.
fn substitute(grammar: &mut Grammar, rule: &str, earlier: &str) {
    let Some(inner) = grammar.get(earlier).map(branches) else {
        return;
    };
    let body = grammar.get(rule).map(branches).unwrap_or_default();
    let mut out = Vec::new();
    for branch in body {
        if begins_with(&branch, earlier) {
            let rest = items(&branch).split_off(1);
            for start in &inner {
                let mut all = items(start);
                all.extend(rest.clone());
                out.push(Expr::Seq(all));
            }
        } else {
            out.push(branch);
        }
    }
    grammar.set(rule, one_or_alt(out));
}

/// Rewrites `A = A a | b` to `A = b { a }`.
fn remove_immediate(grammar: &mut Grammar, rule: &str) -> Result<(), String> {
    let body = grammar.get(rule).map(branches).unwrap_or_default();
    let (recursive, others): (Vec<_>, Vec<_>) =
        body.into_iter().partition(|b| begins_with(b, rule));
    if recursive.is_empty() {
        return Ok(());
    }
    if others.is_empty() {
        return Err(format!(
            "`{rule}` has no alternative that doesn't begin with itself"
        ));
    }
    let mut tails = Vec::new();
    for branch in &recursive {
        let rest = items(branch).split_off(1);
        if rest.is_empty() {
            return Err(format!("`{rule}` is defined as itself"));
        }
        tails.push(Expr::Seq(rest));
    }
    let star = Expr::Star(Box::new(one_or_alt(tails)));
    grammar.set(rule, Expr::Seq(vec![one_or_alt(others), star]));
    Ok(())
}

/// The groups of rules that can each begin with the others, in grammar order.
fn left_cycles(grammar: &Grammar) -> Vec<Vec<String>> {
    let nullable = nullable_rules(grammar);
    let leading: BTreeMap<&str, BTreeSet<String>> = grammar
        .rules
        .iter()
        .map(|(name, body)| (name.as_str(), leading_refs(body, &nullable)))
        .collect();
    let reach = |from: &str| {
        let mut seen = BTreeSet::new();
        let mut todo: Vec<String> = leading[from].iter().cloned().collect();
        while let Some(next) = todo.pop() {
            if seen.insert(next.clone()) {
                todo.extend(leading.get(next.as_str()).into_iter().flatten().cloned());
            }
        }
        seen
    };
    let mut done = BTreeSet::new();
    let mut cycles = Vec::new();
    for (name, _) in &grammar.rules {
        if done.contains(name) || !reach(name).contains(name) {
            continue;
        }
        let cycle: Vec<String> = grammar
            .rules
            .iter()
            .map(|(other, _)| other.clone())
            .filter(|other| reach(name).contains(other) && reach(other).contains(name))
            .collect();
        done.extend(cycle.iter().cloned());
        cycles.push(cycle);
    }
    cycles
}

fn nullable_rules(grammar: &Grammar) -> BTreeSet<String> {
    let mut nullable = BTreeSet::new();
    loop {
        let before = nullable.len();
        for (name, body) in &grammar.rules {
            if is_nullable(body, &nullable) {
                nullable.insert(name.clone());
            }
        }
        if nullable.len() == before {
            return nullable;
        }
    }
}

fn is_nullable(expr: &Expr, nullable: &BTreeSet<String>) -> bool {
    match expr {
        Expr::Ref(name) => nullable.contains(name),
        Expr::Lit(_) | Expr::Call(..) => false,
        Expr::Empty | Expr::Opt(_) | Expr::Star(_) => true,
        Expr::Seq(items) => items.iter().all(|e| is_nullable(e, nullable)),
        Expr::Alt(items) => items.iter().any(|e| is_nullable(e, nullable)),
    }
}

/// The rules that a derivation of `expr` can begin with.
fn leading_refs(expr: &Expr, nullable: &BTreeSet<String>) -> BTreeSet<String> {
    match expr {
        Expr::Ref(name) => BTreeSet::from([name.clone()]),
        Expr::Seq(items) => {
            let mut out = BTreeSet::new();
            for item in items {
                out.extend(leading_refs(item, nullable));
                if !is_nullable(item, nullable) {
                    break;
                }
            }
            out
        }
        Expr::Alt(items) => items
            .iter()
            .flat_map(|e| leading_refs(e, nullable))
            .collect(),
        Expr::Opt(inner) | Expr::Star(inner) => leading_refs(inner, nullable),
        Expr::Lit(_) | Expr::Empty | Expr::Call(..) => BTreeSet::new(),
    }
}
