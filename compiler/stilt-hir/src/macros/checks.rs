//! The checks of a macro's declaration (macros.patterns, macros.pattern-checks and
//! macros.templates): each pattern names its fragments once, from the six kinds, with a follower
//! that ends an expression, a pattern or a type, and a fragment in each repetition (E0220); each
//! template names only the fragments its pattern binds, at their depths, each repetition's from one
//! repetition of the pattern, and parses as an expression, a pattern or both (E0221).

use std::collections::hash_map::Entry;
use std::collections::{HashMap, HashSet};

use stilt_diag::{AlternativeKind, Diagnostic, Edit, Fix, codes};
use stilt_syntax::forms::{Form, Piece, parse_form};
use stilt_syntax::{SyntaxKind, TextRange};

use super::substitute::{Tok, placeholders};
use super::{FragKind, MacroArm, Matcher, Rep, TItem};
use crate::hir::Name;

/// Checks an arm, adding its errors, and returns whether its template is an expression and
/// whether it is a pattern. An arm with an error is neither.
pub(super) fn check_arm(arm: &MacroArm, errors: &mut Vec<Diagnostic>) -> (bool, bool) {
    let before = errors.len();
    let mut bound = HashMap::new();
    pattern(&arm.pattern, &mut Vec::new(), &mut bound, errors);
    if let Some((name, kind, (name_at, kind_at))) = &arm.trailing {
        if kind != &Some(FragKind::Block) {
            let message = format!("`${name}` follows the pattern, so its kind is `block`");
            errors.push(Diagnostic::new(codes::E0220, *kind_at, message));
        }
        fragment_named(*name, *name_at, &mut bound, (Vec::new(), *kind), errors);
    }
    follows(&arm.pattern, &[Follower::End], errors);
    if errors.len() > before {
        return (false, false);
    }
    template(&arm.template, &mut Vec::new(), &bound, errors);
    if errors.len() > before {
        return (false, false);
    }
    let kinds: HashMap<Name, FragKind> = arm.kinds().into_iter().collect();
    let own = |kind, text: &Name, at| Tok {
        kind,
        text: *text,
        at,
        user: false,
        mark: 0,
    };
    let tokens = placeholders(&arm.template, &kinds, &own);
    let pieces: Vec<Piece<'_>> = tokens
        .iter()
        .map(|t| Piece {
            kind: t.kind,
            text: &t.text,
        })
        .collect();
    let is = |form| parse_form(&pieces, form).is_whole(pieces.len());
    let (expr, pattern) = (is(Form::Expr), is(Form::Pattern));
    if !expr && !pattern {
        let message = "this template is neither an expression nor a pattern";
        let first = TextRange::at(arm.at.start(), first_len(&arm.template));
        errors.push(Diagnostic::new(codes::E0221, first, message));
    }
    (expr, pattern)
}

/// The length of a template's first token.
fn first_len(items: &[TItem]) -> stilt_syntax::TextSize {
    match items.first() {
        Some(TItem::Token(_, _, at) | TItem::Frag(_, at) | TItem::Group(_, _, at, _)) => at.len(),
        Some(TItem::Rep(rep)) => rep.at.len(),
        None => 0.into(),
    }
}

/// What a fragment is bound to: the repetitions it is inside, each by its `$`, and its kind.
type Binding = (Vec<TextRange>, Option<FragKind>);

fn fragment_named(
    name: Name,
    at: TextRange,
    bound: &mut HashMap<Name, Binding>,
    binding: Binding,
    errors: &mut Vec<Diagnostic>,
) {
    match bound.entry(name) {
        Entry::Occupied(_) => {
            let message = format!("`${name}` is already named in this pattern");
            errors.push(Diagnostic::new(codes::E0220, at, message));
        }
        Entry::Vacant(v) => {
            v.insert(binding);
        }
    }
}

/// The fragments of a pattern, each named once and of a kind (macros.pattern-checks), and a
/// fragment in each repetition.
fn pattern(
    ms: &[Matcher],
    reps: &mut Vec<TextRange>,
    bound: &mut HashMap<Name, Binding>,
    errors: &mut Vec<Diagnostic>,
) {
    for m in ms {
        match m {
            Matcher::Frag(name, kind, at) => {
                if kind.is_none() {
                    let message = "a fragment's kind is `expr`, `block`, `pattern`, `type`, \
                                   `name` or `Name`";
                    errors.push(Diagnostic::new(codes::E0220, *at, message));
                }
                fragment_named(*name, *at, bound, (reps.clone(), *kind), errors);
            }
            Matcher::Rep(rep) => {
                if !holds_fragment(&rep.items) {
                    let message = "this repetition holds no fragment";
                    errors.push(Diagnostic::new(codes::E0220, rep.at, message));
                }
                reps.push(rep.at);
                pattern(&rep.items, reps, bound, errors);
                reps.pop();
            }
            Matcher::Group(_, items) => pattern(items, reps, bound, errors),
            Matcher::Token(..) => {}
        }
    }
}

fn holds_fragment(ms: &[Matcher]) -> bool {
    ms.iter().any(|m| match m {
        Matcher::Frag(..) => true,
        Matcher::Rep(rep) => holds_fragment(&rep.items),
        Matcher::Group(_, items) => holds_fragment(items),
        Matcher::Token(..) => false,
    })
}

/// What may follow a matcher in its pattern: the end of its group, a token, or anything else,
/// a fragment or a group, which an expression could read on into.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Follower {
    End,
    Token(SyntaxKind),
    Other,
}

/// What may come first in a sequence of matchers that `after` follows: its first matcher's
/// first, and, past a repetition with `*`, which may match nothing, what comes after it.
fn first(ms: &[Matcher], after: &[Follower]) -> Vec<Follower> {
    match ms.split_first() {
        None => after.to_vec(),
        Some((Matcher::Token(kind, _), _)) => vec![Follower::Token(*kind)],
        Some((Matcher::Rep(rep), rest)) => {
            let mut set = first(&rep.items, &[]);
            if !rep.plus {
                set.extend(first(rest, after));
            }
            set
        }
        Some((Matcher::Frag(..) | Matcher::Group(..), _)) => vec![Follower::Other],
    }
}

/// Whether what may follow a fragment ends an expression, a pattern or a type there.
fn ends(next: &[Follower]) -> bool {
    use SyntaxKind::{COMMA, FAT_ARROW, SEP};
    next.iter()
        .all(|f| matches!(f, Follower::End | Follower::Token(COMMA | SEP | FAT_ARROW)))
}

/// An `expr`, `pattern` or `type` fragment is followed by the end of its group, `,`, `;` or
/// `=>`. Inside a repetition, the last matcher is followed by the separator, or by the first
/// matcher when there is none, and by what follows the repetition.
fn follows(ms: &[Matcher], after: &[Follower], errors: &mut Vec<Diagnostic>) {
    for (i, m) in ms.iter().enumerate() {
        let next = first(&ms[i + 1..], after);
        match m {
            Matcher::Frag(name, Some(kind), at) if kind.parenthesized() && !ends(&next) => {
                let message = format!(
                    "`${name}` could read on into what follows it, which isn't `,`, `;`, `=>` or \
                     the group's end"
                );
                let comma = Fix::new(
                    format!("end `${name}` with a `,`"),
                    vec![Edit::insert(at.end(), ",")],
                );
                errors.push(Diagnostic::new(codes::E0220, *at, message).with_fix(comma));
            }
            Matcher::Rep(rep) => {
                let mut last = match rep.sep {
                    Some(sep) => vec![Follower::Token(sep)],
                    None => first(&rep.items, &[]),
                };
                last.extend(next);
                follows(&rep.items, &last, errors);
            }
            Matcher::Group(_, items) => follows(items, &[Follower::End], errors),
            Matcher::Frag(..) | Matcher::Token(..) => {}
        }
    }
}

/// The fragments a template names: each bound, at its depth, and each repetition's from one
/// repetition of the pattern (macros.templates).
fn template(
    items: &[TItem],
    depth: &mut Vec<TextRange>,
    bound: &HashMap<Name, Binding>,
    errors: &mut Vec<Diagnostic>,
) {
    for item in items {
        match item {
            TItem::Frag(name, at) => match bound.get(name) {
                None => {
                    let message = format!("`${name}` isn't a fragment of this arm's pattern");
                    let mut written: Vec<String> = bound.keys().map(|n| format!("${n}")).collect();
                    written.sort();
                    let d = Diagnostic::new(codes::E0221, *at, message).with_closest(
                        AlternativeKind::Name,
                        *at,
                        &format!("${name}"),
                        written.iter().map(String::as_str),
                    );
                    errors.push(d);
                }
                Some((reps, _)) if reps.len() != depth.len() => {
                    let message = format!(
                        "`${name}` is bound inside {} repetitions, but named inside {}",
                        reps.len(),
                        depth.len()
                    );
                    errors.push(Diagnostic::new(codes::E0221, *at, message));
                }
                Some(_) => {}
            },
            TItem::Rep(rep) => repetition(rep, depth, bound, errors),
            TItem::Group(_, inner, ..) => template(inner, depth, bound, errors),
            TItem::Token(..) => {}
        }
    }
}

fn repetition(
    rep: &Rep<TItem>,
    depth: &mut Vec<TextRange>,
    bound: &HashMap<Name, Binding>,
    errors: &mut Vec<Diagnostic>,
) {
    let level = depth.len();
    let mut sources = HashSet::new();
    let mut any = false;
    named(&rep.items, &mut |name| {
        any = true;
        if let Some((reps, _)) = bound.get(name)
            && let Some(source) = reps.get(level)
        {
            sources.insert(*source);
        }
    });
    // A fragment named at the wrong depth is an error of its own.
    let message = if !any {
        Some("this repetition names no fragment, so nothing gives its length")
    } else if sources.len() > 1 {
        Some("this repetition names fragments of two repetitions, which may differ in length")
    } else {
        None
    };
    if let Some(message) = message {
        errors.push(Diagnostic::new(codes::E0221, rep.at, message));
    }
    depth.push(rep.at);
    template(&rep.items, depth, bound, errors);
    depth.pop();
}

/// Calls `f` on the name of each fragment that items name.
fn named(items: &[TItem], f: &mut impl FnMut(&Name)) {
    for item in items {
        match item {
            TItem::Frag(name, _) => f(name),
            TItem::Rep(rep) => named(&rep.items, f),
            TItem::Group(_, inner, ..) => named(inner, f),
            TItem::Token(..) => {}
        }
    }
}
