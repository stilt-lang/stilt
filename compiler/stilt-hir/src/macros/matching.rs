//! Matching a use's tokens against a macro's arms (macros.matching): the first arm that matches
//! them all is used, a fragment matching the longest form of its kind, a repetition as many
//! times as it can, and a trailing block the use's. A use that no arm matches names the
//! furthest token any arm reached, and what that arm expected there.

use std::collections::HashMap;

use stilt_syntax::SyntaxKind::{
    self, L_BRACK, L_CURLY, L_PAREN, LOWER_IDENT, R_BRACK, R_CURLY, R_PAREN, UPPER_IDENT,
};
use stilt_syntax::ast::Bracket;
use stilt_syntax::forms::{Form, Piece, parse_form};

use super::substitute::{Bindings, Bound, Tok};
use super::{FragKind, MacroArm, Matcher, Rep, bracket_text};
use crate::hir::Name;

/// A use's tokens: its group's, brackets included, then its trailing block's, if any.
pub(crate) struct UseTokens {
    pub(crate) tokens: Vec<Tok>,
    /// The index of the group's closing bracket.
    pub(crate) group_end: usize,
    /// For each opening bracket, the index of its closing one.
    closes: HashMap<usize, usize>,
}

impl UseTokens {
    pub(crate) fn new(tokens: Vec<Tok>, group_end: usize) -> Self {
        let mut closes = HashMap::new();
        let mut open = Vec::new();
        for (i, t) in tokens.iter().enumerate() {
            match t.kind {
                L_PAREN | L_BRACK | L_CURLY => open.push(i),
                R_PAREN | R_BRACK | R_CURLY => {
                    if let Some(o) = open.pop() {
                        closes.insert(o, i);
                    }
                }
                _ => {}
            }
        }
        Self {
            tokens,
            group_end,
            closes,
        }
    }

    fn bracket(&self) -> Bracket {
        match self.tokens.first().map(|t| t.kind) {
            Some(L_BRACK) => Bracket::Square,
            _ => Bracket::Paren,
        }
    }
}

/// Why no arm matched: the furthest token reached, by index, and what was expected there.
#[derive(Clone, Debug)]
pub(crate) struct Failure {
    pub(crate) at: usize,
    pub(crate) expected: String,
}

/// The first arm that matches the use, by index, with what its fragments bound.
pub(crate) fn match_arms(
    arms: &[MacroArm],
    use_: &UseTokens,
) -> Result<(usize, Bindings), Failure> {
    let mut m = Matching {
        use_,
        failure: None,
    };
    for (i, arm) in arms.iter().enumerate() {
        if let Some(bindings) = m.arm(arm) {
            return Ok((i, bindings));
        }
    }
    Err(m.failure.unwrap_or(Failure {
        at: use_.group_end,
        expected: "an arm".to_owned(),
    }))
}

struct Matching<'u> {
    use_: &'u UseTokens,
    failure: Option<Failure>,
}

impl Matching<'_> {
    /// Records that a matcher expected `expected` at token `at`, if no arm got further.
    fn fail(&mut self, at: usize, expected: impl Into<String>) {
        if self.failure.as_ref().is_none_or(|f| at > f.at) {
            self.failure = Some(Failure {
                at,
                expected: expected.into(),
            });
        }
    }

    fn arm(&mut self, arm: &MacroArm) -> Option<Bindings> {
        let toks = &self.use_.tokens;
        let end = self.use_.group_end;
        if arm.bracket != self.use_.bracket() {
            let (_, text) = bracket_text(arm.bracket, true);
            self.fail(0, format!("`{text}`"));
            return None;
        }
        let mut binds = Bindings::new();
        let pos = self.seq(&arm.pattern, 1, end, &mut binds)?;
        if pos != end {
            let (_, text) = bracket_text(arm.bracket, false);
            self.fail(pos, format!("`{text}`"));
            return None;
        }
        let trailing = end + 1 < toks.len();
        match &arm.trailing {
            Some((name, _, _)) if trailing => {
                let tokens = self.block(end + 1)?;
                binds.insert(*name, (FragKind::Block, Bound::One(tokens)));
            }
            Some(_) => {
                self.fail(end, "a block after the use");
                return None;
            }
            None if trailing => {
                self.fail(end + 1, "no block after the use");
                return None;
            }
            None => {}
        }
        Some(binds)
    }

    /// Matches `ms` from token `pos`, before `end`, and returns where the match ends.
    fn seq(
        &mut self,
        ms: &[Matcher],
        mut pos: usize,
        end: usize,
        binds: &mut Bindings,
    ) -> Option<usize> {
        for m in ms {
            pos = match m {
                Matcher::Token(kind, text) => {
                    let t = self.use_.tokens.get(pos).filter(|_| pos < end);
                    if t.is_some_and(|t| t.kind == *kind && t.text == *text) {
                        pos + 1
                    } else {
                        self.fail(pos, format!("`{text}`"));
                        return None;
                    }
                }
                Matcher::Group(bracket, inner) => self.group(*bracket, inner, pos, end, binds)?,
                Matcher::Frag(name, kind, _) => {
                    let kind = kind.unwrap_or(FragKind::Expr);
                    let (tokens, next) = self.fragment(kind, pos, end)?;
                    binds.insert(*name, (kind, Bound::One(tokens)));
                    next
                }
                Matcher::Rep(rep) => self.repetition(rep, pos, end, binds)?,
            };
        }
        Some(pos)
    }

    fn group(
        &mut self,
        bracket: Bracket,
        inner: &[Matcher],
        pos: usize,
        end: usize,
        binds: &mut Bindings,
    ) -> Option<usize> {
        let (open, text) = bracket_text(bracket, true);
        let at = self.use_.tokens.get(pos).filter(|_| pos < end);
        let Some(close) = at
            .filter(|t| t.kind == open)
            .and_then(|_| self.use_.closes.get(&pos).copied())
        else {
            self.fail(pos, format!("`{text}`"));
            return None;
        };
        let inside = self.seq(inner, pos + 1, close, binds)?;
        if inside != close {
            let (_, text) = bracket_text(bracket, false);
            self.fail(inside, format!("`{text}`"));
            return None;
        }
        Some(close + 1)
    }

    /// The tokens of the longest form of `kind` from `pos`, and where it ends.
    fn fragment(&mut self, kind: FragKind, pos: usize, end: usize) -> Option<(Vec<Tok>, usize)> {
        let toks = &self.use_.tokens;
        let one = |want: SyntaxKind| (pos < end && toks[pos].kind == want).then(|| pos + 1);
        let next = match kind {
            FragKind::Lower => one(LOWER_IDENT),
            FragKind::Upper => one(UPPER_IDENT),
            FragKind::Block => return self.block(pos).map(|t| (t, self.use_.closes[&pos] + 1)),
            FragKind::Expr | FragKind::Pattern | FragKind::Type => {
                let form = match kind {
                    FragKind::Pattern => Form::Pattern,
                    FragKind::Type => Form::Type,
                    _ => Form::Expr,
                };
                longest(&toks[pos..end], form).map(|taken| pos + taken)
            }
        };
        if let Some(next) = next {
            Some((toks[pos..next].to_vec(), next))
        } else {
            self.fail(pos, expected(kind));
            None
        }
    }

    /// The tokens of the block from `pos`, which must parse as one.
    fn block(&mut self, pos: usize) -> Option<Vec<Tok>> {
        let toks = &self.use_.tokens;
        let close = (toks.get(pos).map(|t| t.kind) == Some(L_CURLY))
            .then(|| self.use_.closes.get(&pos).copied())
            .flatten();
        let Some(close) = close else {
            self.fail(pos, expected(FragKind::Block));
            return None;
        };
        if parse(&toks[pos..=close], Form::Block).error.is_some() {
            self.fail(pos, expected(FragKind::Block));
            return None;
        }
        Some(toks[pos..=close].to_vec())
    }

    fn repetition(
        &mut self,
        rep: &Rep<Matcher>,
        mut pos: usize,
        end: usize,
        binds: &mut Bindings,
    ) -> Option<usize> {
        let mut matches: Vec<Bindings> = Vec::new();
        loop {
            let mut at = pos;
            if !matches.is_empty()
                && let Some(sep) = rep.sep
            {
                match self.use_.tokens.get(at) {
                    Some(t) if at < end && t.kind == sep => at += 1,
                    _ => break,
                }
            }
            let mut found = Bindings::new();
            match self.seq(&rep.items, at, end, &mut found) {
                Some(next) if next > at => {
                    pos = next;
                    matches.push(found);
                }
                _ => break,
            }
        }
        if rep.plus && matches.is_empty() {
            return None;
        }
        let mut names = Vec::new();
        fragments(&rep.items, &mut names);
        for (name, kind) in names {
            let all = matches
                .iter_mut()
                .filter_map(|m| m.remove(&name).map(|(_, b)| b))
                .collect();
            binds.insert(name, (kind, Bound::Many(all)));
        }
        Some(pos)
    }
}

/// How many tokens the longest form of `form` takes, from the first, if one does: the form the
/// parser reads, or, when it reads on into an error, the longest that parses whole before it.
fn longest(toks: &[Tok], form: Form) -> Option<usize> {
    let parsed = parse(toks, form);
    let Some(error) = parsed.error else {
        return (parsed.taken > 0).then_some(parsed.taken);
    };
    (1..=error.min(toks.len()))
        .rev()
        .find(|&n| parse(&toks[..n], form).is_whole(n))
}

/// The fragments that matchers bind, with their kinds.
fn fragments(ms: &[Matcher], out: &mut Vec<(Name, FragKind)>) {
    for m in ms {
        match m {
            Matcher::Frag(name, kind, _) => {
                out.push((*name, kind.unwrap_or(FragKind::Expr)));
            }
            Matcher::Rep(rep) => fragments(&rep.items, out),
            Matcher::Group(_, inner) => fragments(inner, out),
            Matcher::Token(..) => {}
        }
    }
}

fn parse(toks: &[Tok], form: Form) -> stilt_syntax::forms::FormParse {
    let pieces: Vec<Piece<'_>> = toks
        .iter()
        .map(|t| Piece {
            kind: t.kind,
            text: &t.text,
        })
        .collect();
    parse_form(&pieces, form)
}

/// What a fragment of a kind expects, as an error names it.
fn expected(kind: FragKind) -> &'static str {
    match kind {
        FragKind::Expr => "an expression",
        FragKind::Block => "a block",
        FragKind::Pattern => "a pattern",
        FragKind::Type => "a type",
        FragKind::Lower => "a name",
        FragKind::Upper => "an uppercase name",
    }
}
