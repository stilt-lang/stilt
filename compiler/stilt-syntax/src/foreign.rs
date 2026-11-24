//! Syntax errors that come from another language's way of writing a construct, such as
//! `let mut`, `&str` or `->` in a `match` arm: each gets a message that names the Stilt form,
//! a help that says why, and, where the edit is plain, a fix that writes the Stilt form
//! (reference/messages.md, "Teach the Stilt form").

use rowan::TextRange;
use stilt_diag::{Edit, Fix};

use crate::SyntaxKind::{self, *};
use crate::stream::Sig;

/// What a syntax error that comes from another language says.
#[derive(Debug)]
pub(crate) struct Foreign {
    pub(crate) message: String,
    pub(crate) help: &'static str,
    pub(crate) fix: Option<Fix>,
}

impl Foreign {
    pub(crate) fn new(message: impl Into<String>, help: &'static str) -> Self {
        Self {
            message: message.into(),
            help,
            fix: None,
        }
    }

    pub(crate) fn fix(self, title: &str, edits: Vec<Edit>) -> Self {
        Self {
            fix: Some(Fix::new(title, edits)),
            ..self
        }
    }
}

/// The tokens of a part around its syntax error.
pub(crate) struct Cx<'t> {
    pub(crate) text: &'t str,
    pub(crate) tokens: &'t [Sig],
    /// The index of the token at which the part breaks.
    pub(crate) at: usize,
}

impl Cx<'_> {
    pub(crate) fn kind(&self, i: usize) -> SyntaxKind {
        self.tokens.get(i).map_or(EOF, |t| t.kind)
    }

    /// The token `n` places before the error's, if there is one.
    pub(crate) fn before(&self, n: usize) -> Option<usize> {
        self.at.checked_sub(n)
    }

    pub(crate) fn kind_before(&self, n: usize) -> SyntaxKind {
        self.before(n).map_or(EOF, |i| self.kind(i))
    }

    /// The kind of the token before token `i`, or the end for the first.
    pub(crate) fn kind_before_token(&self, i: usize) -> SyntaxKind {
        i.checked_sub(1).map_or(EOF, |j| self.kind(j))
    }

    /// The text of token `i`: none for a separator that a newline makes, or the end.
    pub(crate) fn word(&self, i: usize) -> &str {
        match self.tokens.get(i) {
            Some(t) if !matches!(t.kind, SEP | EOF) => &self.text[t.range],
            _ => "",
        }
    }

    pub(crate) fn word_before(&self, n: usize) -> &str {
        self.before(n).map_or("", |i| self.word(i))
    }

    pub(crate) fn range(&self, i: usize) -> TextRange {
        self.tokens[i].range
    }

    /// The span from the start of token `i` to the end of token `j`.
    pub(crate) fn through(&self, i: usize, j: usize) -> TextRange {
        TextRange::new(self.range(i).start(), self.range(j).end())
    }

    /// Whether tokens `i` and `i + 1` touch, as the two `:` of `::` do.
    pub(crate) fn touching(&self, i: usize) -> bool {
        i + 1 < self.tokens.len() && self.range(i).end() == self.range(i + 1).start()
    }

    /// The span of token `i` and the blanks after it on its line.
    pub(crate) fn with_blanks(&self, i: usize) -> TextRange {
        let end = usize::from(self.range(i).end());
        let blanks =
            self.text[end..].len() - self.text[end..].trim_start_matches([' ', '\t']).len();
        TextRange::new(self.range(i).start(), self.range(i).end() + offset(blanks))
    }

    /// The index of the bracket that opens the one that token `close` closes.
    pub(crate) fn opening(&self, close: usize) -> Option<usize> {
        if !matches!(self.kind(close), R_PAREN | R_BRACK | R_CURLY) {
            return None;
        }
        let mut depth = 0usize;
        for i in (0..=close).rev() {
            match self.kind(i) {
                R_PAREN | R_BRACK | R_CURLY => depth += 1,
                L_PAREN | L_BRACK | L_CURLY if depth == 1 => return Some(i),
                L_PAREN | L_BRACK | L_CURLY => depth -= 1,
                _ => {}
            }
        }
        None
    }

    /// The index of the bracket that closes the one that token `open` opens.
    pub(crate) fn closing(&self, open: usize) -> Option<usize> {
        let mut depth = 0usize;
        for i in open..self.tokens.len() {
            match self.kind(i) {
                L_PAREN | L_BRACK | L_CURLY => depth += 1,
                R_PAREN | R_BRACK | R_CURLY if depth == 1 => return Some(i),
                R_PAREN | R_BRACK | R_CURLY => depth = depth.checked_sub(1)?,
                _ => {}
            }
        }
        None
    }

    /// The index of the token after the last one of the statement that holds token `from`:
    /// a separator or a comma outside every bracket, or the bracket that closes the one it is in.
    pub(crate) fn statement_end(&self, from: usize) -> usize {
        let mut depth = 0usize;
        for i in from..self.tokens.len() {
            match self.kind(i) {
                L_PAREN | L_BRACK | L_CURLY => depth += 1,
                R_PAREN | R_BRACK | R_CURLY | SEP | COMMA | EOF if depth == 0 => return i,
                R_PAREN | R_BRACK | R_CURLY => depth -= 1,
                _ => {}
            }
        }
        self.tokens.len()
    }

    /// The index of the first token of the statement that holds token `from`, going back to a
    /// separator, a bracket left open, or a `=`, `,`, `=>` or `return` outside brackets.
    pub(crate) fn statement_start(&self, from: usize) -> usize {
        let mut depth = 0usize;
        for i in (0..from).rev() {
            match self.kind(i) {
                R_PAREN | R_BRACK | R_CURLY => depth += 1,
                L_PAREN | L_BRACK | L_CURLY | SEP | EQ | COMMA | FAT_ARROW | RETURN_KW
                    if depth == 0 =>
                {
                    return i + 1;
                }
                L_PAREN | L_BRACK | L_CURLY => depth -= 1,
                _ => {}
            }
        }
        0
    }

    /// The index of the `{` of the `match` or `catch` whose arms hold token `from` outside
    /// every other bracket.
    pub(crate) fn arms(&self, from: usize) -> Option<usize> {
        let mut depth = 0usize;
        let mut open = None;
        for i in (0..from).rev() {
            match self.kind(i) {
                R_PAREN | R_BRACK | R_CURLY => depth += 1,
                L_CURLY if depth == 0 => {
                    open = Some(i);
                    break;
                }
                L_PAREN | L_BRACK if depth == 0 => return None,
                L_PAREN | L_BRACK | L_CURLY => depth -= 1,
                _ => {}
            }
        }
        let open = open?;
        let start = self.statement_start(open);
        (start..open)
            .any(|i| matches!(self.kind(i), MATCH_KW | CATCH_KW))
            .then_some(open)
    }

    /// The indexes of the tokens of `kind` directly inside the brackets that open at `open`.
    pub(crate) fn inside(&self, open: usize, kind: SyntaxKind) -> Vec<usize> {
        let mut depth = 0usize;
        let mut found = Vec::new();
        for i in open + 1..self.tokens.len() {
            match self.kind(i) {
                L_PAREN | L_BRACK | L_CURLY => depth += 1,
                R_PAREN | R_BRACK | R_CURLY if depth == 0 => break,
                R_PAREN | R_BRACK | R_CURLY => depth -= 1,
                k if k == kind && depth == 0 => found.push(i),
                _ => {}
            }
        }
        found
    }
}

fn offset(n: usize) -> rowan::TextSize {
    rowan::TextSize::from(u32::try_from(n).expect("a source file is under 4 GiB"))
}

/// What the syntax error at `cx.at` says, if it comes from another language.
pub(crate) fn explain(cx: &Cx<'_>) -> Option<Foreign> {
    let rules: [fn(&Cx<'_>) -> Option<Foreign>; 10] = [
        crate::foreign_words::words,
        crate::foreign_words::declarations,
        crate::foreign_items::items,
        references,
        arms,
        closures,
        operators,
        crate::foreign_forms::forms,
        crate::foreign_marks::unwrap,
        crate::foreign_marks::power,
    ];
    rules.iter().find_map(|rule| rule(cx))
}

/// `&T` and `&mut T` in a signature, `&self`, and `&x` in a call.
fn references(cx: &Cx<'_>) -> Option<Foreign> {
    if !matches!(cx.kind(cx.at), AMP | AMP2) {
        return None;
    }
    let mutable = cx.word(cx.at + 1) == "mut";
    let last = if mutable { cx.at + 1 } else { cx.at };
    let reference = TextRange::new(cx.range(cx.at).start(), cx.with_blanks(last).end());
    let help = "A parameter takes a value, which the function can't change. One written \
                `inout` changes the caller's variable, which the call marks `inout` too.";
    if cx.kind(last + 1) == SELF_KW && mutable {
        return Some(crate::foreign_marks::inout_self(reference));
    }
    if cx.kind(last + 1) == SELF_KW {
        let found = Foreign::new(
            "Stilt has no references: a method takes `self`, without `&`",
            "A method's receiver is a value, `self`; one that changes it takes `inout self`.",
        );
        return Some(found.fix("write `self`", vec![Edit::delete(reference)]));
    }
    match cx.kind_before(1) {
        COLON | THIN_ARROW | L_ANGLE => {}
        L_PAREN | COMMA => {
            let found = Foreign::new("Stilt has no references: pass the value itself", help);
            return Some(found.fix("pass the value", vec![Edit::delete(reference)]));
        }
        _ => return None,
    }
    let name = cx.before(2).filter(|&i| {
        matches!(cx.kind(i), LOWER_IDENT) && matches!(cx.kind_before(3), L_PAREN | COMMA)
    });
    match (mutable, name) {
        (true, Some(name)) => {
            let found = Foreign::new(
                "Stilt has no references: a parameter that the function changes is `inout`",
                help,
            );
            let edits = vec![
                Edit::insert(cx.range(name).start(), "inout "),
                Edit::delete(reference),
            ];
            Some(found.fix(&format!("write `inout {}`", cx.word(name)), edits))
        }
        (true, None) => Some(Foreign::new(
            "Stilt has no references or `&mut` types",
            help,
        )),
        (false, _) => {
            let found = Foreign::new("Stilt has no references: a parameter takes a value", help);
            Some(found.fix("take the value", vec![Edit::delete(reference)]))
        }
    }
}

/// `->` or `:` between a `match` arm's pattern and its body, which every arm of the match then
/// writes the same way, so the fix writes each as `=>`.
fn arms(cx: &Cx<'_>) -> Option<Foreign> {
    let kind = cx.kind(cx.at);
    if !matches!(kind, THIN_ARROW | COLON) || doubled(cx, cx.at) {
        return None;
    }
    let open = cx.arms(cx.at)?;
    let written = cx.word(cx.at);
    let edits = cx
        .inside(open, kind)
        .into_iter()
        .filter(|&i| !doubled(cx, i))
        .map(|i| Edit::replace(cx.range(i), if kind == COLON { " =>" } else { "=>" }))
        .collect();
    let found = Foreign::new(
        format!("a `match` arm is written with `=>`, not `{written}`"),
        "Each arm is a pattern, `=>` and the arm's value, as `Some(v) => v`.",
    );
    Some(found.fix("write `=>`", edits))
}

/// Whether the `:` at token `i` is half of a `::`.
fn doubled(cx: &Cx<'_>, i: usize) -> bool {
    let colon = |j: usize| cx.kind(j) == COLON;
    (colon(i + 1) && cx.touching(i)) || (i > 0 && colon(i - 1) && cx.touching(i - 1))
}

/// `=>` after a closure's parameters, and `(x) => body`, a closure of JavaScript's.
fn closures(cx: &Cx<'_>) -> Option<Foreign> {
    if cx.kind(cx.at) != FAT_ARROW {
        return None;
    }
    let help = "A closure is its parameters between `|`, then its body: `|x| x * 2`, or \
                `|a, b| { … }` for a block.";
    match cx.kind_before(1) {
        PIPE => {
            let found = Foreign::new(
                "a closure's body follows its parameters, without `=>`",
                help,
            );
            Some(found.fix("delete the `=>`", vec![Edit::delete(cx.with_blanks(cx.at))]))
        }
        R_PAREN => {
            let open = cx.opening(cx.at - 1)?;
            let params = TextRange::new(cx.range(open).end(), cx.range(cx.at - 1).start());
            let written = TextRange::new(cx.range(open).start(), cx.range(cx.at).end());
            let found = Foreign::new("Stilt writes a closure as `|x| x * 2`", help);
            let edit = Edit::replace(written, format!("|{}|", &cx.text[params]));
            Some(found.fix("write the closure with `|`", vec![edit]))
        }
        _ => None,
    }
}

/// `x++`, `?` after a call, `? :`, `===`, `!==`, `::` and `:=`.
fn operators(cx: &Cx<'_>) -> Option<Foreign> {
    let at = cx.at;
    match cx.kind(at) {
        PLUS if cx.kind_before(1) == PLUS && cx.touching(at - 1) => {
            let found = Foreign::new(
                "Stilt has no `++`: write `+= 1`",
                "A variable changes only by an assignment, such as `i += 1`.",
            );
            let edit = Edit::replace(cx.through(at - 1, at), " += 1");
            Some(found.fix("write `+= 1`", vec![edit]))
        }
        QUESTION => crate::foreign_marks::optional(cx).or_else(|| Some(question(cx))),
        EQ if cx
            .before(1)
            .is_some_and(|i| matches!(cx.kind(i), EQ2 | NEQ) && cx.touching(i)) =>
        {
            let same = cx.word(at - 1).to_owned();
            let found = Foreign::new(
                format!("Stilt compares with `{same}`, which never converts its operands"),
                "Two values compare only when they have the same type, so one `==` says it all.",
            );
            Some(found.fix(&format!("write `{same}`"), vec![Edit::delete(cx.range(at))]))
        }
        COLON if cx.kind(at + 1) == COLON && cx.touching(at) => {
            Some(crate::foreign_marks::paths(cx))
        }
        COLON if cx.kind(at + 1) == EQ && cx.touching(at) => {
            let start = cx.statement_start(at);
            let found = Foreign::new(
                "Stilt declares a binding with `let`, not `:=`",
                "A `let` binding never changes, and a `var` binding can.",
            );
            let edits = vec![
                Edit::insert(cx.range(start).start(), "let "),
                Edit::replace(cx.through(at, at + 1), "="),
            ];
            Some(found.fix("write `let`", edits))
        }
        _ => None,
    }
}

/// `?` after a call, Rust's way of passing an error on, or a condition's `? :`.
fn question(cx: &Cx<'_>) -> Foreign {
    let at = cx.at;
    let end = cx.statement_end(at);
    let mut depth = 0usize;
    let colon = (at + 1..end).find(|&i| match cx.kind(i) {
        L_PAREN | L_BRACK | L_CURLY => {
            depth += 1;
            false
        }
        R_PAREN | R_BRACK | R_CURLY => {
            depth = depth.saturating_sub(1);
            false
        }
        COLON => depth == 0,
        _ => false,
    });
    if let Some(colon) = colon {
        let start = cx.statement_start(at);
        let found = Foreign::new(
            "Stilt has no `? :`: an `if` gives a value, as `if c { a } else { b }`",
            "An `if` with `else` is an expression, so it stands wherever a value does.",
        );
        let edits = vec![
            Edit::insert(cx.range(start).start(), "if "),
            Edit::replace(cx.range(at), "{"),
            Edit::replace(cx.range(colon), "} else {"),
            Edit::insert(cx.range(end - 1).end(), " }"),
        ];
        return found.fix("write an `if`", edits);
    }
    let found = Foreign::new(
        "Stilt marks a call that can raise with `try` before it, not `?` after it",
        "`try` marks the calls that can raise, and passes their errors on to the caller, whose \
         row names the error type.",
    );
    let start = call_start(cx, at);
    let edits = vec![
        Edit::insert(cx.range(start).start(), "try "),
        Edit::delete(cx.range(at)),
    ];
    found.fix("write `try`", edits)
}

/// The first token of the chain of calls, fields and indexes that ends just before `at`.
fn call_start(cx: &Cx<'_>, at: usize) -> usize {
    let mut i = at;
    while let Some(last) = i.checked_sub(1) {
        let first = match cx.kind(last) {
            R_PAREN | R_BRACK => cx.opening(last).unwrap_or(last),
            LOWER_IDENT | UPPER_IDENT | SELF_KW | DOT => last,
            _ => break,
        };
        i = first;
    }
    i
}
