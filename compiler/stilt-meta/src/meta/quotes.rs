//! Quotes in a macro's run (macros.splices and macros.quote-hygiene): a quote's tokens with its
//! splices filled, each splice standing as one form, as if parenthesized, and the code placed at
//! the use. The names a quote writes are marked with its evaluation, so that they resolve where it
//! is written, and those it binds are fresh in the expansion.

use std::sync::{Arc, LazyLock};

use stilt_hir::hir::{CodeForm, Name, QuoteTok};
use stilt_hir::procs::{Origin, Rel};
use stilt_syntax::SyntaxKind::{
    self, COMMA, FALSE_KW, FLOAT, INT, L_CURLY, L_PAREN, LOWER_IDENT, MINUS, R_BRACK, R_CURLY,
    R_PAREN, STRING, TRUE_KW, UPPER_IDENT,
};
use stilt_types::tast;

use crate::eval::{Flow, Frame, Machine, R, panic, reserve};
use crate::value::{Code, Lex, Meta, Value};

/// The brackets and the comma that a quote writes around and between what it holds, each
/// interned once.
struct Marks {
    l_curly: Name,
    r_curly: Name,
    l_paren: Name,
    r_paren: Name,
    comma: Name,
}

static MARKS: LazyLock<Marks> = LazyLock::new(|| Marks {
    l_curly: Name::from("{"),
    r_curly: Name::from("}"),
    l_paren: Name::from("("),
    r_paren: Name::from(")"),
    comma: Name::from(","),
});

/// A string's value as a literal that never interpolates: `\`, `"` and `{` escaped.
fn literal(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '{' => out.push_str("\\{"),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

impl<'a> Machine<'a> {
    /// A quote's code: its splices evaluated left to right, and its tokens with them filled.
    pub(crate) fn quote(&mut self, fr: &mut Frame<'a>, quote: &'a tast::Quote) -> R<'a> {
        let id = self.io.quotes;
        self.io.quotes += 1;
        self.io.quote.clone_from(&quote.written);
        let origin = Origin::Quote {
            home: quote.home,
            id,
        };
        let own = |kind: SyntaxKind, text: Name| Lex {
            kind,
            text,
            origin: origin.clone(),
        };
        let mut out = Vec::with_capacity(quote.tokens.len() + 2);
        if quote.form == CodeForm::Expr {
            out.push(own(L_CURLY, MARKS.l_curly));
        }
        let mut pos = 0;
        while pos < quote.tokens.len() {
            match &quote.tokens[pos] {
                QuoteTok::Token(kind, text) => out.push(own(*kind, *text)),
                QuoteTok::Negative(kind, digits) => {
                    out.extend(negative(*kind, digits, self.io.use_rel()));
                }
                QuoteTok::Splice(index) => {
                    let Some(splice) = quote.splices.get(*index as usize) else {
                        pos += 1;
                        continue;
                    };
                    let value = self.expr(fr, &splice.value)?;
                    if splice.spread {
                        let next = quote.tokens.get(pos + 1);
                        pos += self.spread(&value, next, &own, &mut out)?;
                    } else {
                        self.written(&value, &own, &mut out)?;
                    }
                }
            }
            pos += 1;
        }
        if quote.form == CodeForm::Expr {
            out.push(own(R_CURLY, MARKS.r_curly));
        }
        reserve(out.len() * std::mem::size_of::<Lex>())?;
        Ok(Value::meta(Meta::Code(Code {
            tokens: Arc::new(crate::value::Counted::new(out)),
            span: self.io.use_span(),
            form: quote.form,
        })))
    }

    /// A spread's elements, separated by commas: an empty one takes the comma after it, and
    /// a closing bracket after one keeps it a list of elements, as `(x,)` is a tuple. Gives
    /// how many of the quote's tokens after it it took.
    fn spread(
        &mut self,
        v: &Value<'a>,
        next: Option<&QuoteTok>,
        own: &Own<'_>,
        out: &mut Vec<Lex>,
    ) -> Result<usize, Flow<'a>> {
        let items = v.as_list().to_vec();
        let next_kind = match next {
            Some(QuoteTok::Token(kind, _)) => Some(*kind),
            _ => None,
        };
        if items.is_empty() {
            return Ok(usize::from(next_kind == Some(COMMA)));
        }
        for (j, x) in items.iter().enumerate() {
            if j > 0 {
                out.push(own(COMMA, MARKS.comma));
            }
            self.written(x, own, out)?;
        }
        if matches!(next_kind, Some(R_PAREN | R_BRACK | R_CURLY)) {
            out.push(own(COMMA, MARKS.comma));
        }
        Ok(0)
    }

    /// The tokens a value writes where a splice stands: code as one form, a name, or a
    /// literal, at the use.
    fn written(
        &mut self,
        v: &Value<'a>,
        own: &Own<'_>,
        out: &mut Vec<Lex>,
    ) -> Result<(), Flow<'a>> {
        let at = self.io.use_rel();
        let lit = |kind: SyntaxKind, text: &str| Lex {
            kind,
            text: Name::from(text),
            origin: Origin::Placed { at, user: false },
        };
        match v {
            Value::Meta(m) => match &**m {
                Meta::Code(c) if c.form == CodeForm::Field => out.extend(c.tokens.iter().cloned()),
                Meta::Code(c) => {
                    out.push(own(L_PAREN, MARKS.l_paren));
                    out.extend(c.tokens.iter().cloned());
                    out.push(own(R_PAREN, MARKS.r_paren));
                }
                Meta::Name(n) => {
                    let upper = n.text.starts_with(|c: char| c.is_ascii_uppercase());
                    out.push(Lex {
                        kind: if upper { UPPER_IDENT } else { LOWER_IDENT },
                        text: Name::from(&*n.text),
                        origin: n.origin.clone(),
                    });
                }
                _ => unreachable!(
                    "a splice's value is code or a name, as checking found (macros.splices)"
                ),
            },
            Value::Str(s) => out.push(lit(STRING, &literal(s.get()))),
            Value::Bool(b) => out.push(lit(
                if *b { TRUE_KW } else { FALSE_KW },
                if *b { "true" } else { "false" },
            )),
            Value::Int(x, _) => number(INT, &x.to_string(), (at, own), out),
            Value::Float(x, f32) => {
                if !x.is_finite() {
                    return panic("splice", "a NaN or an infinite float can't be spliced");
                }
                number(
                    FLOAT,
                    &crate::structural::float_text(*x, *f32),
                    (at, own),
                    out,
                );
            }
            _ => unreachable!(
                "a splice's value is code, a name or a literal's, as checking found (macros.splices and macros.literal-splices)"
            ),
        }
        Ok(())
    }
}

/// What makes a token of the quote's own.
type Own<'f> = dyn Fn(SyntaxKind, Name) -> Lex + 'f;

/// The tokens of a number at the use `at`. A negative one is written in parentheses, its `-`
/// directly before its digits, so that the `-` is part of the literal when its range is checked
/// (numbers.negative-literals): the `-` stands at the use's first byte and the digits at the rest.
fn number(kind: SyntaxKind, text: &str, (at, own): (Rel, &Own<'_>), out: &mut Vec<Lex>) {
    let placed = |kind, text: &str, at| Lex {
        kind,
        text: Name::from(text),
        origin: Origin::Placed { at, user: false },
    };
    let Some(digits) = text.strip_prefix('-') else {
        out.push(placed(kind, text, at));
        return;
    };
    out.push(own(L_PAREN, MARKS.l_paren));
    out.extend(negative(kind, digits, at));
    out.push(own(R_PAREN, MARKS.r_paren));
}

/// A `-` and the digits of a number at the use `at`, the `-` at the use's first byte and the
/// digits directly after it, so that the `-` is part of the literal when its range is checked
/// (numbers.negative-literals), as a quote's own `-32768` is.
fn negative(kind: SyntaxKind, digits: &str, at: Rel) -> [Lex; 2] {
    let placed = |kind, text: &str, at| Lex {
        kind,
        text: Name::from(text),
        origin: Origin::Placed { at, user: false },
    };
    let minus = Rel {
        start: at.start,
        end: at.start + 1,
    };
    let rest = Rel {
        start: at.start + 1,
        end: at.end.max(at.start + 2),
    };
    [placed(MINUS, "-", minus), placed(kind, digits, rest)]
}
