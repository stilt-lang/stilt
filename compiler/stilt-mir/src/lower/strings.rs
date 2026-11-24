//! Interpolation (lexical.interpolation; std.width-fill-and-alignment, std.precision and
//! std.integer-kinds): each splice is evaluated and shown in turn, from left to right, then
//! formatted by its spec, and the pieces are joined.

use stilt_types::tast::{Expr, Segment};
use stilt_types::ty::Ty;

use super::Lower;
use crate::mir::{Const, Operand, Repr, Runtime, Rvalue};
use crate::repr::num_kind;

/// A format spec, `[[fill]align][width][.precision][kind]`, as lexical.format-specs parses it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Spec {
    fill: char,
    /// `<`, `^` or `>`, or 0 for none.
    align: u8,
    width: u64,
    precision: Option<u64>,
    /// `x`, `X`, `o`, `b` or `e`, or 0 for none.
    kind: u8,
}

const LIMIT: u64 = 65535;

fn number(text: &[char], i: usize) -> Option<(u64, usize)> {
    if i + 1 < text.len() && text[i] == '0' && text[i + 1].is_ascii_digit() {
        return None;
    }
    let mut j = i;
    let mut value = 0u64;
    while j < text.len() && text[j].is_ascii_digit() {
        value = value * 10 + u64::from(text[j].to_digit(10)?);
        if value > LIMIT {
            return None;
        }
        j += 1;
    }
    Some((value, j))
}

/// Parses a spec, as the type checker already accepted it.
pub(crate) fn parse_spec(text: &str) -> Option<Spec> {
    let chars: Vec<char> = text.chars().collect();
    let is_align = |c: char| matches!(c, '<' | '^' | '>');
    let (fill, align, mut i) = if chars.len() > 1 && is_align(chars[1]) && chars[0] != '{' {
        (chars[0], chars[1] as u8, 2)
    } else if !chars.is_empty() && is_align(chars[0]) {
        (' ', chars[0] as u8, 1)
    } else {
        (' ', 0, 0)
    };
    let (width, j) = number(&chars, i)?;
    i = j;
    let precision = if i < chars.len() && chars[i] == '.' {
        let (p, j) = number(&chars, i + 1)?;
        if j == i + 1 {
            return None;
        }
        i = j;
        Some(p)
    } else {
        None
    };
    let kind = if i < chars.len() && "xXobe".contains(chars[i]) {
        i += 1;
        chars[i - 1] as u8
    } else {
        0
    };
    (i == chars.len()).then_some(Spec {
        fill,
        align,
        width,
        precision,
        kind,
    })
}

/// The two words of the spec `text` as the runtime takes it, if it parses.
#[must_use]
pub fn spec_words(text: &str) -> Option<(u64, u64)> {
    parse_spec(text).map(Spec::words)
}

impl Spec {
    /// The spec as the runtime takes it: the fill, alignment and kind in one word, and the
    /// width and precision in another.
    fn words(self) -> (u64, u64) {
        let first =
            u64::from(self.fill as u32) << 16 | u64::from(self.align) << 8 | u64::from(self.kind);
        let precision = self.precision.unwrap_or(0xffff_ffff);
        (first, self.width << 32 | precision)
    }
}

impl Lower<'_> {
    pub(crate) fn interpolated(&mut self, segments: &[Segment]) -> Operand {
        let pieces = segments
            .iter()
            .map(|segment| match segment {
                Segment::Text(s) => Operand::Const(Const::Str(s.as_str().into())),
                Segment::Splice(x, spec) => self.splice(x, spec.as_deref()),
            })
            .collect();
        self.concat(pieces)
    }

    /// A splice's text. A spec formats a number where the splice is written, and pads any
    /// other value's text (std.width-fill-and-alignment).
    fn splice(&mut self, x: &Expr, spec: Option<&str>) -> Operand {
        let v = self.expr(x);
        let loc = self.loc_at(x.at);
        let kind = num_kind(&x.ty);
        let spec = spec.and_then(parse_spec);
        match (spec, kind) {
            (None, _) => self.show(&x.ty, v, loc),
            (Some(spec), Some(k)) => {
                let value = super::words::word(&v, 0);
                self.format(spec, Operand::word(k.code()), value, Operand::word(0))
            }
            (Some(spec), None) => {
                let shown = self.show(&x.ty, v, loc);
                self.format(spec, Operand::word(255), Operand::word(0), shown)
            }
        }
    }

    pub(crate) fn show(&mut self, ty: &Ty, v: Vec<Operand>, loc: Operand) -> Operand {
        self.trait_call("Show", "show", ty, vec![v], loc)
    }

    fn format(&mut self, spec: Spec, kind: Operand, value: Operand, shown: Operand) -> Operand {
        let (first, second) = spec.words();
        let args = vec![
            kind,
            value,
            shown,
            Operand::word(first),
            Operand::word(second),
        ];
        self.b
            .define_op(Repr::Heap, Rvalue::Runtime(Runtime::Format, args))
    }
}
