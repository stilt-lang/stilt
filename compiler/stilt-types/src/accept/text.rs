//! The text of what E0204 says a rule of acceptance needs (facts.closest-rule): each expression
//! written back from the typed body, as the reference interpreter writes it, a block and any other form that
//! holds one as `{ … }`.

use stilt_hir::decls::{Lookup, MemberKindInfo};
use stilt_hir::hir::{BinaryOp, GenericId, Item, LocalId, Mode, Name, UnaryOp};
use stilt_syntax::{TextRange, TextSize};

use super::Need;
use crate::tast::walk::iter;
use crate::tast::{Arg, Callee, Code, Definition, Expr, ExprKind, TypedBody};

/// What writing an expression back reads: its body's locals and the declarations it names.
pub(crate) struct Writer<'a> {
    pub(crate) decls: &'a dyn Lookup,
    pub(crate) body: &'a TypedBody,
    pub(crate) names: &'a dyn Fn(&GenericId) -> Name,
}

/// How tightly an operator binds, as the grammar's levels give it: 10 for a prefix operator and
/// 11 for a postfix one or an atom.
fn level(op: BinaryOp) -> u8 {
    match op {
        BinaryOp::Or => 1,
        BinaryOp::And => 2,
        BinaryOp::Eq | BinaryOp::Ne | BinaryOp::Lt | BinaryOp::Le | BinaryOp::Gt | BinaryOp::Ge => {
            3
        }
        BinaryOp::BitOr => 4,
        BinaryOp::BitXor => 5,
        BinaryOp::BitAnd => 6,
        BinaryOp::Shl | BinaryOp::Shr => 7,
        BinaryOp::Add | BinaryOp::Sub | BinaryOp::AddWrap | BinaryOp::SubWrap => 8,
        BinaryOp::Mul | BinaryOp::Div | BinaryOp::Rem | BinaryOp::MulWrap => 9,
    }
}

fn symbol(op: BinaryOp) -> &'static str {
    match op {
        BinaryOp::Add => "+",
        BinaryOp::Sub => "-",
        BinaryOp::Mul => "*",
        BinaryOp::Div => "/",
        BinaryOp::Rem => "%",
        BinaryOp::AddWrap => "+%",
        BinaryOp::SubWrap => "-%",
        BinaryOp::MulWrap => "*%",
        BinaryOp::Eq => "==",
        BinaryOp::Ne => "!=",
        BinaryOp::Lt => "<",
        BinaryOp::Le => "<=",
        BinaryOp::Gt => ">",
        BinaryOp::Ge => ">=",
        BinaryOp::And => "&&",
        BinaryOp::Or => "||",
        BinaryOp::BitAnd => "&",
        BinaryOp::BitOr => "|",
        BinaryOp::BitXor => "^",
        BinaryOp::Shl => "<<",
        BinaryOp::Shr => ">>",
    }
}

fn quoted(s: &str) -> String {
    let mut out = String::from("\"");
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

impl<'a> Writer<'a> {
    /// The expression at `at` in the body, the outermost one there.
    fn find(&self, at: TextRange) -> Option<&'a Expr> {
        let body: &'a TypedBody = self.body;
        let mut found: Option<&'a Expr> = None;
        let mut find = |e: &'a Expr| {
            if found.is_none() && e.at == at {
                found = Some(e);
            }
        };
        match &body.code {
            Definition::Code(Code::Block(b)) => {
                crate::tast::walk::iter_block(b, &mut |_| {}, &mut find);
            }
            Definition::Code(Code::Expr(e)) => iter(e, &mut |_| {}, &mut find),
            Definition::Native | Definition::Broken => {}
        }
        found
    }

    /// The text of the expression at `at`.
    fn at(&self, at: TextRange) -> String {
        self.find(at)
            .map_or_else(|| "{ … }".to_owned(), |e| self.expr(e))
    }

    /// The text of the expression at `at`, in parentheses unless it is an atom.
    fn wrapped_at(&self, at: TextRange) -> String {
        self.find(at)
            .map_or_else(|| "{ … }".to_owned(), |e| self.wrapped(11, e))
    }

    /// An expression's text.
    pub(crate) fn expr(&self, e: &Expr) -> String {
        self.text(e).0
    }

    /// An expression's text, in parentheses when its operator binds less tightly than `needed`.
    fn wrapped(&self, needed: u8, e: &Expr) -> String {
        let (s, l) = self.text(e);
        if l < needed { format!("({s})") } else { s }
    }

    fn text(&self, e: &Expr) -> (String, u8) {
        let atom = |s: String| (s, 11);
        match &e.kind {
            ExprKind::Int(s) | ExprKind::Float(s) => atom(s.clone()),
            ExprKind::Str(s) => atom(quoted(s)),
            ExprKind::Bool(b) => atom(b.to_string()),
            ExprKind::Local(v) => atom(
                self.body
                    .locals
                    .get(v.0 as usize)
                    .map_or_else(String::new, ToString::to_string),
            ),
            ExprKind::ValueParam(id) => atom((self.names)(id).to_string()),
            ExprKind::Constant(item) => atom(item.name.to_string()),
            ExprKind::MemberConstant(item, name, _) => atom(format!("{}.{name}", item.name)),
            ExprKind::Field(x, f) => atom(format!("{}.{f}", self.wrapped(11, x))),
            ExprKind::TupleField(x, i) => atom(format!("{}.{i}", self.wrapped(11, x))),
            ExprKind::Index(x, k) => atom(format!("{}[{}]", self.wrapped(11, x), self.expr(k))),
            ExprKind::Unary(UnaryOp::Neg, x) => (format!("-{}", self.wrapped(10, x)), 10),
            ExprKind::Unary(UnaryOp::Not, x) => (format!("!{}", self.wrapped(10, x)), 10),
            ExprKind::Binary(op, a, b) => {
                let l = level(*op);
                (
                    format!(
                        "{} {} {}",
                        self.wrapped(l, a),
                        symbol(*op),
                        self.wrapped(l + 1, b)
                    ),
                    l,
                )
            }
            ExprKind::Call(c, _, args, _) | ExprKind::Project(c, _, args, _) => {
                atom(self.call(c, args))
            }
            ExprKind::CallValue(f, args) => {
                atom(format!("{}{}", self.wrapped(11, f), self.arguments(args)))
            }
            ExprKind::Instantiate(x, _) => self.text(x),
            ExprKind::Tuple(es) => atom(format!("({})", self.list(es))),
            ExprKind::List(es) => atom(format!("[{}]", self.list(es))),
            _ => atom("{ … }".to_owned()),
        }
    }

    fn list(&self, es: &[Expr]) -> String {
        es.iter()
            .map(|e| self.expr(e))
            .collect::<Vec<_>>()
            .join(", ")
    }

    fn call(&self, c: &Callee, args: &[Arg]) -> String {
        match (c, args) {
            (Callee::Member(owner, name), [recv, rest @ ..]) if self.is_method(owner, name) => {
                format!(
                    "{}.{name}{}",
                    self.wrapped(11, &recv.value),
                    self.arguments(rest)
                )
            }
            (Callee::TraitMethod(_, name, _), [recv, rest @ ..]) => {
                format!(
                    "{}.{name}{}",
                    self.wrapped(11, &recv.value),
                    self.arguments(rest)
                )
            }
            (Callee::Member(owner, name), _) => {
                format!("{}.{name}{}", owner.name, self.arguments(args))
            }
            (Callee::TraitMethod(_, name, _), []) => format!("{name}()"),
            (Callee::Function(i), _) => format!("{}{}", i.name, self.arguments(args)),
            (Callee::Operation(effect, name), _) => {
                format!("{}.{name}{}", effect.name, self.arguments(args))
            }
        }
    }

    fn is_method(&self, owner: &Item, name: &str) -> bool {
        self.decls
            .inherent_members(owner)
            .iter()
            .any(|m| &*m.name == name && matches!(m.kind, MemberKindInfo::Method(_)))
    }

    fn arguments(&self, args: &[Arg]) -> String {
        let each: Vec<String> = args
            .iter()
            .map(|a| {
                let mode = if a.mode == Mode::Inout { "inout " } else { "" };
                format!("{mode}{}", self.expr(&a.value))
            })
            .collect();
        format!("({})", each.join(", "))
    }

    /// A binding's name.
    fn local(&self, v: LocalId) -> String {
        (self.body.locals.get(v.0 as usize)).map_or_else(String::new, ToString::to_string)
    }

    /// What a rule needs, as E0204 says it after its message (facts.closest-rule), with `line`
    /// giving the line of an offset relative to the body's start.
    #[must_use]
    pub(crate) fn need(&self, need: &Need, line: &dyn Fn(TextSize) -> u32) -> String {
        self.range_need(need, line)
            .or_else(|| self.guard_need(need, line))
            .or_else(|| self.key_need(need, line))
            .or_else(|| self.loop_need(need, line))
            .unwrap_or_default()
    }

    /// What a range loop needs (facts.range-loops).
    fn range_need(&self, need: &Need, line: &dyn Fn(TextSize) -> u32) -> Option<String> {
        let len = |list: TextRange| format!("{}.len()", self.wrapped_at(list));
        Some(match need {
            Need::OutsideClosures => "a range loop needs the index outside closures".to_owned(),
            Need::IndexForm(v) => {
                let i = self.local(*v);
                format!("a range loop needs the index to be `{i}`, `{i} + k` or `{i} - k`")
            }
            Need::StartNonNegative => {
                "a range loop needs it to start at a value known non-negative".to_owned()
            }
            Need::StartAtLeast(k) => {
                format!(
                    "a range loop needs it to start at `{}` or above",
                    self.at(*k)
                )
            }
            Need::EndAt(list, k, end, inclusive) => {
                let wanted = match k {
                    Some(k) => format!("{} - {}", len(*list), self.at(*k)),
                    None => len(*list),
                };
                let end = format!("{}{}", if *inclusive { "..=" } else { "" }, self.at(*end));
                format!("a range loop needs it to end at `{wanted}`, not at `{end}`")
            }
            Need::KeepsLength(list, at) => format!(
                "a range loop needs a body that keeps the length of `{}`, which line {} changes",
                self.at(*list),
                line(*at)
            ),
            _ => return None,
        })
    }

    /// What a guard needs (facts.guards), and a divisor (facts.divisors).
    fn guard_need(&self, need: &Need, line: &dyn Fn(TextSize) -> u32) -> Option<String> {
        let between = "nothing between the test and the";
        Some(match need {
            Need::GuardForm => "a guard needs the index to be a name or a literal".to_owned(),
            Need::LowerTest(i) => format!("a guard needs a test that gives `{} >= 0`", self.at(*i)),
            Need::UpperTest(i, list) => format!(
                "a guard needs a test that gives `{} < {}.len()`",
                self.at(*i),
                self.wrapped_at(*list)
            ),
            Need::GuardWrites(i, at) => format!(
                "a guard needs {between} index to write `{}`, which line {} does",
                self.at(*i),
                line(*at)
            ),
            Need::GuardLength(list, at) => format!(
                "a guard needs {between} index to change the length of `{}`, which line {} does",
                self.at(*list),
                line(*at)
            ),
            Need::DivisorForm => {
                "a divisor needs to be a name or a literal other than 0".to_owned()
            }
            Need::DivisorTest(d) => {
                format!("a divisor needs a test that gives `{} != 0`", self.at(*d))
            }
            Need::DivisorWrites(d, at) => format!(
                "a divisor needs {between} division to write `{}`, which line {} does",
                self.at(*d),
                line(*at)
            ),
            _ => return None,
        })
    }

    /// What a key needs (facts.keys).
    fn key_need(&self, need: &Need, line: &dyn Fn(TextSize) -> u32) -> Option<String> {
        Some(match need {
            Need::KeyForm => {
                "a key needs to be a name or a literal that doesn't interpolate".to_owned()
            }
            Need::KeyType => "a key needs a type whose `Eq` and `Hash` are structural".to_owned(),
            Need::KeyTest(m, k) => {
                let k = self.at(*k);
                format!(
                    "a key needs a test that gives `{}.contains({k})`, or a store of `{k}` \
                     before it",
                    self.wrapped_at(*m)
                )
            }
            Need::KeyWrites(k, at) => format!(
                "a key needs nothing between to write `{}`, which line {} does",
                self.at(*k),
                line(*at)
            ),
            Need::KeyChanges(m, at) => format!(
                "a key needs nothing between to change `{}` but by storing into it, which line \
                 {} does",
                self.at(*m),
                line(*at)
            ),
            _ => return None,
        })
    }

    /// What a counting loop needs (facts.counting-loops), and shrinking recursion
    /// (facts.shrinking-recursion).
    fn loop_need(&self, need: &Need, line: &dyn Fn(TextSize) -> u32) -> Option<String> {
        let step = |v: &LocalId, grows: &bool| {
            let op = if *grows { "+=" } else { "-=" };
            (self.local(*v), op)
        };
        Some(match need {
            Need::Comparison => {
                "a counting loop needs a comparison by `<`, `<=`, `>` or `>=`".to_owned()
            }
            Need::CounterVar => "a counting loop needs a `var` on one side".to_owned(),
            Need::Bound(None) => {
                "a counting loop needs a bound that the loop doesn't change".to_owned()
            }
            Need::Bound(Some(at)) => format!(
                "a counting loop needs a bound that the loop doesn't change, which line {} does",
                line(*at)
            ),
            Need::Step(v, grows) => {
                let (v, op) = step(v, grows);
                format!(
                    "a counting loop needs a statement `{v} {op} s` of the loop's own block, \
                     with `s` known positive"
                )
            }
            Need::ContinueBefore(v, grows, s, at) => {
                let (v, op) = step(v, grows);
                let s = self.at(*s);
                let line = line(*at);
                format!(
                    "a counting loop needs no `continue` before `{v} {op} {s}`, which line {line} is"
                )
            }
            Need::CounterWrites(v, at) => format!(
                "a counting loop needs `{}` written nowhere else, which line {} does",
                self.local(*v),
                line(*at)
            ),
            Need::ShrinkForm => "shrinking recursion needs every self-call to pass `p - s` or \
                                 `p + s` at one parameter"
                .to_owned(),
            Need::ShrinkTest(p, falls, at) => {
                let op = if *falls { ">" } else { "<" };
                format!(
                    "shrinking recursion needs a test that gives `{} {op} b` at the self-call \
                     on line {}",
                    self.local(*p),
                    line(*at)
                )
            }
            _ => return None,
        })
    }
}
