//! `for (x, y) in xs.zip(ys)` and `for (i, x) in xs.enumerate(start)`, whose pairs the loop
//! reads from the lists it was given rather than from the list of pairs the call would build:
//! element `i` of each list, or `start + i` and element `i`, for `i` below the shorter length
//! (expressions.for-iterables). Both functions of `List` only build that list, so the loop runs
//! as it would over it, and allocates nothing for it (goal debug-speed).

use stilt_types::tast::{Arg, Block, Callee, Expr, ExprKind, Pat, PatKind};

use super::Lower;
use crate::mir::{NumKind, Operand, Prim, Repr, Runtime, Rvalue};

/// What a loop reads its pairs from.
pub(crate) enum Pairs<'e> {
    /// The two lists of `xs.zip(ys)`.
    Zip(&'e Expr, &'e Expr),
    /// The list and the first index of `xs.enumerate(start)`.
    Enumerate(&'e Expr, &'e Expr),
}

/// The pairs that a `for` loop with the pattern `p` over `source` reads from its lists: when
/// `source` is a call of `List.zip` or `List.enumerate` and `p` a tuple pattern of two parts.
pub(crate) fn pairs<'e>(p: &Pat, source: &'e Expr) -> Option<Pairs<'e>> {
    let PatKind::Tuple(parts) = &p.kind else {
        return None;
    };
    let ExprKind::Call(Callee::Member(owner, name), _, args, _) = &source.kind else {
        return None;
    };
    if parts.len() != 2 || &*owner.home != "std.prelude" || &*owner.name != "List" {
        return None;
    }
    let [Arg { value: a, .. }, Arg { value: b, .. }] = args.as_slice() else {
        return None;
    };
    match &**name {
        "zip" => Some(Pairs::Zip(a, b)),
        // `start + i` can't overflow from a small start, so the loop needn't check it, as
        // `enumerate`'s addition does.
        "enumerate" if small(b) => Some(Pairs::Enumerate(a, b)),
        _ => None,
    }
}

/// Whether `e` is an integer literal from 0 to 2^32.
fn small(e: &Expr) -> bool {
    matches!(&e.kind, ExprKind::Int(n) if n.parse::<u64>().is_ok_and(|n| n <= 1 << 32))
}

impl Lower<'_> {
    /// The loop over the pairs `pairs` gives, with the tuple pattern of two parts `pattern`
    /// and the body `body`.
    pub(crate) fn for_pairs(&mut self, pattern: &Pat, pairs: &Pairs<'_>, body: &Block) {
        let PatKind::Tuple(parts) = &pattern.kind else {
            return;
        };
        let (first, second) = match pairs {
            Pairs::Zip(xs, ys) | Pairs::Enumerate(xs, ys) => (*xs, *ys),
        };
        // The receiver and the argument, in the order the call evaluates them.
        let xs = self.list_of(first);
        let other = self.expr1(second);
        let other = self.b.define_op(self.repr(&second.ty), Rvalue::Use(other));
        let len = self.len_of(xs.clone());
        let len = match pairs {
            Pairs::Zip(..) => {
                let theirs = self.len_of(other.clone());
                let min = Prim::Min(NumKind::I64);
                let shorter = Rvalue::Prim(min, vec![len, theirs], Operand::word(0));
                self.b.define_op(Repr::Scalar, shorter)
            }
            Pairs::Enumerate(..) => len,
        };
        let index = self.b.temp(Repr::Scalar);
        self.b.assign(index, Rvalue::Use(Operand::word(0)));
        let (head, start, next, exit) = self.loop_blocks();
        self.b.goto(head);
        self.b.switch_to(head);
        let more = self.lt(NumKind::I64, Operand::Local(index), len);
        self.b.branch(more, start, exit);
        self.b.switch_to(start);
        let i = Operand::Local(index);
        let at = self.loc_at(first.at);
        let (left, right) = match pairs {
            Pairs::Zip(..) => {
                let x = self.list_element(xs, i.clone(), at.clone(), &parts[0].ty);
                let y = self.list_element(other, i, at, &parts[1].ty);
                (x, y)
            }
            Pairs::Enumerate(..) => {
                let add = Prim::AddWrap(NumKind::I64);
                let counted = Rvalue::Prim(add, vec![other, i.clone()], Operand::word(0));
                let counted = vec![self.b.define_op(Repr::Scalar, counted)];
                (counted, self.list_element(xs, i, at, &parts[1].ty))
            }
        };
        self.binding(&parts[0], left, false, None);
        self.binding(&parts[1], right, false, None);
        self.loop_body(body, exit, next);
        self.b.switch_to(next);
        self.step(index);
        self.b.goto(head);
        self.b.switch_to(exit);
    }

    /// The list that `e` gives, held for the loop.
    fn list_of(&mut self, e: &Expr) -> Operand {
        let list = self.expr1(e);
        self.b.define_op(Repr::Heap, Rvalue::Use(list))
    }

    fn len_of(&mut self, list: Operand) -> Operand {
        self.b
            .define_op(Repr::Scalar, Rvalue::Runtime(Runtime::ListLen, vec![list]))
    }
}
