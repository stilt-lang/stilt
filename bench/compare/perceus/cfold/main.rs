//! cfold: builds an expression of 2^20 sums, reassociates it into a chain and folds its
//! constants, then evaluates it before and after (Reinking et al., Perceus, PLDI 2021). Each pass
//! owns the expression, so it rebuilds it in the nodes it takes apart.

enum Expr {
    #[expect(
        dead_code,
        reason = "a variable's name is never read: every variable evaluates to 0"
    )]
    Var(i64),
    Val(i64),
    Add(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
}

use Expr::{Add, Mul, Val, Var};

fn constant(e: &Expr) -> Option<i64> {
    if let Val(n) = e { Some(*n) } else { None }
}

fn make(n: i64, v: i64) -> Expr {
    if n == 0 {
        if v == 0 { Var(1) } else { Val(v) }
    } else {
        Add(
            Box::new(make(n - 1, v + 1)),
            Box::new(make(n - 1, (v - 1).max(0))),
        )
    }
}

fn append_add(a: Expr, b: Expr) -> Expr {
    match a {
        Add(x, mut y) => {
            *y = append_add(*y, b);
            Add(x, y)
        }
        a => Add(Box::new(a), Box::new(b)),
    }
}

fn append_mul(a: Expr, b: Expr) -> Expr {
    match a {
        Mul(x, mut y) => {
            *y = append_mul(*y, b);
            Mul(x, y)
        }
        a => Mul(Box::new(a), Box::new(b)),
    }
}

fn reassoc(e: Expr) -> Expr {
    match e {
        Add(a, b) => append_add(reassoc(*a), reassoc(*b)),
        Mul(a, b) => append_mul(reassoc(*a), reassoc(*b)),
        e => e,
    }
}

fn fold(e: Expr) -> Expr {
    match e {
        Add(mut a, mut b) => {
            *a = fold(*a);
            *b = fold(*b);
            match (constant(&a), *b) {
                (Some(x), Val(y)) => Val(x + y),
                (Some(x), Add(mut f, mut g)) => {
                    if let Some(y) = constant(&g) {
                        *g = Val(x + y);
                        Add(g, f)
                    } else if let Some(y) = constant(&f) {
                        *f = Val(x + y);
                        Add(f, g)
                    } else {
                        Add(a, Box::new(Add(f, g)))
                    }
                }
                (_, b) => Add(a, Box::new(b)),
            }
        }
        Mul(mut a, mut b) => {
            *a = fold(*a);
            *b = fold(*b);
            match (constant(&a), *b) {
                (Some(x), Val(y)) => Val(x * y),
                (Some(x), Mul(mut f, mut g)) => {
                    if let Some(y) = constant(&g) {
                        *g = Val(x * y);
                        Mul(g, f)
                    } else if let Some(y) = constant(&f) {
                        *f = Val(x * y);
                        Mul(f, g)
                    } else {
                        Mul(a, Box::new(Mul(f, g)))
                    }
                }
                (_, b) => Mul(a, Box::new(b)),
            }
        }
        e => e,
    }
}

fn eval(e: &Expr) -> i64 {
    match e {
        Var(_) => 0,
        Val(v) => *v,
        Add(a, b) => eval(a) + eval(b),
        Mul(a, b) => eval(a) * eval(b),
    }
}

pub(crate) fn main() {
    let e = make(20, 1);
    println!("{}", eval(&e));
    println!("{}", eval(&fold(reassoc(e))));
}
