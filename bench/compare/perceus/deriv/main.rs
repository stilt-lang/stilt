//! deriv: differentiates x^x ten times, simplifying each derivative as it is built, and prints the
//! size of each (Reinking et al., Perceus, PLDI 2021). A derivative shares the subexpressions it
//! copies from its function, so they are counted references.

use std::rc::Rc;

enum Expr {
    Val(i64),
    Var(Rc<str>),
    Add(E, E),
    Mul(E, E),
    Pow(E, E),
    Ln(E),
}

type E = Rc<Expr>;

use Expr::{Add, Ln, Mul, Pow, Val, Var};

fn val(n: i64) -> E {
    Rc::new(Val(n))
}

fn constant(e: &Expr) -> Option<i64> {
    if let Val(n) = e { Some(*n) } else { None }
}

fn pown(a: i64, n: i64) -> i64 {
    (0..n).fold(1, |r, _| r * a)
}

fn add(a: E, b: E) -> E {
    match (&*a, &*b) {
        (Val(n), Val(m)) => val(n + m),
        (Val(0), _) => b,
        (_, Val(0)) => a,
        (_, Val(_)) => add(b.clone(), a),
        (Val(n), Add(c, f)) if constant(c).is_some() => {
            add(val(n + constant(c).unwrap_or(0)), f.clone())
        }
        (_, Add(c, g)) if constant(c).is_some() => add(c.clone(), add(a.clone(), g.clone())),
        (Add(f, g), _) => add(f.clone(), add(g.clone(), b.clone())),
        _ => Rc::new(Add(a.clone(), b.clone())),
    }
}

fn mul(a: E, b: E) -> E {
    match (&*a, &*b) {
        (Val(n), Val(m)) => val(n * m),
        (Val(0), _) | (_, Val(0)) => val(0),
        (Val(1), _) => b,
        (_, Val(1)) => a,
        (_, Val(_)) => mul(b.clone(), a),
        (Val(n), Mul(c, f)) if constant(c).is_some() => {
            mul(val(n * constant(c).unwrap_or(1)), f.clone())
        }
        (_, Mul(c, g)) if constant(c).is_some() => mul(c.clone(), mul(a.clone(), g.clone())),
        (Mul(f, g), _) => mul(f.clone(), mul(g.clone(), b.clone())),
        _ => Rc::new(Mul(a.clone(), b.clone())),
    }
}

fn pow(a: E, b: E) -> E {
    match (&*a, &*b) {
        (Val(m), Val(n)) => val(pown(*m, *n)),
        (_, Val(0)) => val(1),
        (_, Val(1)) => a,
        (Val(0), _) => val(0),
        _ => Rc::new(Pow(a.clone(), b.clone())),
    }
}

fn ln(e: E) -> E {
    match &*e {
        Val(1) => val(0),
        _ => Rc::new(Ln(e)),
    }
}

/// The derivative of `e` by `x`.
fn d(x: &str, e: &E) -> E {
    match &**e {
        Val(_) => val(0),
        Var(y) => val(i64::from(**y == *x)),
        Add(f, g) => add(d(x, f), d(x, g)),
        Mul(f, g) => add(mul(f.clone(), d(x, g)), mul(g.clone(), d(x, f))),
        Pow(f, g) => mul(
            pow(f.clone(), g.clone()),
            add(
                mul(mul(g.clone(), d(x, f)), pow(f.clone(), val(-1))),
                mul(ln(f.clone()), d(x, g)),
            ),
        ),
        Ln(f) => mul(d(x, f), pow(f.clone(), val(-1))),
    }
}

fn count(e: &Expr) -> i64 {
    match e {
        Val(_) | Var(_) => 1,
        Add(f, g) | Mul(f, g) | Pow(f, g) => count(f) + count(g),
        Ln(f) => count(f),
    }
}

pub(crate) fn main() {
    let x: E = Rc::new(Var("x".into()));
    let mut f = pow(x.clone(), x);
    for i in 0..10 {
        f = d("x", &f);
        println!("{} count: {}", i + 1, count(&f));
    }
    println!("done");
}
