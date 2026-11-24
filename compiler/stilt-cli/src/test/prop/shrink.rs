//! Shrinking a failing case (tests.shrinking and tests.shrink-candidates): each value's candidates,
//! in order, and the search that replaces a value with the first candidate whose run fails in the
//! same way, until no candidate does or after 1,000 runs. The reference interpreter's `Prop_shrink`
//! shrinks alike.

use std::collections::HashSet;

use stilt_types::generable::{Graph, Node};

use super::values::{Val, int_value, int_word, minimal, range};

/// The candidates of a value, read once.
type Candidates<'a> = Box<dyn Iterator<Item = Val> + 'a>;

/// The most runs of the closure that shrinking makes.
pub(super) const LIMIT: u32 = 1000;

/// The candidates of a value of a node's type, each once, none identical to the value (rule
/// 12).
pub(super) fn candidates<'a>(g: &'a Graph, k: usize, v: &Val) -> Candidates<'a> {
    let all: Candidates<'a> = match (&g.nodes[k], v.clone()) {
        (Node::Bool, Val::Word(1)) => Box::new(std::iter::once(Val::Word(0))),
        (Node::Int { bits, signed }, Val::Word(w)) => Box::new(ints(*bits, *signed, w).into_iter()),
        (Node::Float { f32 }, Val::Word(w)) => Box::new(floats(*f32, w).into_iter()),
        (Node::Str, Val::Str(s)) => strings(&s),
        (Node::List(elem), Val::Seq(xs)) => {
            let elem = *elem;
            Box::new(sequence(xs, move |x| candidates(g, elem, x)).map(Val::Seq))
        }
        (Node::Map(_, value), Val::Map(entries)) => {
            // A key has no candidates: only values shrink in place.
            let value = *value;
            let entry = move |(kx, vx): &(Val, Val)| -> Box<dyn Iterator<Item = (Val, Val)> + 'a> {
                let kx = kx.clone();
                Box::new(candidates(g, value, vx).map(move |c| (kx.clone(), c)))
            };
            Box::new(sequence(entries, entry).map(Val::Map))
        }
        (Node::Tuple(slots), Val::Seq(xs)) => {
            let slots = slots.clone();
            Box::new(components(xs, move |j, x| candidates(g, slots[j], x)).map(Val::Seq))
        }
        (Node::Record(_, fields), Val::Seq(xs)) => {
            let slots: Vec<usize> = fields.iter().map(|&(_, s)| s).collect();
            Box::new(components(xs, move |j, x| candidates(g, slots[j], x)).map(Val::Seq))
        }
        (Node::Variants(vs), Val::Variant(n, xs)) => {
            let payload = vs[n].1.clone();
            let own: Vec<Val> = payload
                .iter()
                .zip(&xs)
                .filter(|&(&s, _)| s == k)
                .map(|(_, x)| x.clone())
                .collect();
            let inner = components(xs, move |j, x| candidates(g, payload[j], x));
            let first = std::iter::once(minimal(g, k)).chain(own);
            Box::new(first.chain(inner.map(move |ys| Val::Variant(n, ys))))
        }
        _ => Box::new(std::iter::empty()),
    };
    let mut seen = HashSet::from([v.clone()]);
    Box::new(all.filter(move |c| seen.insert(c.clone())))
}

fn ints(bits: u32, signed: bool, w: u64) -> Vec<Val> {
    let x = int_value(w, signed);
    if x == 0 {
        return Vec::new();
    }
    let (lo, _) = range(bits, signed);
    let mut out = vec![0];
    if x < 0 && x != lo {
        out.push(-x);
    }
    out.push(x / 2);
    out.push(if x > 0 { x - 1 } else { x + 1 });
    out.into_iter()
        .map(|x| Val::Word(int_word(x, signed)))
        .collect()
}

/// The candidates of a float, computed on its value as an `f64`, which every operation here
/// gives exactly for an `f32` too.
fn floats(f32: bool, w: u64) -> Vec<Val> {
    #[expect(clippy::cast_possible_truncation, reason = "an f32's bits")]
    let x = if f32 {
        f64::from(f32::from_bits(w as u32))
    } else {
        f64::from_bits(w)
    };
    let word = |x: f64| {
        #[expect(clippy::cast_possible_truncation, reason = "an f32's value, exact")]
        let bits = if f32 {
            u64::from((x as f32).to_bits())
        } else {
            x.to_bits()
        };
        Val::Word(bits)
    };
    if !x.is_finite() {
        return vec![word(0.0)];
    }
    let mut out = vec![0.0];
    if x < 0.0 {
        out.push(-x);
    }
    out.push(x.trunc());
    if x.fract() == 0.0 {
        out.push((x / 2.0).trunc());
    }
    out.into_iter().map(word).collect()
}

/// The candidates of a sequence as tests.shrink-candidates gives them for a list: shorter
/// sequences, then each element replaced by each of its candidates, which `elem` gives.
fn sequence<'a, T: Clone + 'a>(
    xs: Vec<T>,
    elem: impl Fn(&T) -> Box<dyn Iterator<Item = T> + 'a> + 'a,
) -> Box<dyn Iterator<Item = Vec<T>> + 'a> {
    let n = xs.len();
    let shorter = [Vec::new(), xs[n / 2..].to_vec(), xs[..n / 2].to_vec()];
    let without = {
        let xs = xs.clone();
        (0..n).map(move |i| [&xs[..i], &xs[i + 1..]].concat())
    };
    let replaced = (0..n).flat_map(move |i| {
        let xs = xs.clone();
        elem(&xs[i]).map(move |c| {
            let mut ys = xs.clone();
            ys[i] = c;
            ys
        })
    });
    Box::new(shorter.into_iter().chain(without).chain(replaced))
}

/// The value with component `j` replaced by each of its candidates, for each `j` in order.
fn components<'a>(
    xs: Vec<Val>,
    elem: impl Fn(usize, &Val) -> Candidates<'a> + 'a,
) -> Box<dyn Iterator<Item = Vec<Val>> + 'a> {
    Box::new((0..xs.len()).flat_map(move |j| {
        let xs = xs.clone();
        elem(j, &xs[j]).map(move |c| {
            let mut ys = xs.clone();
            ys[j] = c;
            ys
        })
    }))
}

fn strings<'a>(s: &str) -> Candidates<'a> {
    let cs: Vec<char> = s.chars().collect();
    let replaced: Vec<String> = (0..cs.len())
        .filter(|&i| cs[i] != 'a')
        .map(|i| {
            let mut ys = cs.clone();
            ys[i] = 'a';
            ys.into_iter().collect()
        })
        .collect();
    let shorter = sequence(cs, |_| Box::new(std::iter::empty()));
    Box::new(
        shorter
            .map(|cs| cs.into_iter().collect::<String>())
            .chain(replaced)
            .map(Val::Str),
    )
}

/// How a run of the closure failed (tests.running-cases).
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) enum Failure {
    False,
    /// The raised value, as its `Show` impl shows it.
    Raise(String),
    /// The panic's kind and its detail.
    Panic(String, String),
}

impl Failure {
    /// tests.shrinking: whether a run fails in the same way as this one.
    fn same(&self, other: &Failure) -> bool {
        match (self, other) {
            (Failure::False, Failure::False) | (Failure::Raise(_), Failure::Raise(_)) => true,
            (Failure::Panic(k, _), Failure::Panic(l, _)) => k == l,
            _ => false,
        }
    }
}

/// The counterexample, the failure of its run, and the number of values replaced.
pub(super) struct Shrunk {
    pub(super) values: Vec<Val>,
    pub(super) failure: Failure,
    pub(super) shrinks: u32,
}

/// Shrinks the values of a case of the nodes `params`, whose run failed with `failure` (rule
/// 11): `run` gives a run's failure on some values, or `None` when it passes.
pub(super) fn shrink(
    g: &Graph,
    params: &[usize],
    mut values: Vec<Val>,
    mut failure: Failure,
    run: &mut impl FnMut(&[Val]) -> Option<Failure>,
) -> Shrunk {
    let (mut runs, mut shrinks) = (0, 0);
    'search: loop {
        for (j, &k) in params.iter().enumerate() {
            for c in candidates(g, k, &values[j]) {
                if runs >= LIMIT {
                    break 'search;
                }
                runs += 1;
                let mut ys = values.clone();
                ys[j] = c;
                if let Some(f) = run(&ys).filter(|f| failure.same(f)) {
                    (values, failure) = (ys, f);
                    shrinks += 1;
                    continue 'search;
                }
            }
        }
        break;
    }
    Shrunk {
        values,
        failure,
        shrinks,
    }
}
