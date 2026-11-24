//! A run's values, written to the tape that the property's entry reads them from
//! (`stilt_mir::synth::props`), in the order the entry reads them; and the maps of a case as
//! the run built them, from the positions the tape notes.

use stilt_runtime::Tape;
use stilt_types::generable::{Graph, Node};

use super::values::Val;

/// The tape of values of the nodes `params`.
pub(super) fn write(g: &Graph, params: &[usize], values: &[Val]) -> Tape {
    let (mut words, mut strings) = (Vec::new(), Vec::new());
    for (&k, v) in params.iter().zip(values) {
        put(g, k, v, &mut words, &mut strings);
    }
    Tape::new(words, strings)
}

fn put(g: &Graph, k: usize, v: &Val, words: &mut Vec<u64>, strings: &mut Vec<String>) {
    match (&g.nodes[k], v) {
        (_, Val::Word(w)) => words.push(*w),
        (_, Val::Str(s)) => strings.push(s.clone()),
        (Node::Tuple(slots), Val::Seq(xs)) => {
            for (&s, x) in slots.iter().zip(xs) {
                put(g, s, x, words, strings);
            }
        }
        (Node::Record(_, fields), Val::Seq(xs)) => {
            for (&(_, s), x) in fields.iter().zip(xs) {
                put(g, s, x, words, strings);
            }
        }
        (Node::List(elem), Val::Seq(xs)) => {
            words.push(xs.len() as u64);
            for x in xs {
                put(g, *elem, x, words, strings);
            }
        }
        (Node::Map(key, value), Val::Map(entries)) => {
            words.push(entries.len() as u64);
            for (kx, vx) in entries {
                put(g, *key, kx, words, strings);
                put(g, *value, vx, words, strings);
            }
        }
        (Node::Variants(vs), Val::Variant(n, xs)) => {
            words.push(*n as u64);
            for (&s, x) in vs[*n].1.iter().zip(xs) {
                put(g, s, x, words, strings);
            }
        }
        _ => {}
    }
}

/// The values as the run built them: each map with its entries inserted in order, so that a key
/// equal to an earlier one replaced that entry's value and kept its place (tests.composite-values;
/// std.maps), as the positions that the tape noted for each entry's key, in the order the
/// entries were stored, tell.
pub(super) fn settle(g: &Graph, params: &[usize], values: &[Val], notes: &[u64]) -> Vec<Val> {
    let mut notes = notes.iter().copied();
    params
        .iter()
        .zip(values)
        .map(|(&k, v)| settled(g, k, v, &mut notes))
        .collect()
}

fn settled(g: &Graph, k: usize, v: &Val, notes: &mut impl Iterator<Item = u64>) -> Val {
    match (&g.nodes[k], v) {
        (Node::Tuple(slots), Val::Seq(xs)) => Val::Seq(
            slots
                .iter()
                .zip(xs)
                .map(|(&s, x)| settled(g, s, x, notes))
                .collect(),
        ),
        (Node::Record(_, fields), Val::Seq(xs)) => Val::Seq(
            fields
                .iter()
                .zip(xs)
                .map(|(&(_, s), x)| settled(g, s, x, notes))
                .collect(),
        ),
        (Node::List(elem), Val::Seq(xs)) => {
            Val::Seq(xs.iter().map(|x| settled(g, *elem, x, notes)).collect())
        }
        (Node::Map(key, value), Val::Map(entries)) => {
            let mut built: Vec<(Val, Val)> = Vec::new();
            for (kx, vx) in entries {
                let kx = settled(g, *key, kx, notes);
                let vx = settled(g, *value, vx, notes);
                let at = notes.next().and_then(|p| usize::try_from(p).ok());
                match at.and_then(|p| built.get_mut(p)) {
                    Some(entry) => entry.1 = vx,
                    None => built.push((kx, vx)),
                }
            }
            Val::Map(built)
        }
        (Node::Variants(vs), Val::Variant(n, xs)) => Val::Variant(
            *n,
            vs[*n]
                .1
                .iter()
                .zip(xs)
                .map(|(&s, x)| settled(g, s, x, notes))
                .collect(),
        ),
        _ => v.clone(),
    }
}
