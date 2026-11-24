//! Pulling an iterator's elements one at a time (views.laziness): each element passes through
//! the adapters from the source outward, each adapter calling its closure as the element
//! reaches it. A pull of a node reads its own state, then the states of the nodes it reads, in
//! the order of its fields, all of which start at zero; an adapter's closure has an empty row
//! (views.adapters), so a pull never raises, while a closure that panics ends the program there.

use super::values::{boxed, release, tuple};
use super::{A, B, C, D, Kind, field, kind, shape, state_len};
use crate::abi::{call1, call1_out};
use crate::list::box_of;
use crate::object::Header;
use crate::shape::Shape;
use crate::{list, map, panic};

/// The next element of the iterator `node`, owning its references, whose tree keeps its state
/// in `state`, or `None` once it has ended. `loc` is where the consumer pulls from.
///
/// # Safety
///
/// `node` is a live iterator, and `state` its tree's state, as earlier pulls left it.
pub(super) unsafe fn pull(loc: u64, node: u64, state: &mut [u64]) -> Option<u64> {
    // SAFETY: the caller guarantees the node, whose fields are as its kind says.
    unsafe {
        let k = kind(node);
        let (own, inner) = state.split_at_mut(k.own_state());
        match k {
            Kind::List | Kind::Map | Kind::Range | Kind::Chars | Kind::Bytes => {
                source(node, k, &mut own[0])
            }
            Kind::MapWith => {
                let x = pull(loc, field(node, A), inner)?;
                let given = apply(loc, field(node, B), x, shape(node));
                release(x, Shape(field(node, C)));
                Some(given)
            }
            Kind::Filter => loop {
                let x = pull(loc, field(node, A), inner)?;
                if accepts(loc, field(node, B), x) {
                    return Some(x);
                }
                release(x, shape(node));
            },
            Kind::Take | Kind::Skip => counted(loc, node, k, &mut own[0], inner),
            Kind::TakeWhile | Kind::SkipWhile => tested(loc, node, k, &mut own[0], inner),
            Kind::Enumerate => {
                let x = pull(loc, field(node, A), inner)?;
                let start = field(node, C).cast_signed();
                let i = start.checked_add(own[0].cast_signed()).unwrap_or_else(|| {
                    panic::panic(loc, panic::OVERFLOW, "the index of `enumerate` overflows")
                });
                own[0] += 1;
                let parts = [
                    (i.cast_unsigned(), Shape::word(false)),
                    (x, Shape(field(node, D))),
                ];
                Some(tuple(&parts, shape(node)))
            }
            Kind::Zip | Kind::Chain => pair(loc, node, k, own, inner),
        }
    }
}

/// The next element of a source, whose own state is `at`: how far it has gone.
///
/// # Safety
///
/// `node` is a live source of kind `k`.
unsafe fn source(node: u64, k: Kind, at: &mut u64) -> Option<u64> {
    // SAFETY: the caller guarantees the node, whose fields are as its kind says.
    unsafe {
        let (a, start, end) = (field(node, A), field(node, B), field(node, C));
        match k {
            Kind::Range => {
                let next = i128::from(start.cast_signed()) + i128::from(*at);
                (next < i128::from(end.cast_signed())).then(|| {
                    *at += 1;
                    i64::try_from(next).unwrap_or(0).cast_unsigned()
                })
            }
            Kind::Map => {
                let position = map::next(a as *mut Header, usize::try_from(*at).ok()?)?;
                *at = position as u64 + 1;
                Some(entry(a, position, shape(node)))
            }
            Kind::Chars => {
                let here = usize::try_from(start + *at).ok()?;
                let (c, len) = super::char_at(a, here, usize::try_from(end).ok()?)?;
                *at += len as u64;
                Some(c)
            }
            _ => {
                let i = start + *at;
                (i < end).then(|| {
                    *at += 1;
                    let i = usize::try_from(i).unwrap_or(usize::MAX);
                    if k == Kind::Bytes {
                        u64::from(crate::text::bytes(&a)[i])
                    } else {
                        list::get(a as *mut Header, i)
                    }
                })
            }
        }
    }
}

/// The entry of a map at a position, as a pair of its key and value with references of their
/// own, of the shape `pair`.
///
/// # Safety
///
/// `m` is a live map with an entry at `position`.
unsafe fn entry(m: u64, position: usize, pair: Shape) -> u64 {
    // SAFETY: the caller guarantees the entry, whose words get new references.
    unsafe {
        let m = m as *mut Header;
        let (k, v) = map::shapes(m);
        let key = std::slice::from_raw_parts(map::key_at(m, position), k.words());
        let value = std::slice::from_raw_parts(map::value_at(m, position), v.words());
        map::dup_words(key, k);
        map::dup_words(value, v);
        let words: Vec<u64> = key.iter().chain(value).copied().collect();
        box_of(&words, pair)
    }
}

/// `f(x)`, which borrows `x`, as a value of the shape `out` of its own.
///
/// # Safety
///
/// `f` is a live closure that takes `x`'s type, and gives values of the shape `out`.
unsafe fn apply(loc: u64, f: u64, x: u64, out: Shape) -> u64 {
    // SAFETY: as the caller guarantees; a closure of an empty row raises nothing.
    unsafe {
        if !boxed(out) {
            return call1(loc, f, x, std::ptr::null_mut()).value;
        }
        let mut words = vec![0; out.words()];
        call1_out(loc, f, x, words.as_mut_ptr(), std::ptr::null_mut());
        box_of(&words, out)
    }
}

/// Whether the closure `p`, which borrows `x`, accepts it.
///
/// # Safety
///
/// `p` is a live closure from `x`'s type to `bool`.
unsafe fn accepts(loc: u64, p: u64, x: u64) -> bool {
    // SAFETY: as the caller guarantees; a closure of an empty row raises nothing.
    unsafe { call1(loc, p, x, std::ptr::null_mut()).value != 0 }
}

/// The next element of `take(n)`, which asks for none after the `n`th, or of `skip(n)`, which
/// asks for the first `n` and drops them: `seen` counts the elements taken, or is 1 once the
/// skipped ones are dropped.
///
/// # Safety
///
/// `node` is a live adapter of kind `k`, and `inner` its iterator's state.
unsafe fn counted(loc: u64, node: u64, k: Kind, seen: &mut u64, inner: &mut [u64]) -> Option<u64> {
    // SAFETY: the caller guarantees the node, whose fields are as its kind says.
    unsafe {
        let (it, n) = (field(node, A), field(node, C).cast_signed());
        if k == Kind::Take {
            if seen.cast_signed() >= n {
                return None;
            }
            *seen += 1;
            return pull(loc, it, inner);
        }
        if *seen == 0 {
            *seen = 1;
            for _ in 0..n {
                release(pull(loc, it, inner)?, shape(node));
            }
        }
        pull(loc, it, inner)
    }
}

/// The next element of `take_while(p)`, which asks for none after the first that `p` rejects,
/// or of `skip_while(p)`, which drops the elements before it: `done` is 1 once that element has
/// come.
///
/// # Safety
///
/// `node` is a live adapter of kind `k`, and `inner` its iterator's state.
unsafe fn tested(loc: u64, node: u64, k: Kind, done: &mut u64, inner: &mut [u64]) -> Option<u64> {
    // SAFETY: the caller guarantees the node, whose fields are as its kind says.
    unsafe {
        let (it, p) = (field(node, A), field(node, B));
        if *done != 0 {
            return match k {
                Kind::TakeWhile => None,
                _ => pull(loc, it, inner),
            };
        }
        loop {
            let x = pull(loc, it, inner)?;
            let accepted = accepts(loc, p, x);
            if k == Kind::TakeWhile {
                if accepted {
                    return Some(x);
                }
                *done = 1;
                release(x, shape(node));
                return None;
            }
            if !accepted {
                *done = 1;
                return Some(x);
            }
            release(x, shape(node));
        }
    }
}

/// The next element of `zip`, which asks its first iterator and then its second, and ends with
/// the first that ends, or of `chain`, which asks its second once its first has ended, `own`
/// then holding 1.
///
/// # Safety
///
/// `node` is a live adapter of kind `k`, and `inner` its iterators' states, the first's first.
unsafe fn pair(loc: u64, node: u64, k: Kind, own: &mut [u64], inner: &mut [u64]) -> Option<u64> {
    // SAFETY: the caller guarantees the node, whose fields are as its kind says.
    unsafe {
        let (first, second) = (field(node, A), field(node, B));
        let (s1, s2) = inner.split_at_mut(state_len(first));
        if k == Kind::Chain {
            if own[0] == 0 {
                if let Some(x) = pull(loc, first, s1) {
                    return Some(x);
                }
                own[0] = 1;
            }
            return pull(loc, second, s2);
        }
        let x = pull(loc, first, s1)?;
        let (sx, sy) = (Shape(field(node, C)), Shape(field(node, D)));
        let Some(y) = pull(loc, second, s2) else {
            release(x, sx);
            return None;
        };
        Some(tuple(&[(x, sx), (y, sy)], shape(node)))
    }
}
