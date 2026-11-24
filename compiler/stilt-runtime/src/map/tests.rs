//! A map keeps its entries in insertion order through inserts, replacements, removals and
//! inserts again, and finds a key by one call of its type's `hash`, then `eq` on each stored key
//! of the same hash in insertion order until one returns `true` (std.finding-keys), however its
//! table grows and is built again. The dictionaries' methods are written in Rust, with the code
//! that compiled methods have, and note each call.

use std::cell::RefCell;

use super::{Keys, find, key_at, next, remove_at};
use crate::abi::Ret;
use crate::layout::{STR_KEYS, WORD_KEYS};
use crate::maps::store;
use crate::object::{Header, alloc_data, data_field, drop};
use crate::shape::Shape;
use crate::text;

#[derive(Clone, Debug, PartialEq, Eq)]
enum Call {
    Hash(u64),
    Eq(u64, u64),
}

thread_local! {
    static CALLS: RefCell<Vec<Call>> = const { RefCell::new(Vec::new()) };
}

fn calls() -> Vec<Call> {
    CALLS.with(RefCell::take)
}

/// A hash with many collisions: keys that agree modulo 7 share it.
fn colliding(k: u64) -> u64 {
    k % 7
}

unsafe extern "C" fn hash(_: u64, _: u64, k: u64) -> Ret {
    CALLS.with(|c| c.borrow_mut().push(Call::Hash(k)));
    Ret::ok(colliding(k))
}

unsafe extern "C" fn eq(_: u64, _: u64, k: u64, other: u64) -> Ret {
    CALLS.with(|c| c.borrow_mut().push(Call::Eq(k, other)));
    Ret::ok(u64::from(k == other))
}

/// A slot that holds the address of `code`, as compiled code's slots do. The address exposes the
/// function's provenance, so the address read back from the slot may be called.
fn slot(code: *const ()) -> u64 {
    std::ptr::from_ref(Box::leak(Box::new(code.expose_provenance() as u64))) as u64
}

/// A dictionary of one method, whose code's slot is `slot`, with the tag `tag`.
fn dict(slot: u64, tag: u16) -> u64 {
    let d = alloc_data(1, tag);
    // SAFETY: the object has one field.
    unsafe { *data_field(d, 0) = slot };
    d as u64
}

/// Dictionaries whose methods note their calls, tagged as `tag` says.
fn noting(tag: u16) -> Keys {
    Keys {
        loc: 0,
        eq: dict(slot(eq as *const ()), tag),
        hash: dict(slot(hash as *const ()), tag),
    }
}

const WORD: Shape = Shape::word(false);

/// The keys of a map, in its order.
fn keys_of(m: *mut Header) -> Vec<u64> {
    let mut out = Vec::new();
    // SAFETY: the map is alive and its keys are one word each.
    unsafe {
        let mut at = next(m, 0);
        while let Some(p) = at {
            out.push(*key_at(m, p));
            at = next(m, p + 1);
        }
    }
    out
}

/// The calls that finding `k` among `stored`, the keys in insertion order, makes.
fn expected(stored: &[u64], k: u64) -> Vec<Call> {
    let mut out = vec![Call::Hash(k)];
    for &s in stored.iter().filter(|&&s| colliding(s) == colliding(k)) {
        out.push(Call::Eq(k, s));
        if s == k {
            break;
        }
    }
    out
}

/// Inserts, replaces and removes keys drawn from a small range, many times over, so that the
/// table fills, gains removed slots, grows and is built again, and the entries are compacted;
/// after each operation the calls and the order are those that a list of the keys gives.
#[test]
fn finding_a_key_calls_hash_once_then_eq_in_insertion_order() {
    let keys = noting(0);
    let m = super::new(WORD, WORD, None);
    let mut model: Vec<u64> = Vec::new();
    let (mut x, mut removed) = (12345u64, 0);
    for step in 0..4000u64 {
        x = (x * 1_103_515_245 + 12345) % 2_147_483_648;
        let k = x % 300;
        let before = model.clone();
        // SAFETY: the map is alive and unique, and its keys and values are scalars.
        unsafe {
            if (x >> 16) % 3 == 0 {
                let (found, _) = find(m, keys, &[k]);
                assert_eq!(found.is_some(), model.contains(&k));
                if let Some(p) = found {
                    let _ = remove_at(m, p);
                    model.retain(|&s| s != k);
                    removed += 1;
                }
            } else {
                store(m, keys, &[k], &[step]);
                if !model.contains(&k) {
                    model.push(k);
                }
            }
        }
        assert_eq!(calls(), expected(&before, k), "step {step}, key {k}");
        assert_eq!(keys_of(m), model, "step {step}");
    }
    assert!(removed > 500, "the keys come and go, {removed} times");
    // SAFETY: the map is alive, and the test owns it.
    unsafe { drop(m as u64) };
}

/// A key that `insert` finds keeps its place, and one removed and inserted again goes last.
#[test]
fn a_replaced_key_keeps_its_place_and_a_reinserted_one_goes_last() {
    let keys = noting(0);
    let m = super::new(WORD, WORD, None);
    // SAFETY: the map is alive and unique, and its keys and values are scalars.
    unsafe {
        for k in [3, 10, 17, 4] {
            store(m, keys, &[k], &[k]);
        }
        store(m, keys, &[10], &[99]);
        assert_eq!(keys_of(m), [3, 10, 17, 4]);
        let at = find(m, keys, &[10]).0.expect("a stored key");
        assert_eq!(*super::value_at(m, at), 99);
        let _ = remove_at(m, at);
        store(m, keys, &[10], &[1]);
        assert_eq!(keys_of(m), [3, 17, 4, 10]);
        drop(m as u64);
    }
    let _ = calls();
}

/// Keys of an integer type and strings, whose dictionaries' tags say so, are hashed and compared
/// by the map itself, which finds them as their dictionaries would and calls neither.
#[test]
fn keys_of_words_and_strings_are_found_without_calls() {
    let words = noting(WORD_KEYS);
    let m = super::new(WORD, WORD, None);
    // SAFETY: the map is alive and unique, and its keys and values are scalars.
    unsafe {
        for k in 0..1000 {
            store(m, words, &[k * 1024], &[k]);
        }
        assert_eq!(find(m, words, &[512 * 1024]).0, Some(512));
        assert_eq!(find(m, words, &[3]).0, None);
        drop(m as u64);
    }
    let strings = noting(STR_KEYS);
    let m = super::new(Shape::word(true), WORD, None);
    // SAFETY: as above, with keys that are live strings, which the map counts.
    unsafe {
        for k in 0..100 {
            let s = text::from(&format!("key {k}"));
            store(m, strings, &[s], &[k]);
            drop(s);
        }
        let probe = text::from("key 42");
        assert_eq!(find(m, strings, &[probe]).0, Some(42));
        drop(probe);
        let absent = text::from("key 100");
        assert_eq!(find(m, strings, &[absent]).0, None);
        drop(absent);
        drop(m as u64);
    }
    assert_eq!(calls(), []);
}
