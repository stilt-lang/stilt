//! The calls of `std.par` on one thread and on several give what their sequential meaning gives
//! (par.sequential-meaning), and report the first panic in its order (par.panics). The closures are
//! written in Rust, with the code that compiled closures have.

use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Duration;

use super::{stilt_std_par_both, stilt_std_par_each, stilt_std_par_fold, stilt_std_par_map};
use crate::abi::Ret;
use crate::layout::{SHAPE_MASK_SHIFT, SHAPE_SIZE_SHIFT};
use crate::list;
use crate::object::{Header, SHARED, alloc_data, data_field, drop, dup, set_masks};
use crate::shape::Shape;
use crate::text;
use crate::workers::tests::{COUNTS, on_threads};

type Code0 = unsafe extern "C" fn(u64, u64, u64) -> Ret;
type Code1 = unsafe extern "C" fn(u64, u64, u64, u64) -> Ret;
type Code2 = unsafe extern "C" fn(u64, u64, u64, u64, u64) -> Ret;

const WORD: Shape = Shape::word(false);
const STR: Shape = Shape::word(true);
/// A record of a scalar then a string, held inline in two words.
const PAIR: Shape = Shape(1 | 16 << SHAPE_SIZE_SHIFT | 0b10 << SHAPE_MASK_SHIFT);

/// A closure whose code's slot is `slot`, capturing `captures`, each a heap word if marked so,
/// whose references it takes.
fn closure(slot: u64, captures: &[(u64, bool)]) -> u64 {
    let object = alloc_data(1 + captures.len(), 0);
    // SAFETY: the object has a field for the slot and one per capture.
    unsafe {
        *data_field(object, 0) = slot;
        for (i, &(word, _)) in captures.iter().enumerate() {
            *data_field(object, i + 1) = word;
        }
        let mask = captures
            .iter()
            .enumerate()
            .fold(0, |m, (i, &(_, heap))| m | u64::from(heap) << (i + 1));
        set_masks(object, |_| mask);
    }
    object as u64
}

/// Capture `i` of a closure.
fn captured(closure: u64, i: usize) -> u64 {
    // SAFETY: each test's closure has the capture it reads.
    unsafe { *data_field(closure as *mut Header, i + 1) }
}

unsafe extern "C" fn square(_: u64, _: u64, x: u64, _: u64) -> Ret {
    Ret::ok(x.wrapping_mul(x))
}
static SQUARE: Code1 = square;

unsafe extern "C" fn same(_: u64, _: u64, x: u64, _: u64) -> Ret {
    // SAFETY: `x` is a live string, which the result shares.
    unsafe { dup(x) };
    Ret::ok(x)
}
static SAME: Code1 = same;

unsafe extern "C" fn bump(_: u64, _: u64, p: u64, _: u64) -> Ret {
    // SAFETY: `p` points to the first word of an element.
    unsafe { *(p as *mut u64) += 1 };
    Ret::unit()
}
static BUMP: Code1 = bump;

unsafe extern "C" fn paren(_: u64, _: u64, p: u64, q: u64, _: u64) -> Ret {
    // SAFETY: both are live strings.
    let (p, q) = unsafe { (text::text(&p), text::text(&q)) };
    Ret::ok(text::new(format!("({p}{q})").as_bytes()))
}
static PAREN: Code2 = paren;

unsafe extern "C" fn add(_: u64, _: u64, p: u64, q: u64, _: u64) -> Ret {
    Ret::ok((f64::from_bits(p) + f64::from_bits(q)).to_bits())
}
static ADD: Code2 = add;

unsafe extern "C" fn first_capture(_: u64, c: u64, _: u64) -> Ret {
    let x = captured(c, 0);
    // SAFETY: the capture is a live string, which the result shares.
    unsafe { dup(x) };
    Ret::ok(x)
}
static FIRST_CAPTURE: Code0 = first_capture;

/// Sums `par.map` of the captured list by the captured closure, inside a call of `par.map`.
unsafe extern "C" fn nested(loc: u64, c: u64, x: u64, _: u64) -> Ret {
    // SAFETY: the captures are a list of words and a closure of them.
    unsafe {
        let inner = stilt_std_par_map(loc, WORD.0, WORD.0, captured(c, 0), captured(c, 1)).value;
        let sum = list::words(inner as *mut Header).iter().sum::<u64>();
        drop(inner);
        Ret::ok(sum + x)
    }
}
static NESTED: Code1 = nested;

static COMPUTED: AtomicUsize = AtomicUsize::new(0);

unsafe extern "C" fn seven(_: u64, _: u64, _: u64) -> Ret {
    COMPUTED.fetch_add(1, Ordering::SeqCst);
    std::thread::sleep(Duration::from_millis(20));
    Ret::ok(7)
}
static SEVEN: Code0 = seven;

/// `x` plus the captured lazy value.
unsafe extern "C" fn lazily(loc: u64, c: u64, x: u64, _: u64) -> Ret {
    // SAFETY: the capture is a lazy integer.
    let seven = unsafe { crate::std_lazy::stilt_std_lazy_Lazy_get(loc, WORD.0, captured(c, 0), 0) };
    Ret::ok(x + seven.value)
}
static LAZILY: Code1 = lazily;

/// The address of a code's slot, as a closure's field 0 holds it.
fn slot<T>(code: &'static T) -> u64 {
    std::ptr::from_ref(code) as u64
}

fn words(n: u64) -> u64 {
    list::from_words(&(0..n).collect::<Vec<_>>(), WORD) as u64
}

fn marked(word: u64) -> bool {
    // SAFETY: each test passes a live object.
    unsafe { (*(word as *mut Header)).flags & SHARED != 0 }
}

#[test]
fn map_gives_each_element_mapped_in_order() {
    for threads in COUNTS {
        on_threads(threads, || {
            for n in [0, 1, 3, 4, 5, 64, 1000] {
                let (xs, f) = (words(n), closure(slot(&SQUARE), &[]));
                // SAFETY: a list of words and a closure of them.
                let mapped = unsafe { stilt_std_par_map(0, WORD.0, WORD.0, xs, f).value };
                // SAFETY: the list is live, and dropped once read.
                unsafe {
                    let expected: Vec<u64> = (0..n).map(|i| i * i).collect();
                    assert_eq!(
                        list::words(mapped as *mut Header),
                        expected,
                        "{n} on {threads}"
                    );
                    for w in [mapped, xs, f] {
                        drop(w);
                    }
                }
            }
        });
    }
}

#[test]
fn elements_that_share_an_object_count_it_atomically() {
    for threads in COUNTS {
        on_threads(threads, || {
            let (a, own) = (
                text::new(b"a shared string"),
                text::new(b"an element's own"),
            );
            let mut elements = vec![own];
            for _ in 0..100 {
                // SAFETY: `a` is live; each element takes a reference.
                unsafe { dup(a) };
                elements.push(a);
            }
            let xs = list::from_words(&elements, STR) as u64;
            let f = closure(slot(&SAME), &[]);
            // SAFETY: a list of strings and a closure of them.
            let mapped = unsafe { stilt_std_par_map(0, STR.0, STR.0, xs, f).value };
            // SAFETY: the lists are live; `a` lives while they do.
            unsafe {
                assert_eq!(marked(a), threads > 1, "`a` is reached from two elements");
                assert!(!marked(own), "`own` is one element's alone");
                assert_eq!((*(a as *mut Header)).rc, 201, "on {threads}");
                drop(mapped);
                assert_eq!((*(a as *mut Header)).rc, 101);
                drop(xs);
                drop(f);
                drop(a);
            }
        });
    }
}

/// The fold of par.fold-tree of `values`, by `combine`.
fn tree<T: Clone>(values: &[T], combine: &impl Fn(T, T) -> T) -> T {
    if let [only] = values {
        return only.clone();
    }
    let (left, right) = values.split_at(values.len() / 2);
    combine(tree(left, combine), tree(right, combine))
}

#[test]
fn fold_combines_in_the_tree_the_length_fixes() {
    for threads in COUNTS {
        on_threads(threads, || {
            for n in [0, 1, 2, 3, 4, 5, 7, 8, 13, 100] {
                let names: Vec<String> = (0..n).map(|i| format!("{i}.")).collect();
                let words: Vec<u64> = names.iter().map(|s| text::new(s.as_bytes())).collect();
                let xs = list::from_words(&words, STR) as u64;
                let (empty, f) = (text::new(b"e"), closure(slot(&PAREN), &[]));
                // SAFETY: a list of strings, a string, and a closure that combines two.
                let folded = unsafe { stilt_std_par_fold(0, STR.0, xs, empty, f, 0) };
                let expected = if n == 0 {
                    "e".to_owned()
                } else {
                    tree(&names, &|p, q| format!("({p}{q})"))
                };
                // SAFETY: the result is a string it owns.
                unsafe {
                    assert_eq!(text::text(&folded.value), expected, "{n} on {threads}");
                    for w in [folded.value, xs, empty, f] {
                        drop(w);
                    }
                }
            }
        });
    }
}

#[test]
fn a_float_fold_gives_the_same_bits_on_any_number_of_threads() {
    let values: Vec<f64> = (0..1000)
        .map(|i| f64::from(i) * 1e-3 + if i % 7 == 0 { 1e16 } else { -3.25 })
        .collect();
    let expected = tree(&values, &|p, q| p + q).to_bits();
    let bits: Vec<u64> = values.iter().map(|v| v.to_bits()).collect();
    for threads in COUNTS {
        on_threads(threads, || {
            let (xs, f) = (
                list::from_words(&bits, WORD) as u64,
                closure(slot(&ADD), &[]),
            );
            // SAFETY: a list of floats and a closure that adds two.
            let sum = unsafe { stilt_std_par_fold(0, WORD.0, xs, 0, f, 0) };
            assert_eq!(sum.value, expected, "on {threads}");
            // SAFETY: both are live and dropped once.
            unsafe {
                for w in [xs, f] {
                    drop(w);
                }
            }
        });
    }
}

#[test]
fn each_writes_every_element_in_place_whatever_its_layout() {
    for threads in COUNTS {
        on_threads(threads, || {
            let f = closure(slot(&BUMP), &[]);
            let bytes = list::of_bytes(&[1, 2, 255, 7, 9, 0, 3]) as u64;
            let s = text::new(b"kept by every pair");
            let pairs = list::new(50, PAIR);
            for i in 0..50 {
                // SAFETY: the list has room, and each element takes a reference to `s`.
                unsafe {
                    dup(s);
                    list::push_bytes(pairs, [i, s].as_ptr().cast());
                }
            }
            let mut slots = [words(100), bytes, pairs as u64];
            for slot in &mut slots {
                // SAFETY: each slot holds a list, and `f` adds 1 to an element's first word.
                unsafe { stilt_std_par_each(0, 0, crate::abi::address(slot), f) };
            }
            // SAFETY: the lists are live, and dropped once read.
            unsafe {
                let expected: Vec<u64> = (1..=100).collect();
                assert_eq!(list::words(slots[0] as *mut Header), expected);
                assert_eq!(
                    list::as_bytes(slots[1] as *mut Header),
                    [2, 3, 0, 8, 10, 1, 4]
                );
                for i in 0..50 {
                    assert_eq!(
                        list::element_words(slots[2] as *mut Header, i),
                        [i as u64 + 1, s]
                    );
                }
                assert_eq!(marked(s), threads > 1, "every element reaches `s`");
                for w in slots.into_iter().chain([f, s]) {
                    drop(w);
                }
            }
        });
    }
}

#[test]
fn both_gives_the_pair_and_a_nested_call_ends() {
    for threads in COUNTS {
        on_threads(threads, || {
            let (a, b) = (text::new(b"a"), text::new(b"b"));
            let f = closure(slot(&FIRST_CAPTURE), &[(a, true)]);
            let g = closure(slot(&FIRST_CAPTURE), &[(b, true)]);
            let mut out = [0u64; 2];
            // SAFETY: two closures of no parameters that give strings, and room for both.
            unsafe { stilt_std_par_both(0, STR.0, STR.0, f, g, out.as_mut_ptr() as usize as u64) };
            assert_eq!(out, [a, b]);
            let inner = closure(slot(&SQUARE), &[]);
            let outer = closure(slot(&NESTED), &[(words(10), true), (inner, true)]);
            let xs = words(20);
            // SAFETY: a list of words and a closure of them.
            let sums = unsafe { stilt_std_par_map(0, WORD.0, WORD.0, xs, outer).value };
            // SAFETY: every word is live and dropped once.
            unsafe {
                let expected: Vec<u64> = (0..20).map(|x| x + 285).collect();
                assert_eq!(list::words(sums as *mut Header), expected);
                for w in out.into_iter().chain([f, g, outer, xs, sums]) {
                    drop(w);
                }
            }
        });
    }
}

#[test]
fn a_lazy_value_that_threads_share_is_computed_once() {
    on_threads(16, || {
        let seven = closure(slot(&SEVEN), &[]);
        // SAFETY: a closure of no parameters, which the lazy value counts a reference to.
        let lazy = unsafe { crate::std_lazy::stilt_std_lazy_Lazy_new(0, WORD.0, seven) };
        let f = closure(slot(&LAZILY), &[(lazy.value, true)]);
        let xs = words(64);
        // SAFETY: a list of words and a closure of them.
        let mapped = unsafe { stilt_std_par_map(0, WORD.0, WORD.0, xs, f).value };
        // SAFETY: the list is live, and every word is dropped once.
        unsafe {
            let expected: Vec<u64> = (7..71).collect();
            assert_eq!(list::words(mapped as *mut Header), expected);
            assert_eq!(COMPUTED.load(Ordering::SeqCst), 1);
            for w in [mapped, xs, f, seven] {
                drop(w);
            }
        }
    });
}

unsafe extern "C" fn panicking(loc: u64, _: u64, x: u64, _: u64) -> Ret {
    match x {
        10 => {
            std::thread::sleep(Duration::from_millis(30));
            crate::panic::panic(loc, crate::panic::EXPLICIT, "first")
        }
        40 => crate::panic::panic(loc, crate::panic::EXPLICIT, "second"),
        _ => Ret::ok(x),
    }
}
static PANICKING: Code1 = panicking;

/// A test's entry that maps 64 elements on `THREADS` threads, the elements at 10 and 40
/// panicking, the second at once and the first a while later.
extern "C" fn maps_panicking<const THREADS: usize>(_: u64) -> Ret {
    on_threads(THREADS, || {
        let (xs, f) = (words(64), closure(slot(&PANICKING), &[]));
        // SAFETY: a list of words and a closure of them.
        unsafe { stilt_std_par_map(0, WORD.0, WORD.0, xs, f) }
    })
}

unsafe extern "C" fn panics_late(loc: u64, _: u64, _: u64) -> Ret {
    std::thread::sleep(Duration::from_millis(30));
    crate::panic::panic(loc, crate::panic::EXPLICIT, "f")
}
static PANICS_LATE: Code0 = panics_late;

unsafe extern "C" fn panics_now(loc: u64, _: u64, _: u64) -> Ret {
    crate::panic::panic(loc, crate::panic::EXPLICIT, "g")
}
static PANICS_NOW: Code0 = panics_now;

unsafe extern "C" fn one(_: u64, _: u64, _: u64) -> Ret {
    Ret::ok(1)
}
static ONE: Code0 = one;

/// A test's entry that runs `par.both` on two threads, of a first closure that panics late, or
/// gives 1 if `FIRST_FINE`, and a second that panics at once.
extern "C" fn both_panicking<const FIRST_FINE: bool>(_: u64) -> Ret {
    on_threads(2, || {
        let first = if FIRST_FINE {
            slot(&ONE)
        } else {
            slot(&PANICS_LATE)
        };
        let (f, g) = (closure(first, &[]), closure(slot(&PANICS_NOW), &[]));
        let mut out = [0u64; 2];
        // SAFETY: two closures of no parameters that give words, and room for both.
        unsafe { stilt_std_par_both(0, WORD.0, WORD.0, f, g, out.as_mut_ptr() as usize as u64) }
    })
}

#[test]
fn the_first_panic_in_the_order_of_the_sequential_run_is_reported() {
    let maps: [crate::Entry; 4] = [
        maps_panicking::<1>,
        maps_panicking::<2>,
        maps_panicking::<3>,
        maps_panicking::<16>,
    ];
    for entry in maps {
        let tested = crate::watch::test(entry);
        assert_eq!(tested.report.as_deref(), Some("panic: explicit: first\n"));
    }
    for (entry, panic) in [
        (both_panicking::<false> as crate::Entry, "f"),
        (both_panicking::<true>, "g"),
    ] {
        let tested = crate::watch::test(entry);
        let report = format!("panic: explicit: {panic}\n");
        assert_eq!(tested.report, Some(report));
    }
}
