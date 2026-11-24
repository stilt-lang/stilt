mod layouts;

use super::{Header, SHARED, drop, dup, is_unique, share, share_elements, share_held, unique};
use crate::list;
use crate::shape::Shape;
use crate::text;

/// Whether the object a heap word points to is marked shared.
fn marked(word: u64) -> bool {
    // SAFETY: each test passes a live object.
    unsafe { (*(word as *mut Header)).flags & SHARED != 0 }
}

/// The count of the object a heap word points to, which no other thread changes meanwhile.
fn count(word: u64) -> u32 {
    // SAFETY: each test passes a live object.
    unsafe { (*(word as *mut Header)).rc }
}

/// A list of strings, which takes their references.
fn strings(words: &[u64]) -> u64 {
    list::from_words(words, Shape::word(true)) as u64
}

#[test]
fn sharing_marks_what_a_value_reaches_and_stops_at_marks() {
    let (a, b) = (
        text::new(b"the first string"),
        text::new(b"the second string"),
    );
    let inner = strings(&[a]);
    let outer = list::from_words(&[inner, b], Shape::word(true)) as u64;
    // SAFETY: `outer` is a live list that this thread alone reaches.
    unsafe {
        share(outer, Shape::word(true));
        assert!([outer, inner, a, b].into_iter().all(marked));
        // A marked object is written only once copied, and the copy isn't marked.
        assert!(!is_unique(outer as *mut Header));
        let mut slot = outer;
        dup(outer);
        let copy = unique(&raw mut slot) as u64;
        assert_ne!(copy, outer);
        assert!(!marked(copy) && marked(inner));
        assert_eq!(count(inner), 2);
        drop(copy);
        drop(outer);
    }
}

#[test]
fn a_marked_object_that_one_reference_reaches_is_written_in_place() {
    let inner = strings(&[text::new(b"held inside")]);
    let outer = list::from_words(&[inner], Shape::word(true)) as u64;
    // SAFETY: `outer` is a live list that this thread alone reaches, through `slot`.
    unsafe {
        share(outer, Shape::word(true));
        assert!(marked(outer) && marked(inner));
        let mut slot = outer;
        let taken = unique(&raw mut slot) as u64;
        // No copy, and the mark is gone from the object written, not from what it holds.
        assert_eq!(taken, outer);
        assert!(!marked(outer) && marked(inner));
        assert!(is_unique(outer as *mut Header));
        // Sharing it again marks it again.
        share(outer, Shape::word(true));
        assert!(marked(outer));
        drop(outer);
    }
}

#[test]
fn sharing_an_immortal_object_leaves_it_unmarked() {
    let mut memory = [0u64; 8];
    let s = text::new(b"held by a loan");
    let lent = crate::object::lent_data(&mut memory, &[s, 7], |i| i == 0) as u64;
    // SAFETY: the lent box lives in `memory` and lends `s`, which this thread alone reaches.
    unsafe {
        share(lent, Shape::word(true));
        assert!(!marked(lent) && marked(s));
        drop(s);
    }
}

#[test]
fn the_elements_of_a_list_are_marked_only_where_two_references_meet() {
    let (a, own) = (
        text::new(b"a shared string"),
        text::new(b"an element's own"),
    );
    // SAFETY: the words are live strings; `a` gets a second reference for its second element.
    unsafe { dup(a) };
    let xs = strings(&[a, a, own]);
    let nested = strings(&[own]);
    // SAFETY: `own` gets a reference for `nested`, which a list of lists then holds alone.
    unsafe { dup(own) };
    let rows = list::from_words(&[nested], Shape::word(true)) as u64;
    // SAFETY: both lists are live, and this thread alone reaches them.
    unsafe {
        share_elements(xs as *mut Header);
        assert!(marked(a), "`[a, a]` reaches `a` twice");
        assert!(
            !marked(xs),
            "the list itself isn't counted by the call's threads"
        );
        assert!(marked(own), "`own` is reached from `xs` and from `nested`");
        share_elements(rows as *mut Header);
        assert!(
            !marked(nested),
            "a row that only `rows` holds stays unmarked"
        );
        drop(xs);
        drop(rows);
    }
}

#[test]
fn a_write_in_place_is_marked_when_its_hold_ends() {
    let handle = crate::list::box_of(&[text::new(b"before the write")], Shape::word(true));
    // SAFETY: the box is live, and this thread alone writes it, as a `when` does.
    unsafe {
        share(handle, Shape::word(true));
        let field = crate::object::data_field(handle as *mut Header, 0);
        let after = text::new(b"after the write");
        drop(*field);
        *field = after;
        assert!(!marked(after));
        share_held(handle as *mut Header);
        assert!(marked(after));
        drop(handle);
    }
}

#[test]
fn threads_count_a_shared_object_atomically() {
    let s = text::new(b"counted by four threads");
    // SAFETY: `s` is live and marked before any other thread reaches it.
    unsafe { share(s, Shape::word(true)) };
    let threads: Vec<_> = (0..4)
        .map(|_| {
            std::thread::spawn(move || {
                for _ in 0..100_000 {
                    // SAFETY: the main thread holds a reference until every thread has ended.
                    unsafe {
                        dup(s);
                        drop(s);
                    }
                }
            })
        })
        .collect();
    for thread in threads {
        thread.join().expect("the thread ends");
    }
    assert_eq!(count(s), 1);
    // SAFETY: the last reference.
    unsafe { drop(s) };
}
