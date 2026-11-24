use super::{BYTES, Builder, INLINE, bytes, concat, is_inline, len, new, onto};
use crate::object::{Header, drop, dup, is_shared, share};
use crate::shape::STR;

/// The bytes of a string, owned.
fn owned(s: u64) -> Vec<u8> {
    // SAFETY: each caller passes a live string.
    unsafe { bytes(&s) }.to_vec()
}

#[test]
fn a_string_of_up_to_seven_bytes_is_held_in_its_word() {
    for text in ["", "a", "é", "seven!!"] {
        let s = new(text.as_bytes());
        assert!(is_inline(s), "{text:?}");
        assert_eq!(owned(s), text.as_bytes());
        // SAFETY: `s` is a live string.
        assert_eq!(unsafe { len(s) }, text.len());
        // SAFETY: a string held in its word has no object to release.
        unsafe { drop(s) };
    }
    let long = new(b"eight!!!");
    assert!(!is_inline(long), "a string of eight bytes is an object");
    assert_eq!(owned(long), b"eight!!!");
    // SAFETY: `long` is a live string the test owns.
    unsafe { drop(long) };
}

#[test]
fn equal_short_strings_have_one_word() {
    let (a, b) = (new(b"key"), concat([b"k".as_slice(), b"ey"].into_iter()));
    assert_eq!(a, b, "the bytes after a short string's are zero");
    assert_ne!(new(b"ke"), a);
}

#[test]
fn a_slice_of_a_slice_and_a_slice_at_the_end_are_their_bytes() {
    let parent = new(b"a long parent string");
    // SAFETY: `parent` is live while its slices are made.
    let tail = new(&unsafe { bytes(&parent) }[14..]);
    let inner = new(&owned(tail)[1..4]);
    let end = new(&owned(parent)[20..]);
    assert_eq!(
        (owned(tail), owned(inner), owned(end)),
        (b"string".to_vec(), b"tri".to_vec(), Vec::new())
    );
    // SAFETY: the test owns each string once.
    unsafe { drop(parent) };
    assert_eq!(owned(inner), b"tri", "a slice outlives its parent");
    for s in [tail, inner, end] {
        // SAFETY: as above.
        unsafe { drop(s) };
    }
}

#[test]
fn a_builder_writes_a_short_string_in_its_word() {
    let mut out = Builder::new(5);
    out.push(b"ab");
    out.push(b"cde");
    out.written_mut().make_ascii_uppercase();
    let s = out.finish();
    assert!(is_inline(s));
    assert_eq!(owned(s), b"ABCDE");
    assert_eq!(s, new(b"ABCDE"));
}

#[test]
fn a_unique_string_is_appended_to_where_it_is_and_a_shared_one_is_copied() {
    // SAFETY: each string is live until its last reference is dropped.
    unsafe {
        let grown = onto(new(b"abcdefgh"), &[b"cd".as_slice()]);
        assert_eq!(bytes(&grown), b"abcdefghcd");
        let again = onto(grown, &[b"e".as_slice(), b"f".as_slice()]);
        assert_eq!(again, grown, "a string with room grows where it is");
        dup(again);
        let copy = onto(again, &[b"!".as_slice()]);
        assert_ne!(copy, again, "a shared string is never written");
        assert_eq!(
            (bytes(&again), bytes(&copy)),
            (&b"abcdefghcdef"[..], &b"abcdefghcdef!"[..])
        );
        drop(again);
        drop(copy);
    }
}

#[test]
fn appending_to_a_short_string_stays_in_the_word_until_it_needs_an_object() {
    // SAFETY: each string is live until it is passed on or dropped.
    unsafe {
        let s = onto(new(b""), &[b"ab".as_slice()]);
        assert!(is_inline(s));
        let s = onto(s, &[b"cdefg".as_slice()]);
        assert!(is_inline(s), "seven bytes fit in the word");
        let s = onto(s, &[b"h".as_slice()]);
        assert!(!is_inline(s), "an eighth byte takes an object");
        assert!((*(s as *mut Header)).extent >= 8, "with room to grow");
        let t = onto(s, &[b"ij".as_slice()]);
        assert_eq!((t, bytes(&t)), (s, &b"abcdefghij"[..]));
        drop(t);
    }
}

#[test]
fn appending_onto_a_shared_short_string_leaves_it_as_it_was() {
    let s = new(b"abc");
    // SAFETY: a string held in its word is a value: each copy of the word is a string.
    unsafe {
        dup(s);
        let longer = onto(s, &[b"defghij".as_slice()]);
        assert_eq!(
            (owned(s), owned(longer)),
            (b"abc".to_vec(), b"abcdefghij".to_vec())
        );
        drop(longer);
    }
}

#[test]
fn a_short_string_is_no_object_to_count_or_share() {
    let s = new(b"short");
    // SAFETY: counting and sharing leave an immediate as it is.
    unsafe {
        dup(s);
        share(s, STR);
        drop(s);
        drop(s);
    }
    assert_eq!(owned(s), b"short", "an immediate has nothing to free");
    let long = new(b"a string of an object");
    // SAFETY: the test owns `long`.
    unsafe {
        share(long, STR);
        assert!(is_shared(long as *mut Header));
        drop(long);
    }
}

#[test]
fn strings_cross_threads_in_either_form() {
    let (short, long) = (new(b"short"), new(b"a longer string"));
    // SAFETY: the long string is marked shared before another thread can reach it, and each
    // thread owns one reference to it.
    unsafe {
        share(long, STR);
        dup(long);
    }
    let seen = std::thread::spawn(move || {
        let both = concat([owned(short).as_slice(), b" ", &owned(long)].into_iter());
        // SAFETY: the thread owns one of the two references to `long`.
        unsafe { drop(long) };
        owned(both)
    });
    assert_eq!(
        seen.join().expect("the thread ends"),
        b"short a longer string"
    );
    // SAFETY: as above.
    unsafe { drop(long) };
}

#[test]
fn an_object_holds_its_bytes_after_its_length() {
    let s = new(b"0123456789");
    // SAFETY: `s` is a live string object.
    unsafe {
        assert_eq!((s as *const u8).add(BYTES).read(), b'0');
        drop(s);
    }
    const { assert!(INLINE < 8, "a word holds its first byte and the string's") };
}

/// The words of an immortal string object, as the compiler emits a literal of `text`, of at most
/// eight bytes.
fn literal(text: &[u8]) -> [u64; 4] {
    let mut bytes = [0; 8];
    bytes[..text.len()].copy_from_slice(text);
    let kind = u64::from(crate::object::STR) << (8 * crate::layout::KIND);
    [kind, 0, text.len() as u64, u64::from_le_bytes(bytes)]
}

#[test]
fn a_literal_and_a_short_string_of_its_bytes_are_equal() {
    use crate::structural::{stilt_rt_hash_str, stilt_rt_same, stilt_rt_str_eq};
    let object = literal(b"fib");
    let (lit, short, other) = (object.as_ptr() as u64, new(b"fib"), new(b"fig"));
    assert!(!is_inline(lit) && is_inline(short));
    // SAFETY: the literal lives in `object`, which outlives the calls, and the others are words.
    unsafe {
        assert_eq!(stilt_rt_str_eq(lit, short), 1);
        assert_eq!(stilt_rt_hash_str(lit), stilt_rt_hash_str(short));
        assert_eq!(
            (stilt_rt_same(lit, short, 1), stilt_rt_same(short, lit, 1)),
            (1, 1)
        );
        assert_eq!(
            (stilt_rt_same(lit, other, 1), stilt_rt_same(short, other, 1)),
            (0, 0)
        );
    }
}

#[test]
fn strings_of_every_short_length_keep_their_bytes() {
    let source: Vec<u8> = (b'a'..=b'z').chain(b'A'..=b'Z').collect();
    for n in 0..=40 {
        let s = new(&source[..n]);
        let halves = concat([&source[..n / 2], &source[n / 2..n]].into_iter());
        assert_eq!(
            (owned(s), owned(halves)),
            (source[..n].to_vec(), source[..n].to_vec())
        );
        // SAFETY: the test owns both strings.
        unsafe {
            drop(s);
            drop(halves);
        }
    }
}
