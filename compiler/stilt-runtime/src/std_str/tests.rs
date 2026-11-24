//! The parsing of numbers, and the natives that cut and build text, which write each new
//! string once and give back a string they leave as it was (std.str-building).

use super::*;

#[test]
fn integers_parse_within_their_range() {
    assert_eq!(parse_int("007", 64, true), Some(7));
    assert_eq!(parse_int("-128", 8, true), Some((-128i64).cast_unsigned()));
    assert_eq!(parse_int("128", 8, true), None);
    assert_eq!(parse_int("-0", 8, false), None);
    assert_eq!(parse_int("18446744073709551615", 64, false), Some(u64::MAX));
    assert_eq!(parse_int("18446744073709551616", 64, false), None);
    assert_eq!(parse_int("+1", 64, true), None);
    assert_eq!(parse_int("", 64, true), None);
}

#[test]
fn floats_parse_only_in_their_grammar() {
    assert!(valid_float("-1.5e+3"));
    assert!(valid_float("2E10"));
    assert!(!valid_float("1."));
    assert!(!valid_float(".5"));
    assert!(!valid_float("inf"));
    assert!(!valid_float("1e"));
}

#[test]
fn lines_drop_a_final_newline_and_one_carriage_return() {
    assert_eq!(lines(""), Vec::<&str>::new());
    assert_eq!(lines("a\r\nb\n"), vec!["a", "b"]);
    assert_eq!(lines("a\n\n"), vec!["a", ""]);
    assert_eq!(lines("a\r"), vec!["a"]);
}

/// The text of a string that a test owns, which it releases.
fn owned(word: u64) -> String {
    // SAFETY: each test passes a live string that it owns.
    unsafe {
        let t = text::text(&word).to_owned();
        crate::object::drop(word);
        t
    }
}

/// The texts of a list of strings that a test owns, which it releases.
fn texts(xs: u64) -> Vec<String> {
    // SAFETY: each test passes a live list of strings that it owns.
    unsafe {
        let words = list::words(xs as *mut Header).to_vec();
        let out = words.iter().map(|&w| text::text(&w).to_owned()).collect();
        crate::object::drop(xs);
        out
    }
}

#[test]
fn replacing_writes_each_piece_once_and_keeps_a_string_without_matches() {
    let a = text::from("w1 w2 w12 w1");
    assert_eq!(owned(replace(a, "w1", "one-")), "one- w2 one-2 one-");
    assert_eq!(owned(replace(a, "w12", "")), "w1 w2  w1");
    assert_eq!(owned(replace(a, "", "|")), "|w|1| |w|2| |w|1|2| |w|1|");
    let same = replace(a, "x", "y");
    assert_eq!(same, a, "a string without matches is given back");
    assert_eq!(owned(same), "w1 w2 w12 w1");
    assert_eq!(owned(a), "w1 w2 w12 w1");
}

#[test]
fn splitting_on_one_byte_gives_the_pieces_that_a_longer_separator_does() {
    assert_eq!(texts(split("a b  c", " ")), ["a", "b", "", "c"]);
    assert_eq!(texts(split(" a ", " ")), ["", "a", ""]);
    assert_eq!(texts(split("a, b, c", ", ")), ["a", "b", "c"]);
    assert_eq!(texts(split("é", "")), ["é"]);
    assert_eq!(texts(split("", ",")), [""]);
}

#[test]
fn joining_one_part_gives_it_back_and_more_parts_their_text() {
    let part = text::from("only");
    let one = list::from_words(&[part], shape::STR) as u64;
    let joined = join(", ", one);
    assert_eq!(joined, part, "one part is given back");
    assert_eq!(owned(joined), "only");
    let parts = [text::from("a"), text::from(""), text::from("bc")];
    let many = list::from_words(&parts, shape::STR) as u64;
    assert_eq!(owned(join("-", many)), "a--bc");
    // SAFETY: the lists are live, and the test owns them.
    unsafe {
        crate::object::drop(one);
        crate::object::drop(many);
    }
    let none = list::from_words(&[], shape::STR) as u64;
    assert_eq!(owned(join("-", none)), "");
    // SAFETY: as above.
    unsafe { crate::object::drop(none) };
}

#[test]
fn changing_case_touches_only_ascii_letters() {
    assert_eq!(owned(cased("aZé1", <[u8]>::make_ascii_uppercase)), "AZé1");
    assert_eq!(owned(cased("aZé1", <[u8]>::make_ascii_lowercase)), "azé1");
    assert_eq!(owned(cased("q", <[u8]>::make_ascii_uppercase)), "Q");
    assert_eq!(owned(cased("", <[u8]>::make_ascii_uppercase)), "");
}

#[test]
fn a_character_of_a_text_is_held_in_its_word() {
    for t in ["", "a", "~", "é", "日"] {
        let (first, second) = (text::from(t), text::from(t));
        assert_eq!(first, second, "{t:?} is one word");
        assert!(text::is_inline(first), "{t:?} is no object");
    }
    assert_eq!(texts(chars("aé")), ["a", "é"]);
}
