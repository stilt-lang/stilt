//! The parser takes any bytes without panicking, and gives a tree whose text is the input.

#![no_main]

use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    let parse = stilt_syntax::parse_bytes(data);
    if let Ok(text) = std::str::from_utf8(data) {
        assert_eq!(
            parse.syntax().to_string(),
            text,
            "the tree holds every byte"
        );
    }
});
