//! C names of a program's code and files, made from the names the MIR gives them, so that a
//! function's name, and with it the C of the files that call it, stays the same while other
//! code changes: an object of a file whose C is unchanged is then reused.
//!
//! A name keeps the letters and digits of the MIR's, and writes `_` as `__` and any other
//! byte as `_` and its two hexadecimal digits, so that two MIR names never give one C name.
//! One longer than C names should be keeps a readable start and the hash of the whole.

use std::fmt::Write as _;

/// The longest name kept whole. Profiles and debuggers show the names, and clang and the
/// linkers take far longer ones, but instances of generic code can be thousands of bytes.
const LONGEST: usize = 160;

/// The C identifier of `text`, after `prefix`.
pub(crate) fn c_name(prefix: &str, text: &str) -> String {
    let mut out = String::with_capacity(prefix.len() + text.len());
    out.push_str(prefix);
    for b in text.bytes() {
        match b {
            b'_' => out.push_str("__"),
            b'a'..=b'z' | b'A'..=b'Z' | b'0'..=b'9' => out.push(char::from(b)),
            _ => {
                let _ = write!(out, "_{b:02x}");
            }
        }
    }
    if out.len() <= LONGEST {
        return out;
    }
    let mut cut = LONGEST - 18;
    while !out.is_char_boundary(cut) {
        cut -= 1;
    }
    out.truncate(cut);
    let _ = write!(out, "_h{:016x}", fnv(text.as_bytes()));
    out
}

/// The name of a C file of a program: a module's, or with `None`, the program's own.
pub(crate) fn file_name(module: Option<&str>) -> String {
    match module {
        Some(m) => format!("{}.c", c_name("m_", m)),
        None => "program.c".to_owned(),
    }
}

/// The text of a C string literal of `bytes`.
pub(crate) fn c_string(bytes: &[u8]) -> String {
    let mut out = String::from("\"");
    for &b in bytes {
        match b {
            b'"' | b'\\' => {
                out.push('\\');
                out.push(char::from(b));
            }
            0x20..=0x7e => out.push(char::from(b)),
            _ => {
                let _ = write!(out, "\\{b:03o}");
            }
        }
    }
    out.push('"');
    out
}

/// FNV-1a of `bytes`, which tells the long names apart.
fn fnv(bytes: &[u8]) -> u64 {
    bytes.iter().fold(0xcbf2_9ce4_8422_2325, |h, &b| {
        (h ^ u64::from(b)).wrapping_mul(0x0100_0000_01b3)
    })
}

#[cfg(test)]
mod tests {
    use super::{c_name, file_name};

    #[test]
    fn names_are_identifiers_that_tell_names_apart() {
        assert_eq!(c_name("f_", "main.step"), "f_main_2estep");
        assert_eq!(c_name("f_", "a_b"), "f_a__b");
        assert_ne!(c_name("f_", "a.b"), c_name("f_", "a_2eb"));
        assert_eq!(file_name(Some("std.prelude")), "m_std_2eprelude.c");
        assert_eq!(file_name(None), "program.c");
    }

    #[test]
    fn long_names_keep_a_start_and_a_hash() {
        let long = "List.map<".repeat(40);
        let name = c_name("f_", &long);
        assert!(name.len() <= 160, "{name}");
        assert!(name.starts_with("f_List_2emap_3c"));
        assert_ne!(name, c_name("f_", &format!("{long}x")));
    }
}
