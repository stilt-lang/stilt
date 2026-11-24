//! The parts of a module and the edits that replace them.
//!
//! - [`parts`] finds the declarations and bodies of a file, each with its path (edits.parts and edits.paths) and
//!   the span of its source text.
//! - [`canonical`] and [`hash`] give a part's canonical text and its four-digit hash (edits.canonical-text and edits.hash).
//! - [`Address`] reads and writes the addresses of edits.paths, edits.body-addresses and edits.hash.
//! - [`check_text`] decides whether a new text is the part it replaces (edits.new-text), and
//!   [`splice`] writes new texts into a file as `stilt fmt` writes them in their places
//!   (edits.writing).
//! - [`fix_edits`] turns the edits of a fix, spans of a file, into edits of parts (edits.fixes-as-edits).
//! - [`docs`] gives the hashes of each declaration's signature and doc, which `docs.lock` pins
//!   ([`read_lock`], [`write_lock`]; docs.pins, docs.lock-file and docs.stale).
//!
//! Its place among the crates (`compiler/README.md`): it depends on `stilt-syntax` and `stilt-
//! fmt` alone, and on no phase after parsing.
#![warn(missing_docs)]

mod address;
mod canon;
mod fixes;
mod parts;
mod pins;
mod splice;
mod text;

pub use address::{Address, Malformed};
pub use canon::{canonical, hash};
pub use fixes::{FixEdit, Replacement, fix_edits};
pub use parts::{Kind, Part, Place, parts, smallest};
pub use pins::{Doc, Pin, docs, is_stale, read_lock, write_lock};
pub use splice::splice;
pub use text::{Syntax, check_text};

#[cfg(test)]
mod tests;
