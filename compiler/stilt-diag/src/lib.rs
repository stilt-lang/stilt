//! The diagnostics of Stilt's compiler: the registry of their codes, `reference/errors.toml`,
//! generated into [`codes`]; the record that every phase reports; and its two renderings, for people and for tools
//! (Compiler architecture, "Diagnostics as data").
//!
//! A [`Diagnostic`] holds byte ranges in its file. A [`File`] places them: it gives the line and
//! column that conformance.diagnostic-lines compares, and renders the diagnostic.
//!
//! Its place among the crates (`compiler/README.md`): it depends on no other crate of the compiler,
//! so that every phase reports through it.

#![warn(missing_docs)]

mod alternative;
mod closest;
mod diagnostic;
mod explanation;
mod file;
mod fix;
mod json;
mod line_index;
mod registry;
mod render;

pub use crate::alternative::{Alternative, Kind as AlternativeKind, MAX_ALTERNATIVES};
pub use crate::closest::{close, closest};
pub use crate::diagnostic::{Diagnostic, Label, MAX_FIXES};
pub use crate::file::File;
pub use crate::fix::{Edit, Fix, apply};
pub use crate::line_index::{LineIndex, Position};
pub use crate::registry::{Code, Entry, Example};
pub use crate::render::{refusal, wrap};

#[rustfmt::skip]
pub mod codes;

#[cfg(test)]
mod tests {
    use crate::{Code, codes};

    #[test]
    fn looks_codes_up() {
        assert_eq!(Code::lookup("E0208"), Some(codes::E0208));
        assert_eq!(Code::lookup("E9999"), None);
        assert!(codes::E0208.is_error());
        assert!(!codes::W0001.is_error());
    }

    #[test]
    fn every_entry_is_complete() {
        for code in codes::ALL {
            let e = code.entry();
            assert!(
                !e.title.is_empty() && !e.help.is_empty() && !e.span.is_empty(),
                "{code}"
            );
            assert!(e.reference.split('.').count() >= 2, "{code}");
        }
    }
}
