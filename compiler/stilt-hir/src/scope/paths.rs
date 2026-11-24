//! Module names from files' paths (program.module-names).

use crate::hir::Name;

pub(super) fn dotted(segments: &[impl AsRef<str>]) -> String {
    segments
        .iter()
        .map(AsRef::as_ref)
        .collect::<Vec<_>>()
        .join(".")
}

/// Every prefix of a dotted name, the name included.
pub(super) fn prefixes(name: &str) -> impl Iterator<Item = Name> + '_ {
    name.match_indices('.')
        .map(|(i, _)| Name::from(&name[..i]))
        .chain(std::iter::once(Name::from(name)))
}

/// program.module-names: each segment of a module's path is a lowercase identifier that names
/// nothing else, and `std` belongs to the standard library.
pub(super) fn valid_module_path(segments: &[String]) -> bool {
    segments.first().is_some_and(|first| first != "std")
        && segments.iter().all(|s| stilt_syntax::is_module_segment(s))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn module_names() {
        let path = |p: &str| p.split('/').map(str::to_owned).collect::<Vec<_>>();
        assert!(valid_module_path(&path("orders/store_2")));
        for invalid in [
            "std/x", "Orders", "a/fn", "a/async", "i64", "2d", "a-b", "_",
        ] {
            assert!(!valid_module_path(&path(invalid)), "{invalid}");
        }
        assert!(valid_module_path(&path("_a")));
    }

    #[test]
    fn every_prefix() {
        let all: Vec<_> = prefixes("a.b.c").collect();
        assert_eq!(
            all,
            [Name::from("a"), Name::from("a.b"), Name::from("a.b.c")]
        );
    }
}
