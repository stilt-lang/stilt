//! Versions, `MAJOR.MINOR.PATCH`, and the tags `vMAJOR.MINOR.PATCH` that make them
//! (packages.versions).

use std::fmt;

/// A version, ordered by its major number, then its minor, then its patch.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Version {
    /// The major number.
    pub major: u64,
    /// The minor number.
    pub minor: u64,
    /// The patch number.
    pub patch: u64,
}

impl Version {
    /// The version that `text` writes, three decimal numbers without leading zeros.
    #[must_use]
    pub fn parse(text: &str) -> Option<Self> {
        if !crate::manifest::is_version(text) {
            return None;
        }
        let mut parts = text.split('.').map(|p| p.parse().ok());
        Some(Self {
            major: parts.next()??,
            minor: parts.next()??,
            patch: parts.next()??,
        })
    }

    /// The version that a tag names: `vMAJOR.MINOR.PATCH`, and no other tag.
    #[must_use]
    pub fn of_tag(tag: &str) -> Option<Self> {
        Self::parse(tag.strip_prefix('v')?)
    }

    /// The version after this one that a change needs (versions.change-needed).
    #[must_use]
    pub fn next(self, change: Change) -> Self {
        match change {
            Change::Major => Self {
                major: self.major + 1,
                minor: 0,
                patch: 0,
            },
            Change::Minor => Self {
                minor: self.minor + 1,
                patch: 0,
                ..self
            },
            Change::Patch => Self {
                patch: self.patch + 1,
                ..self
            },
        }
    }

    /// The change that going from `self` to `later` makes in the numbers.
    #[must_use]
    pub fn change_to(self, later: Self) -> Change {
        if later.major != self.major {
            Change::Major
        } else if later.minor != self.minor {
            Change::Minor
        } else {
            Change::Patch
        }
    }
}

impl fmt::Display for Version {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}.{}.{}", self.major, self.minor, self.patch)
    }
}

/// How much a change in an API asks a version to change, least first (versions.change-needed).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Change {
    /// A change of the patch number.
    Patch,
    /// A change of the minor number.
    Minor,
    /// A change of the major number.
    Major,
}

#[cfg(test)]
mod tests {
    use super::{Change, Version};

    #[test]
    fn reads_and_orders_versions() {
        let v = |s| Version::parse(s).unwrap();
        assert!(v("1.10.0") > v("1.9.9") && v("2.0.0") > v("1.99.99"));
        assert_eq!(Version::of_tag("v1.4.0"), Some(v("1.4.0")));
        for not in ["1.4", "v1.4.0", "1.04.0", "01.4.0", "1.4.0-rc1"] {
            assert_eq!(Version::parse(not), None, "{not}");
        }
        assert_eq!(Version::of_tag("1.4.0"), None);
        assert_eq!(v("1.4.2").next(Change::Major), v("2.0.0"));
        assert_eq!(v("1.4.2").next(Change::Minor), v("1.5.0"));
        assert_eq!(v("1.4.2").change_to(v("1.4.9")), Change::Patch);
        assert_eq!(v("1.4.2").change_to(v("1.5.0")), Change::Minor);
    }
}
