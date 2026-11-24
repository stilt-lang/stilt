//! The items that stand for anonymous record types and record bounds (records.anonymous-types and
//! records.record-bounds).
//!
//! An anonymous record type has no declaration, so it is the type constructor of an item of a
//! home that no module can have, named by its fields' names in alphabetical order, by their
//! bytes, and applied to their types in that order: two such types are the same type when they
//! have the same fields with the same types, whatever the order they are written in, and never
//! the same as a declared record. A record bound is a bound on an item of another such home,
//! named by the same rule, whose arguments are the fields' types, as a trait's arguments are
//! (traits.bound-arguments).

use super::{Item, Name};

/// The home of the items of anonymous record types.
pub const RECORD_HOME: &str = "{}";

/// The home of the items of record bounds.
pub const RECORD_BOUND_HOME: &str = "{..}";

impl Item {
    /// The constructor of the anonymous record types with the fields `names`, sorted.
    #[must_use]
    pub fn record(names: &[Name]) -> Self {
        Self {
            home: Name::from(RECORD_HOME),
            name: Name::from(names.join(",")),
        }
    }

    /// The item of the record bounds that name the fields `names`, sorted.
    #[must_use]
    pub fn record_bound(names: &[Name]) -> Self {
        Self {
            home: Name::from(RECORD_BOUND_HOME),
            name: Name::from(names.join(",")),
        }
    }

    /// Whether it is an anonymous record type's constructor.
    #[must_use]
    pub fn is_record(&self) -> bool {
        &*self.home == RECORD_HOME
    }

    /// Whether it is a record bound's item.
    #[must_use]
    pub fn is_record_bound(&self) -> bool {
        &*self.home == RECORD_BOUND_HOME
    }

    /// The names of the fields of an anonymous record type or a record bound, in order.
    #[must_use]
    pub fn record_fields(&self) -> Vec<Name> {
        self.name.split(',').map(Name::from).collect()
    }
}

/// The fields `fields`, in the order of an anonymous record type's: alphabetical, by the
/// bytes of their names (records.field-order).
#[must_use]
pub fn sorted_fields<T>(mut fields: Vec<(Name, T)>) -> Vec<(Name, T)> {
    fields.sort_by(|a, b| a.0.as_bytes().cmp(b.0.as_bytes()));
    fields
}
