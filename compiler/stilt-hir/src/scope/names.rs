//! What a module's scope says of one name, a query of its own for each module and name, so
//! that another module's resolution depends only on the names it looks up there: an edit that
//! adds a variant or a function to a module leaves as they are the modules that never name it
//! (goal edit-to-diagnostics).

use stilt_db::{Db, Program, SourceFile};

use super::{Entry, Namespace, Value, module_scope};
use crate::hir::Name;
use crate::items::{TraitShape, ValueParams};

/// What a scope says of one name, in each namespace.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Named {
    /// The item of the type namespace.
    pub ty: Option<Entry>,
    /// What the value namespace binds it to.
    pub value: Option<Value>,
    /// Whether a part with a syntax error declares only its name, as a type or a trait
    /// (errors.declarations-with-errors).
    pub unknown_type: bool,
    /// The same, as a function or a constant.
    pub unknown_value: bool,
    /// The shape of the trait it names (traits.trait-parameters).
    pub shape: Option<TraitShape>,
    /// The value parameters of the type it names (generics.value-parameters).
    pub value_params: Option<ValueParams>,
}

impl Named {
    /// The item in one namespace, as [`super::Scope::find`] finds it.
    #[must_use]
    pub fn find(&self, namespace: Namespace) -> Option<Entry> {
        match namespace {
            Namespace::Types => self.ty,
            Namespace::Values => match self.value {
                Some(Value::Item(entry)) => Some(entry),
                Some(Value::Import(_) | Value::ImportError) | None => None,
            },
        }
    }

    /// Whether the name is declared only as a name, as [`super::Scope::unknown`] says.
    #[must_use]
    pub fn unknown(&self, namespace: Namespace) -> bool {
        match namespace {
            Namespace::Types => self.unknown_type || self.unknown_value,
            Namespace::Values => self.unknown_value,
        }
    }
}

/// What the scope of the module of `file` says of `name`.
#[salsa::tracked(returns(ref))]
pub fn named(db: &dyn Db, program: Program, file: SourceFile, name: Name) -> Named {
    let scope = &module_scope(db, program, file).scope;
    Named {
        ty: scope.types.get(&name).copied(),
        value: scope.values.get(&name).cloned(),
        unknown_type: scope.unknown_types.contains(&name),
        unknown_value: scope.unknown_values.contains(&name),
        shape: scope.traits.get(&name).cloned(),
        value_params: scope.value_params.get(&name).cloned(),
    }
}
