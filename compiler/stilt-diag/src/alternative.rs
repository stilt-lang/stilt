//! What would be admissible where a diagnostic points, which its JSON lists for tools
//! (goal admissible-alternatives): bindings of the expected type, missing variants, effects the row
//! allows, and members and names close to one that a lookup didn't find.

/// The most alternatives a diagnostic lists.
pub const MAX_ALTERNATIVES: usize = 10;

/// What an alternative is.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind {
    /// A binding in scope of the type the code expects.
    Binding,
    /// A pattern that the arms of a `match` or a `catch` don't cover.
    Variant,
    /// An element of the row that the code may perform.
    Effect,
    /// A method or member of the type, with a name close to the one written.
    Method,
    /// A field of the record, with a name close to the one written.
    Field,
    /// A name that the code may write, close to the one written.
    Name,
}

impl Kind {
    /// The kind as the JSON writes it.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Binding => "binding",
            Self::Variant => "variant",
            Self::Effect => "effect",
            Self::Method => "method",
            Self::Field => "field",
            Self::Name => "name",
        }
    }
}

/// Something that would be admissible where a diagnostic points.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Alternative {
    /// What it is.
    pub kind: Kind,
    /// The alternative as code writes it: `count`, `Square(_)`, `io` or `len`.
    pub text: String,
    /// Its type as code writes it, for a binding.
    pub ty: Option<String>,
}

impl Alternative {
    /// An alternative of the kind `kind` that code writes as `text`, without a type.
    #[must_use]
    pub fn new(kind: Kind, text: impl Into<String>) -> Self {
        Self {
            kind,
            text: text.into(),
            ty: None,
        }
    }

    /// The alternative, of type `ty`.
    #[must_use]
    pub fn of_type(self, ty: impl Into<String>) -> Self {
        Self {
            ty: Some(ty.into()),
            ..self
        }
    }
}
