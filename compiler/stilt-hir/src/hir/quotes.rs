//! Quotes (macros.quote, macros.splices and macros.quote-hygiene): code that a procedural macro
//! writes, kept as the tokens it holds, each splice standing for the expression of the macro's code
//! that fills it.

use stilt_syntax::{SyntaxKind, TextRange};

use super::{Expr, Name};

/// The form of code that a quote writes, or that a macro takes or gives
/// (macros.procedural-declarations and macros.quote).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum CodeForm {
    /// `quote { … }`, a `meta.Expr`, whose code is a block of its statements.
    Expr,
    /// `quote type { … }`, a `meta.Type`.
    Type,
    /// `quote pattern { … }`, a `meta.Pattern`.
    Pattern,
    /// `quote field { … }`, a `meta.FieldInit`.
    Field,
}

impl CodeForm {
    /// The name of its type in `std.meta`.
    #[must_use]
    pub fn type_name(self) -> &'static str {
        match self {
            Self::Expr => "Expr",
            Self::Type => "Type",
            Self::Pattern => "Pattern",
            Self::Field => "FieldInit",
        }
    }

    /// The form a use stands for, as a diagnostic names it.
    #[must_use]
    pub fn describe(self) -> &'static str {
        match self {
            Self::Expr | Self::Field => "an expression",
            Self::Type => "a type",
            Self::Pattern => "a pattern",
        }
    }
}

/// Where a splice stands in a quote (macros.splices).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Place {
    /// Where an expression goes.
    Expr,
    /// Where a pattern goes.
    Pattern,
    /// Where a type goes.
    Type,
    /// Where a binding, a variable or a field is named.
    Name,
    /// A spread among the elements of a list, a tuple or a call's arguments.
    Elements,
    /// A spread among a record literal's fields.
    Fields,
}

/// A splice of a quote: where it stands, whether it is a spread, its span, from its `$`, and
/// the expression of the macro's code that fills it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Splice {
    /// Where it stands.
    pub place: Place,
    /// Whether it is a spread, `$..x`.
    pub spread: bool,
    /// Its span, from its `$`.
    pub at: TextRange,
    /// The expression of the macro's code that fills it.
    pub value: Expr,
}

/// A token of a quote: one it writes, by its kind as the parser reads it and its text, a
/// separator's being `;`; a number of this kind and digits written directly after a `-`, which is
/// part of it when its range is checked (numbers.negative-literals); or the splice of this index.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum QuoteTok {
    /// A token it writes: its kind and text.
    Token(SyntaxKind, Name),
    /// A number written directly after a `-`: its kind and digits.
    Negative(SyntaxKind, Name),
    /// The splice of this index.
    Splice(u32),
}

/// A quote, resolved where it is written (macros.quote-hygiene): the module whose items its names
/// resolve among, its form, its tokens and its splices, in the order written.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Quote {
    /// The module whose items its names resolve among.
    pub home: Name,
    /// The form of the code it writes.
    pub form: CodeForm,
    /// Its tokens, in order.
    pub tokens: Vec<QuoteTok>,
    /// Its splices, in the order written.
    pub splices: Vec<Splice>,
    /// Its text, its blanks each one space, as a note shows the quote that wrote an
    /// expansion's code.
    pub written: String,
    /// The functions its contents name, as they resolve where it is written, those of the
    /// quotes inside it included, whose capabilities are its package's
    /// (macros.expansion-effects).
    pub names: Vec<super::Item>,
}

/// What a procedural macro's parameter takes from a use (macros.procedural-declarations).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Input {
    /// `meta.Expr`, `meta.Pattern` or `meta.Type`: a part that parses whole as its form.
    Code(CodeForm),
    /// `meta.Text`: a string literal without interpolation.
    Text,
    /// `meta.File`: a string literal without interpolation that names a file.
    File,
    /// `meta.Tokens`: the tokens of a part and those after it, or of a trailing block.
    Tokens,
}

/// The name of a type of `std.meta` without arguments, if `ty` is one.
fn meta_type(ty: &super::Ty) -> Option<&str> {
    match ty {
        super::Ty::Con(item, args) if &*item.home == "std.meta" && args.is_empty() => {
            Some(&item.name)
        }
        _ => None,
    }
}

impl Input {
    /// What a parameter of type `ty` takes, if `ty` is an input type of `std.meta`.
    #[must_use]
    pub fn of(ty: &super::Ty) -> Option<Self> {
        Some(match meta_type(ty)? {
            "Expr" => Self::Code(CodeForm::Expr),
            "Pattern" => Self::Code(CodeForm::Pattern),
            "Type" => Self::Code(CodeForm::Type),
            "Text" => Self::Text,
            "File" => Self::File,
            "Tokens" => Self::Tokens,
            _ => return None,
        })
    }
}

/// The form of code that a macro whose result is `ty` gives, if it is `meta.Expr`,
/// `meta.Pattern` or `meta.Type`.
#[must_use]
pub fn result_form(ty: &super::Ty) -> Option<CodeForm> {
    match Input::of(ty)? {
        Input::Code(form) => Some(form),
        _ => None,
    }
}

/// Whether `ty` is `meta.Error`.
#[must_use]
pub fn is_meta_error(ty: &super::Ty) -> bool {
    meta_type(ty) == Some("Error")
}
