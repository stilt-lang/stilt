//! The values of `std.meta` that macros read and write (macros.tokens-and-code): tokens, texts,
//! names, code and errors, and the natives that make and read them.

pub(crate) mod natives;
mod parse;
mod quotes;
pub(crate) mod tokens;

use stilt_hir::hir::CodeForm;

use crate::value::Meta;

/// The name of the type of `std.meta` that a native value has.
pub(crate) fn type_name(m: &Meta) -> &'static str {
    match m {
        Meta::Span(_) => "Span",
        Meta::Token(_) => "Token",
        Meta::Text(_) => "Text",
        Meta::Name(_) => "Name",
        Meta::Code(c) => match c.form {
            CodeForm::Expr => "Expr",
            CodeForm::Pattern => "Pattern",
            CodeForm::Type => "Type",
            CodeForm::Field => "FieldInit",
        },
        Meta::Error(_) => "Error",
    }
}

/// Whether two native values are equal: spans by place, names by text and origin.
pub(crate) fn same(a: &Meta, b: &Meta) -> bool {
    match (a, b) {
        (Meta::Span(x), Meta::Span(y)) => x == y,
        (Meta::Name(x), Meta::Name(y)) => x.text == y.text && x.origin == y.origin,
        (Meta::Text(x), Meta::Text(y)) => x.value == y.value,
        _ => false,
    }
}
