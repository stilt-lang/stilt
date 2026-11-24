//! The natives of `std.meta` for procedural macros (macros.tokens-and-code and macros.cursor) in a
//! program's run, outside a macro's (macros.outside-run). There, the functions a macro calls are
//! ordinary ones: `fresh` makes a name, held as its text, which `text()` gives; code, spans and
//! errors are held as texts that nothing shows; and a cursor's parsers, which never find a token,
//! since no token can be made outside a macro's run, raise the error at the end. A token's and a
//! text's methods are never called, since no token and no text can be made there.

use crate::abi::Ret;
use crate::{panic, text};

/// The text of a live string.
///
/// # Safety
///
/// `w` holds a live string.
unsafe fn s(w: &u64) -> &str {
    // SAFETY: the caller guarantees the string is alive.
    unsafe { text::text(w) }
}

/// `meta.fresh(text)`: a new name, held as its text.
///
/// # Safety
///
/// `t` is a live string.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_meta_fresh(_loc: u64, t: u64) -> Ret {
    // SAFETY: the caller guarantees the string is alive.
    Ret::ok(text::from(unsafe { s(&t) }))
}

/// `n.text()`: a name's text.
///
/// # Safety
///
/// `n` is a live name, which is a string.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_meta_Name_text(_loc: u64, n: u64) -> Ret {
    // SAFETY: the caller guarantees the name is alive.
    Ret::ok(text::from(unsafe { s(&n) }))
}

/// Defines natives that give a span, which nothing shows outside a macro's run.
macro_rules! spans {
    ($($name:ident($($arg:ident),*);)*) => {
        $(
            #[doc = concat!("`", stringify!($name), "`: the quote's or the call's place.")]
            #[unsafe(no_mangle)]
            pub(crate) extern "C" fn $name(_loc: u64, $($arg: u64),*) -> Ret {
                $(let _ = $arg;)*
                Ret::ok(text::from(""))
            }
        )*
    };
}

spans! {
    stilt_std_meta_Name_span(n);
    stilt_std_meta_Expr_span(c);
    stilt_std_meta_Pattern_span(c);
    stilt_std_meta_Type_span(c);
    stilt_std_meta_FieldInit_span(c);
    stilt_std_meta_Span_to(a, b);
}

/// `meta.error(span, message)`: an error, held as its message.
///
/// # Safety
///
/// `message` is a live string.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_meta_error(_loc: u64, _span: u64, message: u64) -> Ret {
    // SAFETY: the caller guarantees the string is alive.
    Ret::ok(text::from(unsafe { s(&message) }))
}

/// `e.note(span, message)`: the error, whose notes nothing shows outside a macro's run.
///
/// # Safety
///
/// `e` is a live error, which is a string.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_meta_Error_note(
    _loc: u64,
    e: u64,
    _span: u64,
    _m: u64,
) -> Ret {
    // SAFETY: the caller guarantees the error is alive.
    Ret::ok(text::from(unsafe { s(&e) }))
}

/// Defines the parsers that a cursor calls, which find no token outside a macro's run, and so
/// raise the error at the end of the tokens.
macro_rules! parsers {
    ($($name:ident: $what:literal;)*) => {
        $(
            #[doc = concat!("`", stringify!($name), "`: the error at the end of the tokens.")]
            #[unsafe(no_mangle)]
            pub(crate) extern "C" fn $name(_loc: u64, _tokens: u64, _at: u64) -> Ret {
                Ret::raise(text::from(concat!("expected ", $what, ", found the end")))
            }
        )*
    };
}

parsers! {
    stilt_std_meta_parse_expr: "an expression";
    stilt_std_meta_parse_pattern: "a pattern";
    stilt_std_meta_parse_type: "a type";
}

/// Defines the methods of tokens and texts, which no value outside a macro's run can call.
macro_rules! unmade {
    ($($name:ident($($arg:ident),*);)*) => {
        $(
            #[doc = concat!("`", stringify!($name), "`, which no token or text outside a macro's run calls.")]
            #[unsafe(no_mangle)]
            pub(crate) extern "C" fn $name(loc: u64, $($arg: u64),*) -> Ret {
                $(let _ = $arg;)*
                panic::panic(loc, panic::UNREACHABLE, "a token or a text is made only in a macro's run")
            }
        )*
    };
}

unmade! {
    stilt_std_meta_Token_kind(t);
    stilt_std_meta_Token_span(t);
    stilt_std_meta_Token_name(t);
    stilt_std_meta_Text_value(t);
    stilt_std_meta_Text_span(t, a, b);
    stilt_std_meta_Text_lex(t);
}

/// The functions of this module that compiled code calls, by name.
pub(crate) fn symbols() -> Vec<(&'static str, *const u8)> {
    crate::exports![
        stilt_std_meta_fresh,
        stilt_std_meta_Name_text,
        stilt_std_meta_Name_span,
        stilt_std_meta_Expr_span,
        stilt_std_meta_Pattern_span,
        stilt_std_meta_Type_span,
        stilt_std_meta_FieldInit_span,
        stilt_std_meta_Span_to,
        stilt_std_meta_error,
        stilt_std_meta_Error_note,
        stilt_std_meta_parse_expr,
        stilt_std_meta_parse_pattern,
        stilt_std_meta_parse_type,
        stilt_std_meta_Token_kind,
        stilt_std_meta_Token_span,
        stilt_std_meta_Token_name,
        stilt_std_meta_Text_value,
        stilt_std_meta_Text_span,
        stilt_std_meta_Text_lex,
    ]
}
