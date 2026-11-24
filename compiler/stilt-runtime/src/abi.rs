//! The calling convention that compiled functions, closures and natives share.
//!
//! Every function takes words and returns the words of its result, and whether it raised
//! (effects.raise). A value of a record, a tuple or a variant whose type isn't recursive is several
//! words, those of its layout, such as an `Option`'s tag, the immediate of its variant's index,
//! and its payload. A function that raised returns its error's words in place of its result's,
//! so a raise is an ordinary return, with no unwinding (Compiler architecture, "`raise` and
//! `try`"). A compiled function returns its words and the flag in registers when they fit, and
//! otherwise its caller passes it a pointer to memory for the words, as its last argument, and
//! it returns the flag alone. A native takes a value of a type parameter in one word, which for
//! a value of several words is a data object of them, its *box*, lent on its caller's stack,
//! which no count frees, since it borrows it. It returns two words: a native that can raise, its
//! result and the flag, an error of several words written to memory that its caller passes a
//! pointer to, as its last argument, as `std.fs` raises an `IoError`; and every other native,
//! the words of its result, of which it has at most two; a native whose result holds a value of
//! a type parameter of several words, as `List.get` gives an `Option` of one, writes its words
//! to memory that its caller passes a pointer to, as its last argument, and returns the
//! `Option`'s tag. The method of a dictionary takes a value of `Self` or of a type parameter in
//! one word too, lent so, and gives one in the words that hold it where a type parameter stands;
//! a closure that a native calls takes each value in one word, and writes a result of several
//! words to memory that the native passes a pointer to. The code of every other closure takes
//! and gives each value in the words that hold it where a type parameter stands, as generic code
//! compiled for the layouts of its type arguments does. The first argument
//! is always a *location*, which code of the standard library reports its panics at: the call from
//! the program into the library that led to it (program.panic-location). The code of a closure, and
//! the method of a dictionary, take the closure or the dictionary as their next argument. Then come
//! a witness for each type parameter, its shape (`crate::shape`), whose lowest bit tells whether
//! the word that holds its values is a heap word, and a dictionary for each bound, and then the
//! arguments: a `let` argument is lent, or given when the callee consumes it
//! (values.consumed-parameters), and an `inout` argument is a pointer to the slot that holds it.
//! Natives, closures and the methods of dictionaries consume nothing.

use crate::object::{Header, data_field};

/// What a function of one word returns: its result, or with `raised` set, the error it raised.
/// A native that can't raise returns its result's words in it, of which an `Option` has two.
#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Ret {
    /// The result, or the error raised.
    pub value: u64,
    /// Nonzero when the function raised `value`.
    pub raised: u64,
}

impl Ret {
    pub(crate) const fn ok(value: u64) -> Self {
        Self { value, raised: 0 }
    }

    /// The two words of a native's result: an `Option`'s tag and payload.
    pub(crate) const fn words(first: u64, second: u64) -> Self {
        Self {
            value: first,
            raised: second,
        }
    }

    pub(crate) const fn raise(error: u64) -> Self {
        Self {
            value: error,
            raised: 1,
        }
    }

    pub(crate) const fn unit() -> Self {
        Self::ok(0)
    }
}

/// The value of an immediate: a variant without a payload, by its index among its type's
/// variants.
pub(crate) const fn immediate(index: u64) -> u64 {
    index << 1 | 1
}

impl From<u64> for Ret {
    fn from(value: u64) -> Self {
        Self::ok(value)
    }
}

/// `None`, the first variant of `Option` (std.bytes-and-scalars): its tag, and no payload.
pub(crate) const NONE: Ret = Ret::words(immediate(0), 0);

/// `Some(x)`, which owns `x`: its tag, and `x` in the one word that holds a value of a type
/// parameter.
pub(crate) const fn some(x: u64) -> Ret {
    Ret::words(immediate(1), x)
}

/// An `Option`: `Some(x)` or `None`.
pub(crate) fn option(x: Option<u64>) -> Ret {
    x.map_or(NONE, some)
}

/// `Less`, `Equal` and `Greater`, in their declaration order (std.option-result-and-ordering).
pub(crate) const LESS: u64 = immediate(0);
pub(crate) const EQUAL: u64 = immediate(1);
pub(crate) const GREATER: u64 = immediate(2);

/// An `Ordering` for a comparison of Rust values.
pub(crate) const fn ordering(order: std::cmp::Ordering) -> u64 {
    match order {
        std::cmp::Ordering::Less => LESS,
        std::cmp::Ordering::Equal => EQUAL,
        std::cmp::Ordering::Greater => GREATER,
    }
}

// Compiled code takes every argument as a word, an address among them, which WebAssembly's
// indirect calls check against the callee's own types (wasm.target).
type Code1 = unsafe extern "C" fn(u64, u64, u64) -> Ret;
pub(crate) type Closure1 = unsafe extern "C" fn(u64, u64, u64, u64) -> Ret;
type Closure1Out = unsafe extern "C" fn(u64, u64, u64, u64, u64) -> Ret;
type Code2 = unsafe extern "C" fn(u64, u64, u64, u64) -> Ret;
type Closure2 = unsafe extern "C" fn(u64, u64, u64, u64, u64) -> Ret;
type Closure2Out = unsafe extern "C" fn(u64, u64, u64, u64, u64, u64) -> Ret;

/// The address of memory as the word that compiled code takes.
pub(crate) fn address<T>(p: *mut T) -> u64 {
    p as usize as u64
}

/// The code of a closure, or a method of a dictionary. Field `index` of the data object holds
/// the address of the function's slot, which holds the address of its latest code.
///
/// # Safety
///
/// `object` is a live data object whose field `index` holds the address of a slot.
unsafe fn code(object: u64, index: usize) -> *const () {
    // SAFETY: the caller guarantees the field holds a slot's address, and a slot holds the
    // address of compiled code.
    unsafe { *(*data_field(object as *mut Header, index) as *const u64) as *const () }
}

/// The code of a closure of one parameter, which takes the closure, the argument and the
/// address of the memory for its error.
///
/// # Safety
///
/// `closure` is a live closure of one parameter.
pub(crate) unsafe fn code1(closure: u64) -> Closure1 {
    // SAFETY: as the caller guarantees: a closure's field 0 is its code.
    unsafe { std::mem::transmute(code(closure, 0)) }
}

/// Calls a closure of one argument, which it borrows, giving it `err`, the memory for an error
/// of several words that it raises, which the native's caller provided.
///
/// # Safety
///
/// `closure` is a live closure of one parameter, `x` a word of its parameter's type, and `err`
/// points to room for the words of the error the closure may raise, or is null where it raises
/// none of several words.
pub(crate) unsafe fn call1(loc: u64, closure: u64, x: u64, err: *mut u64) -> Ret {
    // SAFETY: a closure's field 0 is its code, which takes the closure, one argument and the
    // memory for its error.
    unsafe { code1(closure)(loc, closure, x, address(err)) }
}

/// Calls a closure of one argument, which it borrows, whose result has several words, which it
/// writes to the memory `out` points to, which holds zeros: the code that compiled code gives a
/// native for a closure that gives such a value (`stilt_mir`'s `FnRef::Lent`).
///
/// # Safety
///
/// As for [`call1`], and `out` points to room for the words of the result.
pub(crate) unsafe fn call1_out(
    loc: u64,
    closure: u64,
    x: u64,
    out: *mut u64,
    err: *mut u64,
) -> Ret {
    // SAFETY: a closure's field 0 is its code, which takes the closure, one argument, `out`
    // and the memory for its error.
    unsafe {
        let f: Closure1Out = std::mem::transmute(code(closure, 0));
        f(loc, closure, x, address(out), address(err))
    }
}

/// Calls a closure of two arguments, which it borrows, as [`call1`] calls one of one.
///
/// # Safety
///
/// `closure` is a live closure of two parameters, `x` and `y` words of their types, and `err`
/// as for [`call1`].
pub(crate) unsafe fn call2(loc: u64, closure: u64, x: u64, y: u64, err: *mut u64) -> Ret {
    // SAFETY: a closure's field 0 is its code, which takes the closure, two arguments and the
    // memory for its error.
    unsafe {
        let f: Closure2 = std::mem::transmute(code(closure, 0));
        f(loc, closure, x, y, address(err))
    }
}

/// Calls a closure of two arguments whose result has several words, as [`call1_out`] calls one
/// of one.
///
/// # Safety
///
/// As for [`call2`], and `out` points to room for the words of the result.
pub(crate) unsafe fn call2_out(
    loc: u64,
    closure: u64,
    (x, y): (u64, u64),
    out: *mut u64,
    err: *mut u64,
) -> Ret {
    // SAFETY: a closure's field 0 is its code, which takes the closure, two arguments, `out`
    // and the memory for its error.
    unsafe {
        let f: Closure2Out = std::mem::transmute(code(closure, 0));
        f(loc, closure, x, y, address(out), address(err))
    }
}

/// Calls method `index` of a dictionary, on one borrowed argument.
///
/// # Safety
///
/// `dict` is a live dictionary whose method `index` takes one argument of `x`'s type.
pub(crate) unsafe fn method1(loc: u64, dict: u64, index: usize, x: u64) -> Ret {
    // SAFETY: a dictionary's first fields are its methods, which take the dictionary.
    unsafe {
        let f: Code1 = std::mem::transmute(code(dict, index));
        f(loc, dict, x)
    }
}

/// Calls method `index` of a dictionary, on two borrowed arguments.
///
/// # Safety
///
/// `dict` is a live dictionary whose method `index` takes two arguments of the types of `x`
/// and `y`.
pub(crate) unsafe fn method2(loc: u64, dict: u64, index: usize, x: u64, y: u64) -> Ret {
    // SAFETY: a dictionary's first fields are its methods, which take the dictionary.
    unsafe {
        let f: Code2 = std::mem::transmute(code(dict, index));
        f(loc, dict, x, y)
    }
}

/// The methods of the prelude's traits, by their place in their trait (traits.prelude-traits).
pub(crate) const EQ: usize = 0;
pub(crate) const COMPARE: usize = 0;
pub(crate) const HASH: usize = 0;
pub(crate) const SHOW_NESTED: usize = 1;
