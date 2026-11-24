//! The natives of `std.c`, and the prelude's `with_ptr`, `with_mut_ptr` and `with_c_str`
//! (c.module-std-c and c.lending-buffer). A `c.Ptr<T>` and a `c.Str` are one word, an address. A
//! `T` is read and written as C holds it, in the size its shape gives (`crate::shape`), a narrow
//! scalar's sign extended as the shape says; a list holds its elements so, one after the other, so
//! it lends C the address of its first element. `with_c_str` lends a NUL-terminated copy, which it
//! frees when the closure returns.

use crate::abi::{Ret, call1, call1_out};
use crate::list;
use crate::object::Header;
use crate::shape::Shape;
use crate::text;

/// The address a list lends C: its first element's, or for an empty list, an address that
/// isn't 0 and that C may not read (c.lending-buffer).
///
/// # Safety
///
/// `xs` is a live list.
unsafe fn list_address(xs: *mut Header) -> u64 {
    // SAFETY: the caller guarantees the list; its first element is at the start of its memory.
    unsafe {
        if list::len(xs) == 0 {
            std::ptr::NonNull::<u64>::dangling().as_ptr() as u64
        } else {
            list::at(xs, 0) as u64
        }
    }
}

/// Calls the closure `f` with the address `p`, its result going where a native's result of a
/// type parameter goes: in the word it returns, or to `out` for one of several words. An error
/// it raises comes back as its own, of several words in `err`.
///
/// # Safety
///
/// `f` is a live closure of one parameter whose result has the shape `r`, and `out` and `err`
/// are as the native's caller passes them.
unsafe fn lend(loc: u64, f: u64, p: u64, r: Shape, (out, err): (u64, u64)) -> Ret {
    let err = err as usize as *mut u64;
    // SAFETY: as the caller guarantees.
    unsafe {
        if r.words() > 1 {
            call1_out(loc, f, p, out as usize as *mut u64, err)
        } else {
            call1(loc, f, p, err)
        }
    }
}

/// `xs.with_ptr(f)`: `f` of the address of the list's first element (c.lending-buffer).
///
/// # Safety
///
/// `xs` is a live list, and the rest as for [`lend`].
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_prelude_List_with_ptr(
    loc: u64,
    _t: u64,
    r: u64,
    xs: u64,
    f: u64,
    out: u64,
    err: u64,
) -> Ret {
    // SAFETY: as the caller guarantees; the list lives until the call returns.
    unsafe {
        let p = list_address(xs as *mut Header);
        lend(loc, f, p, Shape(r), (out, err))
    }
}

/// `xs.with_mut_ptr(f)`: `f` of the address of the first element of the list the slot holds,
/// made unique first, so that what C writes there is the list's (c.lending-buffer).
///
/// # Safety
///
/// `slot` holds a live list, and the rest as for [`lend`].
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_prelude_List_with_mut_ptr(
    loc: u64,
    _t: u64,
    r: u64,
    slot: u64,
    f: u64,
    out: u64,
    err: u64,
) -> Ret {
    // SAFETY: as the caller guarantees; the slot holds the list until the call returns.
    unsafe {
        let xs = crate::object::unique(slot as usize as *mut u64);
        lend(loc, f, list_address(xs), Shape(r), (out, err))
    }
}

/// `s.with_c_str(f)`: `f` of a copy of the string that a NUL ends, which lives until `f`
/// returns. A string that holds a NUL panics with `nul-in-string` (c.lending-buffer).
///
/// # Safety
///
/// `s` is a live string, and the rest as for [`lend`].
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_prelude_str_with_c_str(
    loc: u64,
    r: u64,
    s: u64,
    f: u64,
    out: u64,
    err: u64,
) -> Ret {
    // SAFETY: the caller guarantees the string, and the closure and memory as for `lend`.
    unsafe {
        let bytes = text::bytes(&s);
        if let Some(at) = bytes.iter().position(|&b| b == 0) {
            let detail = format!("the string holds a NUL at byte {at}");
            crate::panic::panic(loc, crate::panic::NUL_IN_STRING, &detail);
        }
        let mut copy = Vec::with_capacity(bytes.len() + 1);
        copy.extend_from_slice(bytes);
        copy.push(0);
        lend(loc, f, copy.as_ptr() as u64, Shape(r), (out, err))
    }
}

/// `c.null()`: the address 0.
#[unsafe(no_mangle)]
pub(crate) extern "C" fn stilt_std_c_null(_loc: u64, _t: u64) -> Ret {
    Ret::ok(0)
}

/// `p.is_null()`.
#[unsafe(no_mangle)]
pub(crate) extern "C" fn stilt_std_c_Ptr_is_null(_loc: u64, _t: u64, p: u64) -> Ret {
    Ret::ok(u64::from(p == 0))
}

/// `p.offset(n)`: the address `n` values of `T` further on, wrapping as a `u64` does.
#[unsafe(no_mangle)]
pub(crate) extern "C" fn stilt_std_c_Ptr_offset(_loc: u64, t: u64, p: u64, n: u64) -> Ret {
    let size = Shape(t).size() as u64;
    Ret::ok(p.wrapping_add(n.wrapping_mul(size)))
}

/// `p.address()`.
#[unsafe(no_mangle)]
pub(crate) extern "C" fn stilt_std_c_Ptr_address(_loc: u64, _t: u64, p: u64) -> Ret {
    Ret::ok(p)
}

/// The value of shape `t` at `at`, in the word that holds it.
///
/// # Safety
///
/// `at` holds a value of that shape.
unsafe fn read_at(at: u64, t: Shape) -> u64 {
    let at = at as usize as *const u8;
    // SAFETY: as the caller guarantees; C's values need not be aligned as Rust's are.
    unsafe {
        match (t.size(), t.signed()) {
            (1, true) => i64::from(at.cast::<i8>().read_unaligned()).cast_unsigned(),
            (1, false) => u64::from(at.read_unaligned()),
            (2, true) => i64::from(at.cast::<i16>().read_unaligned()).cast_unsigned(),
            (2, false) => u64::from(at.cast::<u16>().read_unaligned()),
            (4, true) => i64::from(at.cast::<i32>().read_unaligned()).cast_unsigned(),
            (4, false) => u64::from(at.cast::<u32>().read_unaligned()),
            _ => at.cast::<u64>().read_unaligned(),
        }
    }
}

/// `p.read()`: the value of `T` at the address (c.element-types).
///
/// # Safety
///
/// The address holds a value of `T`.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_c_Ptr_read(_loc: u64, t: u64, p: u64, _out: u64) -> Ret {
    // SAFETY: as the caller guarantees.
    Ret::ok(unsafe { read_at(p, Shape(t)) })
}

/// `p.write(v)`: writes `v` at the address, in the size of `T`.
///
/// # Safety
///
/// The address has room for a value of `T`, which C lets the program write.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_c_Ptr_write(_loc: u64, t: u64, p: u64, v: u64) -> Ret {
    let size = Shape(t).size().min(8);
    // SAFETY: as the caller guarantees; the low `size` bytes of the word are the value as C
    // holds it, on a little-endian target.
    unsafe {
        let bytes = v.to_le_bytes();
        std::ptr::copy_nonoverlapping(bytes.as_ptr(), p as usize as *mut u8, size);
    }
    Ret::unit()
}

/// `p.read_list(n)`: the `n` values of `T` from the address on, or `[]` when `n <= 0`.
///
/// # Safety
///
/// The address holds `n` values of `T`.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_c_Ptr_read_list(
    _loc: u64,
    t: u64,
    p: u64,
    n: u64,
) -> Ret {
    let shape = Shape(t);
    let n = usize::try_from(n.cast_signed()).unwrap_or(0);
    let xs = list::new(n, shape);
    // SAFETY: as the caller guarantees; the new list has room for `n` elements of the shape.
    unsafe {
        std::ptr::copy_nonoverlapping(p as usize as *const u8, list::at(xs, 0), n * shape.size());
        list::set_len(xs, n);
    }
    Ret::ok(xs as u64)
}

/// `s.is_null()`.
#[unsafe(no_mangle)]
pub(crate) extern "C" fn stilt_std_c_Str_is_null(_loc: u64, s: u64) -> Ret {
    Ret::ok(u64::from(s == 0))
}

/// `s.to_str()`: the bytes up to the NUL, each maximal subpart of an invalid UTF-8 sequence
/// replaced by one U+FFFD (c.module-std-c).
///
/// # Safety
///
/// The address holds a string that a NUL ends.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_c_Str_to_str(_loc: u64, s: u64) -> Ret {
    // SAFETY: as the caller guarantees.
    let bytes = unsafe { std::ffi::CStr::from_ptr(s as usize as *const std::ffi::c_char) };
    Ret::ok(text::from(&String::from_utf8_lossy(bytes.to_bytes())))
}

pub(crate) fn symbols() -> Vec<(&'static str, *const u8)> {
    crate::exports![
        stilt_std_prelude_List_with_ptr,
        stilt_std_prelude_List_with_mut_ptr,
        stilt_std_prelude_str_with_c_str,
        stilt_std_c_null,
        stilt_std_c_Ptr_is_null,
        stilt_std_c_Ptr_offset,
        stilt_std_c_Ptr_address,
        stilt_std_c_Ptr_read,
        stilt_std_c_Ptr_write,
        stilt_std_c_Ptr_read_list,
        stilt_std_c_Str_is_null,
        stilt_std_c_Str_to_str,
    ]
}
