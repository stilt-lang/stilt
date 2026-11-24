//! The implicit effects of the native functions, which have no code to walk: those that can
//! panic, overflow, allocate or may not end.

use stilt_hir::decls::Lookup;

use super::Key;
use crate::ty::{is_float, is_numeric, is_prelude, is_view_type};

pub(super) fn is_built_in(key: &Key) -> bool {
    matches!(key, Key::BuiltIn(..))
}

/// program.prelude-functions, std.str and std.lists, std.integers, views.functions-of-views,
/// projections.writable-views, and c.lending-buffer and c.lending-methods: the native functions
/// that can panic, other than by `overflow` (effects.panicking-operations).
pub(super) fn native_panics(key: &Key) -> bool {
    match key {
        Key::Function(item) => {
            is_prelude(item, "panic")
                || is_prelude(item, "unreachable")
                // effects.panic-kinds: `unwrap` and `expect` panic with `unwrap` through these.
                || is_prelude(item, "unwrap_failed")
                || is_prelude(item, "expect_failed")
                // generics.array-effects: `array.fill` panics with `bounds` for a negative size.
                || (&*item.home == "std.array" && &*item.name == "fill")
                || (&*item.home == "std.view" && matches!(&*item.name, "into" | "part" | "split"))
        }
        Key::Member(owner, name) => {
            (is_prelude(owner, "str") && matches!(&**name, "slice" | "with_c_str"))
                || (is_view_type(owner, "View") && matches!(&**name, "of" | "view"))
                || (is_prelude(owner, "List") && matches!(&**name, "insert" | "remove" | "slice"))
                || (is_numeric(owner)
                    && !is_float(owner)
                    && matches!(&**name, "div_euclid" | "rem_euclid"))
        }
        Key::ImplMethod(..) | Key::DefaultMethod(..) | Key::BuiltIn(..) => false,
    }
}

/// facts.native-allocation: every native function allocates, but for those the Reference lists:
/// the native methods of the number types, the queries and parsers of `str`, the queries of
/// `List` and `Map`, the natives of `std.array`, the views of `std.view`, which are held inline,
/// `std.math`, the pointers of `std.c`, the clock's and the entropy's reads, and the natives whose
/// result is `Never`, which end the program.
pub(super) fn native_allocates(decls: &dyn Lookup, key: &Key) -> bool {
    !match key {
        Key::Member(owner, name) => member_allocation_free(owner, name),
        Key::Function(item) => {
            function_allocation_free(&item.home, &item.name)
                || decls.function(item).is_some_and(|s| ends(&s.ret))
        }
        Key::ImplMethod(..) | Key::DefaultMethod(..) | Key::BuiltIn(..) => true,
    }
}

/// Whether a result type is `Never`, which a native that ends the program has.
fn ends(t: &stilt_hir::hir::Ty) -> bool {
    matches!(t, stilt_hir::hir::Ty::Con(item, _) if is_prelude(item, "Never"))
}

/// facts.native-allocation: the native methods that allocate nothing.
fn member_allocation_free(owner: &stilt_hir::hir::Item, name: &str) -> bool {
    if is_numeric(owner) || matches!(&*owner.home, "std.array" | "std.meta") {
        return true;
    }
    if is_prelude(owner, "str") {
        return matches!(
            name,
            "len"
                | "is_empty"
                | "contains"
                | "starts_with"
                | "ends_with"
                | "find"
                | "rfind"
                | "count"
                | "char_count"
        ) || name.starts_with("is_ascii")
            || STR_PARSERS.contains(&name);
    }
    if is_prelude(owner, "List") {
        return matches!(name, "len" | "is_empty" | "get" | "with_ptr");
    }
    if is_prelude(owner, "Map") {
        return matches!(name, "len" | "is_empty" | "contains" | "get");
    }
    if is_view_type(owner, "View") {
        return matches!(name, "of" | "all" | "len" | "is_empty" | "view");
    }
    if &*owner.home == "std.c" {
        return match &*owner.name {
            "Ptr" => matches!(name, "is_null" | "offset" | "address" | "read" | "write"),
            "Str" => name == "is_null",
            _ => false,
        };
    }
    false
}

/// The parsers of `str`, one for each number type (std.str).
const STR_PARSERS: [&str; 10] = [
    "to_i8", "to_i16", "to_i32", "to_i64", "to_u8", "to_u16", "to_u32", "to_u64", "to_f32",
    "to_f64",
];

/// facts.native-allocation: the native functions, not methods, that allocate nothing.
fn function_allocation_free(home: &str, name: &str) -> bool {
    match home {
        "std.math" | "std.array" | "std.meta" => true,
        "std.view" => matches!(name, "get" | "part"),
        "std.c" => name == "null",
        "std.clock" => matches!(name, "unix_ms" | "monotonic_ns" | "sleep_ms"),
        "std.random" => name == "entropy",
        _ => false,
    }
}

/// polymorphism.lazy-implicit-effects, tasks.implicit-effects-and-capabilities, and
/// tasks.implicit-effects-and-capabilities: the native functions that may not end, `Lazy.get`,
/// `std.task.spawn` and `Scope.spawn`, which run a stored function value.
pub(super) fn native_diverges(key: &Key) -> bool {
    match key {
        Key::Member(owner, name) => {
            (&*owner.home == "std.lazy" && &*owner.name == "Lazy" && &**name == "get")
                || (crate::analyses::demands::is_scope(owner) && &**name == "spawn")
        }
        Key::Function(item) => &*item.home == "std.task" && &*item.name == "spawn",
        _ => false,
    }
}

/// effects.overflow-effect, and std.integers: the native functions that can overflow, an integer
/// type's `abs`, `pow`, `div_euclid`, `rem_euclid`, `gcd` and `lcm`.
pub(super) fn native_overflows(key: &Key) -> bool {
    match key {
        Key::Member(owner, name) => {
            is_numeric(owner)
                && !is_float(owner)
                && matches!(
                    &**name,
                    "abs" | "pow" | "div_euclid" | "rem_euclid" | "gcd" | "lcm"
                )
        }
        _ => false,
    }
}
