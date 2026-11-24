//! The native methods of the integer types that std.integers adds: checked and saturating
//! arithmetic, powers, Euclidean division, bit counts, `gcd` and `lcm`.
//!
//! A value of an integer type comes in a word that holds it sign-extended or zero-extended to 64
//! bits, as its type is signed or not, and goes back in one (`stilt-mir`'s `numeric`).

use crate::abi::{Ret, option};
use crate::panic;

/// The greatest common divisor of two magnitudes.
const fn gcd(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a
}

/// Ends the program with an `overflow` panic for a result that doesn't fit in `ty`.
fn overflow(loc: u64, ty: &str) -> ! {
    panic::panic(
        loc,
        panic::OVERFLOW,
        &format!("the result doesn't fit in `{ty}`"),
    )
}

/// Defines the natives of one integer type `$t`, in a module `$m` of their own, each exported
/// under the name that `stilt-codegen-clif` gives a native of `std.prelude`'s `$t`
/// (`stilt_std_prelude_$t_$method`), with `$extend` giving the word that holds a value and
/// `$magnitude` its magnitude.
macro_rules! integer {
    ($t:ident, $m:ident, $extend:expr, $magnitude:expr) => {
        mod $m {
            use super::{Ret, gcd, option, overflow, panic};

            fn word(x: u64) -> $t {
                x as $t
            }

            fn back(x: $t) -> u64 {
                let f: fn($t) -> u64 = $extend;
                f(x)
            }

            fn magnitude(x: $t) -> u64 {
                let f: fn($t) -> u64 = $magnitude;
                f(x)
            }

            /// A magnitude as a value of the type, or an `overflow` panic.
            fn of_magnitude(loc: u64, m: u64) -> Ret {
                <$t>::try_from(m).map_or_else(|_| overflow(loc, stringify!($t)), |r| Ret::ok(back(r)))
            }

            #[unsafe(export_name = concat!("stilt_std_prelude_", stringify!($t), "_checked_add"))]
            pub(crate) extern "C" fn checked_add(_loc: u64, a: u64, b: u64) -> Ret {
                option(word(a).checked_add(word(b)).map(back))
            }

            #[unsafe(export_name = concat!("stilt_std_prelude_", stringify!($t), "_checked_sub"))]
            pub(crate) extern "C" fn checked_sub(_loc: u64, a: u64, b: u64) -> Ret {
                option(word(a).checked_sub(word(b)).map(back))
            }

            #[unsafe(export_name = concat!("stilt_std_prelude_", stringify!($t), "_checked_mul"))]
            pub(crate) extern "C" fn checked_mul(_loc: u64, a: u64, b: u64) -> Ret {
                option(word(a).checked_mul(word(b)).map(back))
            }

            #[unsafe(export_name = concat!("stilt_std_prelude_", stringify!($t), "_saturating_add"))]
            pub(crate) extern "C" fn saturating_add(_loc: u64, a: u64, b: u64) -> Ret {
                Ret::ok(back(word(a).saturating_add(word(b))))
            }

            #[unsafe(export_name = concat!("stilt_std_prelude_", stringify!($t), "_saturating_sub"))]
            pub(crate) extern "C" fn saturating_sub(_loc: u64, a: u64, b: u64) -> Ret {
                Ret::ok(back(word(a).saturating_sub(word(b))))
            }

            /// `checked_pow` squares its base only up to the highest bit of the exponent, so it
            /// overflows exactly when the power doesn't fit.
            #[unsafe(export_name = concat!("stilt_std_prelude_", stringify!($t), "_pow"))]
            pub(crate) extern "C" fn pow(loc: u64, a: u64, exp: u64) -> Ret {
                word(a)
                    .checked_pow(exp as u32)
                    .map_or_else(|| overflow(loc, stringify!($t)), |r| Ret::ok(back(r)))
            }

            #[unsafe(export_name = concat!("stilt_std_prelude_", stringify!($t), "_div_euclid"))]
            pub(crate) extern "C" fn div_euclid(loc: u64, a: u64, b: u64) -> Ret {
                if word(b) == 0 {
                    panic::panic(loc, panic::DIVIDE_BY_ZERO, "division by zero");
                }
                word(a)
                    .checked_div_euclid(word(b))
                    .map_or_else(|| overflow(loc, stringify!($t)), |r| Ret::ok(back(r)))
            }

            #[unsafe(export_name = concat!("stilt_std_prelude_", stringify!($t), "_rem_euclid"))]
            pub(crate) extern "C" fn rem_euclid(loc: u64, a: u64, b: u64) -> Ret {
                if word(b) == 0 {
                    panic::panic(loc, panic::DIVIDE_BY_ZERO, "division by zero");
                }
                word(a)
                    .checked_rem_euclid(word(b))
                    .map_or_else(|| overflow(loc, stringify!($t)), |r| Ret::ok(back(r)))
            }

            #[unsafe(export_name = concat!("stilt_std_prelude_", stringify!($t), "_count_ones"))]
            pub(crate) extern "C" fn count_ones(_loc: u64, a: u64) -> Ret {
                Ret::ok(u64::from(word(a).count_ones()))
            }

            #[unsafe(export_name = concat!("stilt_std_prelude_", stringify!($t), "_leading_zeros"))]
            pub(crate) extern "C" fn leading_zeros(_loc: u64, a: u64) -> Ret {
                Ret::ok(u64::from(word(a).leading_zeros()))
            }

            #[unsafe(export_name = concat!("stilt_std_prelude_", stringify!($t), "_trailing_zeros"))]
            pub(crate) extern "C" fn trailing_zeros(_loc: u64, a: u64) -> Ret {
                Ret::ok(u64::from(word(a).trailing_zeros()))
            }

            #[unsafe(export_name = concat!("stilt_std_prelude_", stringify!($t), "_gcd"))]
            pub(crate) extern "C" fn gcd_of(loc: u64, a: u64, b: u64) -> Ret {
                of_magnitude(loc, gcd(magnitude(word(a)), magnitude(word(b))))
            }

            #[unsafe(export_name = concat!("stilt_std_prelude_", stringify!($t), "_lcm"))]
            pub(crate) extern "C" fn lcm(loc: u64, a: u64, b: u64) -> Ret {
                let (a, b) = (magnitude(word(a)), magnitude(word(b)));
                if a == 0 || b == 0 {
                    return Ret::ok(0);
                }
                (a / gcd(a, b))
                    .checked_mul(b)
                    .map_or_else(|| overflow(loc, stringify!($t)), |m| of_magnitude(loc, m))
            }

            /// The natives of the type, by the names that compiled code calls them by.
            pub(crate) fn symbols() -> Vec<(&'static str, *const u8)> {
                vec![
                    (concat!("stilt_std_prelude_", stringify!($t), "_checked_add"), checked_add as *const u8),
                    (concat!("stilt_std_prelude_", stringify!($t), "_checked_sub"), checked_sub as *const u8),
                    (concat!("stilt_std_prelude_", stringify!($t), "_checked_mul"), checked_mul as *const u8),
                    (concat!("stilt_std_prelude_", stringify!($t), "_saturating_add"), saturating_add as *const u8),
                    (concat!("stilt_std_prelude_", stringify!($t), "_saturating_sub"), saturating_sub as *const u8),
                    (concat!("stilt_std_prelude_", stringify!($t), "_pow"), pow as *const u8),
                    (concat!("stilt_std_prelude_", stringify!($t), "_div_euclid"), div_euclid as *const u8),
                    (concat!("stilt_std_prelude_", stringify!($t), "_rem_euclid"), rem_euclid as *const u8),
                    (concat!("stilt_std_prelude_", stringify!($t), "_count_ones"), count_ones as *const u8),
                    (concat!("stilt_std_prelude_", stringify!($t), "_leading_zeros"), leading_zeros as *const u8),
                    (concat!("stilt_std_prelude_", stringify!($t), "_trailing_zeros"), trailing_zeros as *const u8),
                    (concat!("stilt_std_prelude_", stringify!($t), "_gcd"), gcd_of as *const u8),
                    (concat!("stilt_std_prelude_", stringify!($t), "_lcm"), lcm as *const u8),
                ]
            }
        }
    };
}

integer!(i8, int_i8, |x| i64::from(x) as u64, |x| u64::from(
    x.unsigned_abs()
));
integer!(i16, int_i16, |x| i64::from(x) as u64, |x| u64::from(
    x.unsigned_abs()
));
integer!(i32, int_i32, |x| i64::from(x) as u64, |x| u64::from(
    x.unsigned_abs()
));
integer!(i64, int_i64, |x| x as u64, i64::unsigned_abs);
integer!(u8, int_u8, u64::from, u64::from);
integer!(u16, int_u16, u64::from, u64::from);
integer!(u32, int_u32, u64::from, u64::from);
integer!(u64, int_u64, |x| x, |x| x);

/// The functions of this module that compiled code calls, by name.
pub(crate) fn symbols() -> Vec<(&'static str, *const u8)> {
    [
        int_i8::symbols(),
        int_i16::symbols(),
        int_i32::symbols(),
        int_i64::symbols(),
        int_u8::symbols(),
        int_u16::symbols(),
        int_u32::symbols(),
        int_u64::symbols(),
    ]
    .concat()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn value(r: Ret) -> i64 {
        r.value as i64
    }

    #[test]
    fn checked_arithmetic_gives_none_past_the_range() {
        assert_eq!(int_i8::checked_add(0, 127, 1), crate::abi::NONE);
        assert_eq!(int_u8::checked_sub(0, 0, 1), crate::abi::NONE);
        assert_eq!(int_i64::checked_mul(0, 3, 4), crate::abi::some(12));
    }

    #[test]
    fn narrow_results_come_back_sign_extended() {
        assert_eq!(value(int_i8::saturating_sub(0, (-128i64) as u64, 1)), -128);
        assert_eq!(
            int_i8::saturating_sub(0, (-128i64) as u64, 1).value,
            (-128i64) as u64
        );
        assert_eq!(int_u8::saturating_add(0, 250, 10).value, 255);
    }

    #[test]
    fn euclidean_division_keeps_the_remainder_non_negative() {
        assert_eq!(value(int_i64::div_euclid(0, (-7i64) as u64, 2)), -4);
        assert_eq!(value(int_i64::rem_euclid(0, (-7i64) as u64, 2)), 1);
        assert_eq!(
            value(int_i64::div_euclid(0, (-7i64) as u64, (-2i64) as u64)),
            4
        );
        assert_eq!(value(int_i64::rem_euclid(0, 7, (-2i64) as u64)), 1);
    }

    #[test]
    fn powers_fit_up_to_the_last_one() {
        assert_eq!(value(int_i64::pow(0, (-2i64) as u64, 63)), i64::MIN);
        assert_eq!(value(int_i8::pow(0, 0, 0)), 1);
        assert_eq!(
            value(int_i8::pow(0, (-1i64) as u64, u64::from(u32::MAX))),
            -1
        );
    }

    #[test]
    fn bits_count_at_the_width() {
        assert_eq!(int_i8::count_ones(0, (-1i64) as u64).value, 8);
        assert_eq!(int_u16::leading_zeros(0, 1).value, 15);
        assert_eq!(int_i32::trailing_zeros(0, 0).value, 32);
    }

    #[test]
    fn gcd_and_lcm_work_on_magnitudes() {
        assert_eq!(value(int_i64::gcd_of(0, 12, (-18i64) as u64)), 6);
        assert_eq!(value(int_i64::gcd_of(0, 0, 0)), 0);
        assert_eq!(value(int_i16::lcm(0, (-4i64) as u64, 6)), 12);
        assert_eq!(value(int_u64::lcm(0, 0, 9)), 0);
    }
}
