//! The natives of `std.math` (std.math): the transcendental functions of `f64`, from
//! the platform's library, whose results are within the record's tolerance rather than exact.
//!
//! An `f64` comes in a word that holds its bits, and goes back in one.

use crate::abi::Ret;

/// Defines natives of `std.math` of one or two `f64` arguments, each the Rust function `f`.
macro_rules! natives {
    ($($name:ident($($arg:ident),*) = $f:expr;)*) => {
        $(
            #[doc = concat!("`math.", stringify!($name), "`.")]
            #[unsafe(no_mangle)]
            pub(crate) extern "C" fn $name(_loc: u64, $($arg: u64),*) -> Ret {
                let f: fn($(natives!(@f64 $arg)),*) -> f64 = $f;
                Ret::ok(f($(f64::from_bits($arg)),*).to_bits())
            }
        )*

        /// The functions of this module that compiled code calls, by name.
        pub(crate) fn symbols() -> Vec<(&'static str, *const u8)> {
            crate::exports![$($name),*]
        }
    };
    (@f64 $arg:ident) => { f64 };
}

natives! {
    stilt_std_math_pow(x, y) = f64::powf;
    stilt_std_math_exp(x) = f64::exp;
    stilt_std_math_log(x) = f64::ln;
    stilt_std_math_log2(x) = f64::log2;
    stilt_std_math_log10(x) = f64::log10;
    stilt_std_math_sin(x) = f64::sin;
    stilt_std_math_cos(x) = f64::cos;
    stilt_std_math_tan(x) = f64::tan;
    stilt_std_math_asin(x) = f64::asin;
    stilt_std_math_acos(x) = f64::acos;
    stilt_std_math_atan(x) = f64::atan;
    stilt_std_math_atan2(y, x) = f64::atan2;
    stilt_std_math_sinh(x) = f64::sinh;
    stilt_std_math_cosh(x) = f64::cosh;
    stilt_std_math_tanh(x) = f64::tanh;
    stilt_std_math_cbrt(x) = f64::cbrt;
    stilt_std_math_hypot(x, y) = f64::hypot;
}

#[cfg(test)]
mod tests {
    use super::*;

    fn of(r: Ret) -> f64 {
        f64::from_bits(r.value)
    }

    #[test]
    fn special_values_are_exact() {
        assert_eq!(
            of(stilt_std_math_pow(0, f64::NAN.to_bits(), 0.0f64.to_bits())),
            1.0
        );
        assert_eq!(
            of(stilt_std_math_log(0, 0.0f64.to_bits())),
            f64::NEG_INFINITY
        );
        assert!(of(stilt_std_math_log(0, (-1.0f64).to_bits())).is_nan());
        assert_eq!(
            of(stilt_std_math_hypot(
                0,
                f64::INFINITY.to_bits(),
                f64::NAN.to_bits()
            )),
            f64::INFINITY
        );
        assert_eq!(
            of(stilt_std_math_sin(0, (-0.0f64).to_bits())).to_bits(),
            (-0.0f64).to_bits()
        );
    }
}
