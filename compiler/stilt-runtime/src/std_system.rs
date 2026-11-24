//! The natives of `std.clock` and `std.random` (std.clock and std.random): the system's clocks,
//! waiting, and entropy.

use std::sync::LazyLock;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

use crate::abi::Ret;

/// The instant from which `monotonic_ns` counts: the first time it is asked.
static START: LazyLock<Instant> = LazyLock::new(Instant::now);

/// `clock.unix_ms()`: milliseconds since 1970-01-01T00:00:00Z.
#[unsafe(no_mangle)]
pub(crate) extern "C" fn stilt_std_clock_unix_ms(_loc: u64) -> Ret {
    let since = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default();
    Ret::ok(i64::try_from(since.as_millis()).unwrap_or(i64::MAX) as u64)
}

/// `clock.monotonic_ns()`: nanoseconds since an unspecified start, which never decrease.
#[unsafe(no_mangle)]
pub(crate) extern "C" fn stilt_std_clock_monotonic_ns(_loc: u64) -> Ret {
    let since = START.elapsed();
    Ret::ok(i64::try_from(since.as_nanos()).unwrap_or(i64::MAX) as u64)
}

/// `clock.sleep_ms(ms)`: waits at least `ms` milliseconds.
#[unsafe(no_mangle)]
pub(crate) extern "C" fn stilt_std_clock_sleep_ms(_loc: u64, ms: i64) -> Ret {
    if let Ok(ms) = u64::try_from(ms) {
        std::thread::sleep(Duration::from_millis(ms));
    }
    Ret::unit()
}

/// `random.entropy()`: eight bytes from the system's source of randomness, or from the clock
/// where it has none.
#[unsafe(no_mangle)]
pub(crate) extern "C" fn stilt_std_random_entropy(_loc: u64) -> Ret {
    let mut bytes = [0u8; 8];
    if !random(&mut bytes) {
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap_or_default();
        return Ret::ok(now.as_nanos() as u64);
    }
    Ret::ok(u64::from_le_bytes(bytes))
}

/// Fills `bytes` from the system's source of randomness, and tells whether it could.
#[cfg(not(target_family = "wasm"))]
fn random(bytes: &mut [u8; 8]) -> bool {
    use std::io::Read as _;
    std::fs::File::open("/dev/urandom")
        .and_then(|mut f| f.read_exact(bytes))
        .is_ok()
}

/// Fills `bytes` from WASI's `random_get`, and tells whether it could (wasm.what-std-reads).
#[cfg(target_family = "wasm")]
fn random(bytes: &mut [u8; 8]) -> bool {
    crate::wasm::entropy(bytes)
}

/// The functions of this module that compiled code calls, by name.
pub(crate) fn symbols() -> Vec<(&'static str, *const u8)> {
    crate::exports![
        stilt_std_clock_unix_ms,
        stilt_std_clock_monotonic_ns,
        stilt_std_clock_sleep_ms,
        stilt_std_random_entropy,
    ]
}
