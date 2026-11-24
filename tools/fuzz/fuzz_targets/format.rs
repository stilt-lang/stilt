//! The formatter takes any bytes without panicking, and formatting what it writes changes
//! nothing.

#![no_main]

use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    if let Ok(once) = stilt_fmt::format(data) {
        let twice = stilt_fmt::format(once.as_bytes()).expect("formatted text formats");
        assert_eq!(once, twice, "formatting is idempotent");
    }
});
