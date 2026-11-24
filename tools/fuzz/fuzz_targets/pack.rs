//! The pack reader takes any bytes without panicking: as a pack a server sends, and, split at
//! the length its first two bytes give, as the index and the pack of a repository on the
//! machine.

#![no_main]

use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    let _ = stilt_pkg::git::read_sent(data);
    if let [high, low, rest @ ..] = data {
        let length = usize::from(u16::from_be_bytes([*high, *low])).min(rest.len());
        let (index, pack) = rest.split_at(length);
        let _ = stilt_pkg::git::read_indexed(index.to_vec(), pack.to_vec());
    }
});
