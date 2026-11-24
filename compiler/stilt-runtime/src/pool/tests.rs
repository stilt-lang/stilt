//! The tests of each thread's pool of small blocks.

use super::{LARGEST, alloc, free, machine_memory, parse_size, realloc, rounded};

#[test]
fn a_heap_size_is_bytes_or_binary_multiples() {
    assert_eq!(parse_size("1000"), Some(1000));
    assert_eq!(parse_size("64K"), Some(64 << 10));
    assert_eq!(parse_size(" 512M "), Some(512 << 20));
    assert_eq!(parse_size("2g"), Some(2 << 30));
    for not_a_size in ["", "M", "0", "-1G", "1.5G", "12T", "lots"] {
        assert_eq!(parse_size(not_a_size), None, "{not_a_size:?}");
    }
    // Miri implements no `sysconf` of the machine's memory.
    if !cfg!(miri) {
        assert!(machine_memory() >= 512 << 20, "a machine has memory");
    }
}

#[test]
#[cfg_attr(stilt_sanitizers, ignore = "the sanitizers' build caches no block")]
fn a_freed_block_serves_the_next_request_of_its_size() {
    let a = alloc(24, 1);
    // SAFETY: `a` came from `alloc` with 24 bytes, and nothing uses it.
    unsafe { free(a, 24, 1) };
    let b = alloc(20, 1);
    assert_eq!(a, b, "a block of 24 bytes serves a request of 20");
    // SAFETY: as above.
    unsafe { free(b, 20, 1) };
}

#[test]
#[cfg_attr(stilt_sanitizers, ignore = "the sanitizers' build caches no block")]
fn sizes_round_up_to_their_lists() {
    assert_eq!(rounded(0), 8);
    assert_eq!(rounded(17), 24);
    assert_eq!(rounded(LARGEST), LARGEST);
    assert_eq!(rounded(LARGEST + 1), LARGEST + 1);
}

#[test]
fn a_block_larger_than_the_cache_keeps_comes_from_the_system() {
    let big = alloc(LARGEST + 1, 0);
    assert!(!big.is_null());
    // SAFETY: `big` came from `alloc` with this size, and nothing uses it.
    unsafe { free(big, LARGEST + 1, 0) };
}

#[test]
fn a_block_grows_past_the_cache_and_shrinks_back_into_it() {
    let block = alloc(16, 0);
    // SAFETY: each call passes the block the previous one gave, with its size.
    unsafe {
        block.write_bytes(7, 16);
        let grown = realloc(block, 16, 1000);
        assert_eq!(grown.read(), 7);
        let shrunk = realloc(grown, 1000, 40);
        free(shrunk, 40, 0);
    }
}

#[test]
#[cfg_attr(stilt_sanitizers, ignore = "the sanitizers' build caches no block")]
fn a_block_that_grows_within_the_cache_moves_to_a_block_of_its_new_size() {
    let a = alloc(32, 0);
    // SAFETY: each call passes the block the previous one gave, with its size.
    unsafe {
        a.write_bytes(9, 32);
        let grown = realloc(a, 32, 64);
        assert_eq!(grown.add(31).read(), 9);
        let again = alloc(32, 0);
        assert_eq!(
            again, a,
            "the block left behind serves the next request of its size"
        );
        free(again, 32, 0);
        free(grown, 64, 0);
    }
}

#[test]
fn a_block_freed_on_another_thread_joins_its_cache() {
    let block = alloc(32, 1) as usize;
    std::thread::spawn(move || {
        // SAFETY: the block came from `alloc` with 32 bytes, and nothing else uses it.
        unsafe { free(block as *mut u8, 32, 1) };
        super::flush();
    })
    .join()
    .expect("the thread ends");
}
