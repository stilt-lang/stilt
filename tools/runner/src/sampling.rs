//! The deterministic sample behind `--fast`.
//!
//! Each agent passes its own key, so different agents cover different tests, while one agent
//! always gets the same sample. The hash is FNV-1a, written out here because the standard
//! library's hashers may change between Rust releases.

/// One test in this many is selected, unless `--one-in` says otherwise.
pub(crate) const ONE_IN: u64 = 10;

/// Whether the test called `name` belongs to the sample of one test in `one_in` for `key`.
pub(crate) fn selected(key: &str, name: &str, one_in: u64) -> bool {
    fnv1a(&[key.as_bytes(), &[0], name.as_bytes()]).is_multiple_of(one_in.max(1))
}

fn fnv1a(parts: &[&[u8]]) -> u64 {
    const OFFSET_BASIS: u64 = 0xcbf2_9ce4_8422_2325;
    const PRIME: u64 = 0x0000_0100_0000_01b3;
    parts
        .iter()
        .flat_map(|part| part.iter())
        .fold(OFFSET_BASIS, |hash, &byte| {
            (hash ^ u64::from(byte)).wrapping_mul(PRIME)
        })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn matches_the_published_fnv1a_values() {
        assert_eq!(fnv1a(&[b""]), 0xcbf2_9ce4_8422_2325);
        assert_eq!(fnv1a(&[b"a"]), 0xaf63_dc4c_8601_ec8c);
        assert_eq!(fnv1a(&[b"fo", b"obar"]), 0x8594_4171_f739_67e8);
    }

    #[test]
    fn selects_about_one_test_in_ten() {
        let count = (0..10_000)
            .filter(|i| selected("agent-1", &format!("conformance/t{i}.lt"), ONE_IN))
            .count();
        assert!((900..1100).contains(&count), "selected {count} of 10000");
    }

    #[test]
    fn different_keys_select_different_samples() {
        let sample = |key: &str| -> Vec<bool> {
            (0..200)
                .map(|i| selected(key, &format!("t{i}.lt"), ONE_IN))
                .collect()
        };
        assert_eq!(sample("a"), sample("a"));
        assert_ne!(sample("a"), sample("b"));
    }
}
