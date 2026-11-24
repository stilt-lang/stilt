//! The numbers that a property's cases are drawn from (tests.seeds and tests.draws): its seed, the
//! 64-bit FNV-1a hash of its text, and for each case a `SplitMix64` generator started at the seed
//! plus the case's number, every operation modulo 2⁶⁴.

/// The FNV-1a hash of a property's text, in UTF-8.
pub(crate) fn seed(text: &str) -> u64 {
    text.bytes().fold(0xcbf2_9ce4_8422_2325, |h, b| {
        (h ^ u64::from(b)).wrapping_mul(0x0000_0100_0000_01b3)
    })
}

/// A case's generator, whose state each draw advances.
#[derive(Debug)]
pub(super) struct Draws {
    state: u64,
}

impl Draws {
    /// The generator of case `case`.
    pub(super) fn new(seed: u64, case: u64) -> Self {
        Self {
            state: seed.wrapping_add(case),
        }
    }

    /// The next number: `SplitMix64`'s mix of the state after adding `0x9e3779b97f4a7c15`.
    pub(super) fn next(&mut self) -> u64 {
        self.state = self.state.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.state;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    /// `next()` modulo `n`, for `n` at least 1, which draws one number even when `n` is 1.
    pub(super) fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }

    /// [`Self::below`] for a bound that a `usize` holds.
    pub(super) fn below_usize(&mut self, n: usize) -> usize {
        usize::try_from(self.below(n as u64)).unwrap_or(0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// FNV-1a's published values, and `SplitMix64`'s from a state of 0.
    #[test]
    fn seeds_and_draws_are_fnv_1a_and_splitmix64() {
        assert_eq!(seed(""), 0xcbf2_9ce4_8422_2325);
        assert_eq!(seed("a"), 0xaf63_dc4c_8601_ec8c);
        assert_eq!(seed("foobar"), 0x8594_4171_f739_67e8);
        let mut d = Draws::new(0, 0);
        let first: Vec<u64> = (0..4).map(|_| d.next()).collect();
        assert_eq!(
            first,
            [
                0xe220_a839_7b1d_cdaf,
                0x6e78_9e6a_a1b9_65f4,
                0x06c4_5d18_8009_454f,
                0xf88b_b8a8_724c_81ec
            ]
        );
        assert_eq!(Draws::new(u64::MAX - 4, 5).next(), 0xe220_a839_7b1d_cdaf);
        let mut d = Draws::new(0, 0);
        let below: Vec<u64> = (0..12).map(|_| d.below(4)).collect();
        assert_eq!(below, [3, 0, 3, 0, 3, 2, 1, 0, 3, 2, 1, 2]);
    }
}
