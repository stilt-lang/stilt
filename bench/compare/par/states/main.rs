//! states in parallel: advances each of a list of generators 400 steps in place with Rayon,
//! then folds their states into one checksum.

use rayon::prelude::*;

fn main() {
    let count: u64 = std::env::args()
        .nth(1)
        .and_then(|a| a.parse().ok())
        .unwrap_or(2_000_000);
    let mut states: Vec<u64> = (0..count)
        .map(|i| i.wrapping_mul(2_654_435_761).wrapping_add(1))
        .collect();
    states.par_iter_mut().for_each(|s| {
        for _ in 0..400 {
            *s = s
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            *s ^= *s >> 29;
        }
    });
    let checksum = states.par_iter().copied().reduce(|| 0, |a, b| a ^ b);
    println!("checksum {checksum} of {count} states");
}
