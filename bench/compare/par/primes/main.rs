//! primes in parallel: counts the primes below a bound by trial division, in chunks that Rayon
//! counts and adds up.

use rayon::prelude::*;

fn is_prime(n: i64) -> bool {
    if n < 2 {
        return false;
    }
    let mut d = 2;
    while d * d <= n {
        if n % d == 0 {
            return false;
        }
        d += 1;
    }
    true
}

/// The primes from `lo` to below `hi`.
fn count(lo: i64, hi: i64) -> i64 {
    (lo..hi).filter(|&n| is_prime(n)).count() as i64
}

fn main() {
    let bound: i64 = std::env::args()
        .nth(1)
        .and_then(|a| a.parse().ok())
        .unwrap_or(8_000_000);
    let chunk = 10_000;
    let starts: Vec<i64> = (0..bound).step_by(chunk as usize).collect();
    let primes: i64 = starts
        .par_iter()
        .map(|&s| count(s, (s + chunk).min(bound)))
        .sum();
    println!("{primes} primes below {bound}");
}
