//! nsieve: counts the primes below three bounds with the sieve of Eratosthenes, as the
//! Benchmarks Game's former program does.

fn primes(m: usize) -> i64 {
    let mut flags = Vec::new();
    for _ in 0..m + 1 {
        flags.push(true);
    }
    let mut count = 0;
    for i in 2..m + 1 {
        if flags[i] {
            count += 1;
            let mut k = i + i;
            while k <= m {
                flags[k] = false;
                k += i;
            }
        }
    }
    count
}

fn main() {
    let size = std::env::args().nth(1).and_then(|a| a.parse().ok()).unwrap_or(22);
    for shift in 0..3 {
        let m = (1 << (size - shift)) * 10000 / 4096;
        println!("Primes up to {m:>8} {:>8}", primes(m));
    }
}
