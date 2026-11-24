//! fasta: writes random DNA sequences, from cumulative probabilities and a linear congruential
//! generator, and a repeated one, as the Benchmarks Game's program does, in lines of 60.

fn random(seed: &mut i64) -> f64 {
    *seed = (*seed * 3877 + 29573) % 139968;
    *seed as f64 / 139968.0
}

fn repeat(alu: &str, n: usize) {
    let len = alu.len();
    let mut start = 0;
    let mut left = n;
    while left > 0 {
        let width = if left < 60 { left } else { 60 };
        let mut line = Vec::new();
        for i in 0..width {
            line.push(&alu[(start + i) % len..(start + i) % len + 1]);
        }
        println!("{}", line.join(""));
        start = (start + width) % len;
        left -= width;
    }
}

fn randomly(symbols: &[&str], chances: &[f64], n: usize, seed: &mut i64) {
    let mut cumulative = Vec::new();
    let mut sum = 0.0;
    for c in chances {
        sum += c;
        cumulative.push(sum);
    }
    let mut left = n;
    while left > 0 {
        let width = if left < 60 { left } else { 60 };
        let mut line = Vec::new();
        for _ in 0..width {
            let r = random(seed);
            let mut k = 0;
            while k < cumulative.len() - 1 && r >= cumulative[k] {
                k += 1;
            }
            line.push(symbols[k]);
        }
        println!("{}", line.join(""));
        left -= width;
    }
}

fn main() {
    let n = std::env::args().nth(1).and_then(|a| a.parse().ok()).unwrap_or(100000);
    let alu = "GGCCGGGCGCGGTGGCTCACGCCTGTAATCCCAGCACTTTGGGAGGCCGAGGCGGGCGGATCACCTGAGGTCAGGAGTTCGAGACCAGCCTGGCCAACATGGTGAAACCCCGTCTCTACTAAAAATACAAAAATTAGCCGGGCGTGGTGGCGCGCGCCTGTAATCCCAGCTACTCGGGAGGCTGAGGCAGGAGAATCGCTTGAACCCGGGAGGCGGAGGTTGCAGTGAGCCGAGATCGCGCCACTGCACTCCAGCCTGGGCGACAGAGCGAGACTCCGTCTCAAAAA";
    let mut seed = 42;
    println!(">ONE Homo sapiens alu");
    repeat(alu, n * 2);
    println!(">TWO IUB ambiguity codes");
    let iub = ["a", "c", "g", "t", "B", "D", "H", "K", "M", "N", "R", "S", "V", "W", "Y"];
    let iub_chances = [0.27, 0.12, 0.12, 0.27, 0.02, 0.02, 0.02, 0.02, 0.02, 0.02, 0.02, 0.02, 0.02, 0.02, 0.02];
    randomly(&iub, &iub_chances, n * 3, &mut seed);
    println!(">THREE Homo sapiens frequency");
    let sapiens = ["a", "c", "g", "t"];
    let sapiens_chances = [0.3029549426680, 0.1979883004921, 0.1975473066391, 0.3015094502008];
    randomly(&sapiens, &sapiens_chances, n * 5, &mut seed);
}
