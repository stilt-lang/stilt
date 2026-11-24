//! map-heavy: inserts, finds, overwrites and removes integer and string keys in hash maps.

use std::collections::HashMap;

fn next(x: i64) -> i64 {
    (x * 1103515245 + 12345) % 2147483648
}

fn main() {
    let n = std::env::args().nth(1).and_then(|a| a.parse().ok()).unwrap_or(300000);
    let mut numbers = HashMap::new();
    let mut x = 42;
    for i in 0..n {
        x = next(x);
        numbers.insert(x % 100000, i);
    }
    let mut hits = 0;
    for _ in 0..n {
        x = next(x);
        if numbers.contains_key(&(x % 200000)) {
            hits += 1;
        }
    }
    for k in 0..50000 {
        numbers.remove(&(k * 2));
    }
    let mut sum = 0;
    for (k, v) in &numbers {
        sum += k ^ v;
    }
    println!("{} numbers, {hits} hits, checksum {sum}", numbers.len());

    let mut words: HashMap<String, i64> = HashMap::new();
    for _ in 0..n {
        x = next(x);
        *words.entry(format!("w{}", x % 5000)).or_insert(0) += 1;
    }
    let mut longest = 0;
    let mut most = 0;
    for (w, count) in &words {
        if w.len() > longest {
            longest = w.len();
        }
        if *count > most {
            most = *count;
        }
    }
    println!("{} words, longest {longest}, most {most}", words.len());
}
