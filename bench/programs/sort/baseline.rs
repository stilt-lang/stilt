//! sort: sorts a list of integers with the standard library's sort and with a quicksort that
//! works in place.

fn quicksort(xs: &mut [i64], lo: i64, hi: i64) {
    if lo >= hi {
        return;
    }
    let pivot = xs[((lo + hi) / 2) as usize];
    let mut i = lo;
    let mut j = hi;
    while i <= j {
        while xs[i as usize] < pivot {
            i += 1;
        }
        while xs[j as usize] > pivot {
            j -= 1;
        }
        if i <= j {
            xs.swap(i as usize, j as usize);
            i += 1;
            j -= 1;
        }
    }
    quicksort(xs, lo, j);
    quicksort(xs, i, hi);
}

fn checksum(xs: &[i64]) -> i64 {
    let mut sum = 0;
    for x in xs {
        sum = (sum * 31 + x) % 1000000007;
    }
    sum
}

fn main() {
    let size = std::env::args().nth(1).and_then(|a| a.parse().ok()).unwrap_or(400000);
    let mut xs = Vec::new();
    let mut x: i64 = 1;
    for _ in 0..size {
        x = (x * 1103515245 + 12345) % 2147483648;
        xs.push(x % 1000000);
    }
    let mut sorted = xs.clone();
    sorted.sort();
    let mut quick = xs.clone();
    let hi = quick.len() as i64 - 1;
    quicksort(&mut quick, 0, hi);
    let mut by_digit = xs.clone();
    by_digit.sort_by_key(|v| v % 10);
    println!("{} {} {}", checksum(&sorted), checksum(&quick), checksum(&by_digit));
}
