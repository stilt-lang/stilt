//! fannkuch-redux: the most pancake flips over the permutations of 1 to n, and a checksum of
//! them, as the Benchmarks Game's program counts them, on one thread.

fn fannkuch(n: usize) -> (i64, i64) {
    let mut perm1 = Vec::new();
    let mut count = Vec::new();
    for i in 0..n {
        perm1.push(i);
        count.push(0);
    }
    let mut max_flips = 0;
    let mut checksum = 0;
    let mut permutations = 0;
    let mut r = n;
    loop {
        while r != 1 {
            count[r - 1] = r;
            r -= 1;
        }
        let mut perm = perm1.clone();
        let mut flips = 0;
        let mut k = perm[0];
        while k != 0 {
            let mut i = 0;
            let mut j = k;
            while i < j {
                perm.swap(i, j);
                i += 1;
                j -= 1;
            }
            flips += 1;
            k = perm[0];
        }
        if flips > max_flips {
            max_flips = flips;
        }
        if permutations % 2 == 0 {
            checksum += flips;
        } else {
            checksum -= flips;
        }
        loop {
            if r == n {
                return (checksum, max_flips);
            }
            let first = perm1[0];
            for i in 0..r {
                perm1[i] = perm1[i + 1];
            }
            perm1[r] = first;
            count[r] -= 1;
            if count[r] > 0 {
                break;
            }
            r += 1;
        }
        permutations += 1;
    }
}

fn main() {
    let n = std::env::args().nth(1).and_then(|a| a.parse().ok()).unwrap_or(10);
    let (checksum, flips) = fannkuch(n);
    println!("{checksum}\nPfannkuchen({n}) = {flips}");
}
