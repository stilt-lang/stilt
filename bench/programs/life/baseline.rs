//! life: runs Conway's Game of Life on a grid that wraps around, held as one list of cells.

fn step(cells: &[bool], n: usize) -> Vec<bool> {
    // The largest side the grid may have, as the Stilt program checks.
    if n < 1 || n > 32768 {
        return cells.to_vec();
    }
    let mut next = Vec::new();
    for y in 0..n {
        for x in 0..n {
            let mut alive = 0;
            for dy in 0..3 {
                for dx in 0..3 {
                    if dy != 1 || dx != 1 {
                        let yy = (y + dy + n - 1) % n;
                        let xx = (x + dx + n - 1) % n;
                        if cells[yy * n + xx] {
                            alive += 1;
                        }
                    }
                }
            }
            let here = cells[y * n + x];
            next.push(alive == 3 || here && alive == 2);
        }
    }
    next
}

fn main() {
    let n = std::env::args().nth(1).and_then(|a| a.parse().ok()).unwrap_or(256);
    let mut cells = Vec::new();
    let mut x: i64 = 11;
    for _ in 0..n * n {
        x = (x * 1103515245 + 12345) % 2147483648;
        cells.push(x % 3 == 0);
    }
    for _ in 0..60 {
        cells = step(&cells, n);
    }
    println!("{} cells alive", cells.iter().filter(|c| **c).count());
}
