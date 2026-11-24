//! mandelbrot in parallel: the suite's mandelbrot, each row of the grid counted by Rayon.

use rayon::prelude::*;

/// The points of row `y` that stay in the set for 50 iterations, and the iterations of those
/// that escape.
fn row(size: i64, y: i64) -> (i64, i64) {
    let scale = size as f64;
    let ci = 2.0 * y as f64 / scale - 1.0;
    let (mut inside, mut escapes) = (0, 0);
    for x in 0..size {
        let cr = 2.0 * x as f64 / scale - 1.5;
        let (mut zr, mut zi) = (0.0, 0.0);
        let mut i = 0;
        let mut escaped = false;
        while i < 50 && !escaped {
            let next = zr * zr - zi * zi + cr;
            zi = 2.0 * zr * zi + ci;
            zr = next;
            if zr * zr + zi * zi > 4.0 {
                escaped = true;
            }
            i += 1;
        }
        if escaped {
            escapes += i;
        } else {
            inside += 1;
        }
    }
    (inside, escapes)
}

fn main() {
    let size: i64 = std::env::args()
        .nth(1)
        .and_then(|a| a.parse().ok())
        .unwrap_or(4000);
    let rows: Vec<(i64, i64)> = (0..size).into_par_iter().map(|y| row(size, y)).collect();
    let (mut inside, mut escapes) = (0, 0);
    for (i, e) in rows {
        inside += i;
        escapes += e;
    }
    println!("{inside} points inside, {escapes} iterations to escape");
}
