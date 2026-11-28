//! mandelbrot: counts the points of a grid that stay in the Mandelbrot set for 50 iterations,
//! and the iterations of those that escape.

fn main() {
    let size: i64 = std::env::args().nth(1).and_then(|a| a.parse().ok()).unwrap_or(600);
    let scale = size as f64;
    let mut inside: i64 = 0;
    let mut escapes: i64 = 0;
    for y in 0..size {
        let ci = 2.0 * y as f64 / scale - 1.0;
        for x in 0..size {
            let cr = 2.0 * x as f64 / scale - 1.5;
            let mut zr = 0.0;
            let mut zi = 0.0;
            let mut i: i64 = 0;
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
    }
    println!("{inside} points inside, {escapes} iterations to escape");
}
