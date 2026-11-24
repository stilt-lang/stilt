//! spectral-norm: the spectral norm of an infinite matrix, by the power method, as the
//! Benchmarks Game's program computes it.

fn a(i: i64, j: i64) -> f64 {
    1.0 / ((i + j) * (i + j + 1) / 2 + i + 1) as f64
}

fn times(v: &[f64]) -> Vec<f64> {
    let n = v.len();
    let mut out = Vec::new();
    for i in 0..n {
        let mut sum = 0.0;
        for j in 0..n {
            sum += a(i as i64, j as i64) * v[j];
        }
        out.push(sum);
    }
    out
}

fn times_transposed(v: &[f64]) -> Vec<f64> {
    let n = v.len();
    let mut out = Vec::new();
    for i in 0..n {
        let mut sum = 0.0;
        for j in 0..n {
            sum += a(j as i64, i as i64) * v[j];
        }
        out.push(sum);
    }
    out
}

fn times_both(v: &[f64]) -> Vec<f64> {
    times_transposed(&times(v))
}

fn main() {
    let n = std::env::args().nth(1).and_then(|a| a.parse().ok()).unwrap_or(1000);
    let mut u = Vec::new();
    for _ in 0..n {
        u.push(1.0);
    }
    let mut v = Vec::new();
    for _ in 0..10 {
        v = times_both(&u);
        u = times_both(&v);
    }
    let mut vbv = 0.0;
    let mut vv = 0.0;
    for i in 0..n {
        vbv += u[i] * v[i];
        vv += v[i] * v[i];
    }
    println!("{:.9}", (vbv / vv).sqrt());
}
