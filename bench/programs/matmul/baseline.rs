//! matmul: multiplies two square matrices of floats, held as lists of rows.

fn matrix(n: i64, seed: i64) -> Vec<Vec<f64>> {
    let mut rows = Vec::new();
    for i in 0..n {
        let mut row = Vec::new();
        for j in 0..n {
            row.push(((i * j + seed) % 17) as f64 / 17.0);
        }
        rows.push(row);
    }
    rows
}

fn multiply(a: &[Vec<f64>], b: &[Vec<f64>]) -> Vec<Vec<f64>> {
    let n = a.len();
    let mut c = Vec::new();
    for i in 0..n {
        let ai = &a[i];
        let mut row = Vec::new();
        for j in 0..n {
            let mut sum = 0.0;
            for k in 0..n {
                sum += ai[k] * b[k][j];
            }
            row.push(sum);
        }
        c.push(row);
    }
    c
}

fn main() {
    let n = std::env::args().nth(1).and_then(|a| a.parse().ok()).unwrap_or(250);
    let c = multiply(&matrix(n, 1), &matrix(n, 2));
    let mut trace = 0.0;
    for i in 0..n as usize {
        trace += c[i][i];
    }
    println!("{:.6} {:.6}", c[n as usize / 2][n as usize / 3], trace);
}
