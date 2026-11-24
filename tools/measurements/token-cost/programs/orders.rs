use std::collections::HashMap;
use std::{env, fs, process};

/// One validated row of the orders file.
struct Order {
    customer: String,
    qty: i64,
    price: f64,
}

/// Parses one `customer,qty,price` row.
fn parse_line(n: usize, text: &str) -> Result<Order, String> {
    let [customer, q, p] = text.split(',').collect::<Vec<_>>()[..] else {
        return Err(format!("line {n}: expected 3 fields"));
    };
    let qty: i64 = q.parse().map_err(|_| format!("line {n}: bad qty {q}"))?;
    let price: f64 = p.parse().map_err(|_| format!("line {n}: bad price {p}"))?;
    if qty <= 0 {
        return Err(format!("line {n}: qty must be positive"));
    }
    Ok(Order { customer: customer.to_string(), qty, price })
}

/// Revenue per customer, largest first.
fn totals(orders: &[Order]) -> Vec<(String, f64)> {
    let mut sums: HashMap<String, f64> = HashMap::new();
    for o in orders {
        *sums.entry(o.customer.clone()).or_insert(0.0) += o.qty as f64 * o.price;
    }
    let mut sorted: Vec<(String, f64)> = sums.into_iter().collect();
    sorted.sort_by(|a, b| b.1.total_cmp(&a.1));
    sorted
}

fn run() -> Result<(), String> {
    let path = env::args().nth(1).ok_or("usage: orders <file>")?;
    let text = fs::read_to_string(&path).map_err(|_| format!("cannot read {path}"))?;
    let orders = text
        .lines()
        .skip(1)
        .enumerate()
        .map(|(i, l)| parse_line(i + 2, l))
        .collect::<Result<Vec<_>, _>>()?;
    for (c, t) in totals(&orders).iter().take(3) {
        println!("{c}: {t:.2}");
    }
    Ok(())
}

fn main() {
    if let Err(e) = run() {
        eprintln!("error: {e}");
        process::exit(1);
    }
}
