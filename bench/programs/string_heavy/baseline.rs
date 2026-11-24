//! string-heavy: builds a text of words, then splits, searches, replaces, changes the case of
//! and joins it.

fn main() {
    let size = std::env::args().nth(1).and_then(|a| a.parse().ok()).unwrap_or(200000);
    let mut words = Vec::new();
    let mut x: i64 = 7;
    for _ in 0..size {
        x = (x * 1103515245 + 12345) % 2147483648;
        words.push(format!("w{}", x % 1000));
    }
    let text = words.join(" ");
    let parts: Vec<&str> = text.split(' ').collect();
    let mut lengths = 0;
    let mut sevens = 0;
    for p in &parts {
        lengths += p.len();
        if p.ends_with('7') {
            sevens += 1;
        }
    }
    let replaced = text.replace("w1", "one-");
    let upper = replaced.to_ascii_uppercase();
    let mut digits = 0;
    for b in upper.bytes() {
        if b.is_ascii_digit() {
            digits += 1;
        }
    }
    let found = upper.find("ONE-99 ").map_or(-1, |i| i as i64);
    let lines: Vec<String> = text.replace(" w5", "\nw5").lines().map(String::from).collect();
    let mut longest = 0;
    for line in &lines {
        if line.len() > longest {
            longest = line.len();
        }
    }
    println!("{} bytes, {} words, {lengths} letters, {sevens} sevens", text.len(), parts.len());
    println!("{} replaced, {digits} digits, found at {found}", replaced.len());
    println!(
        "{} lines, longest {longest}, trimmed {}",
        lines.len(),
        format!("  {}  ", &upper[0..20]).trim()
    );
}
