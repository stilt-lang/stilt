//! pipeline: records through closures: maps, filters, folds and sorts by key, and groups in a
//! map.

use std::collections::HashMap;

#[derive(Clone)]
struct Item {
    id: i64,
    group: i64,
    score: i64,
    name: String,
}

fn items(n: i64) -> Vec<Item> {
    let mut out = Vec::new();
    let mut x: i64 = 3;
    for i in 0..n {
        x = (x * 1103515245 + 12345) % 2147483648;
        out.push(Item { id: i, group: x % 13, score: x % 1000, name: format!("n{}", x % 97) });
    }
    out
}

fn main() {
    let size = std::env::args().nth(1).and_then(|a| a.parse().ok()).unwrap_or(100000);
    let all = items(size);
    let mut total = 0;
    for round in 0..10 {
        let boosted: Vec<Item> = all
            .iter()
            .map(|it| Item { id: it.id, group: it.group, score: it.score + round, name: it.name.clone() })
            .collect();
        let kept: Vec<Item> = boosted.into_iter().filter(|it| it.score % 3 != 0).collect();
        total += kept.iter().fold(0, |acc, it| (acc + it.score * it.group) % 1000000007);
        let mut kept = kept;
        kept.sort_by_key(|it| std::cmp::Reverse(it.score));
        let best: Vec<i64> = kept.iter().take(5).map(|it| it.id).collect();
        total += best.iter().fold(0, |acc, id| acc + id);
    }
    let mut groups: HashMap<i64, i64> = HashMap::new();
    for it in &all {
        *groups.entry(it.group).or_insert(0) += it.score;
    }
    let named = all.iter().filter(|it| it.name.ends_with('7')).count();
    let top = all.iter().find(|it| it.score == 999).map_or(-1, |it| it.id);
    println!(
        "{total} {} {named} {top} {}",
        groups.get(&4).copied().unwrap_or(0),
        all.iter().any(|it| it.score > 998)
    );
}
