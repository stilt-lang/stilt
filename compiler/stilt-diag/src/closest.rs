//! The closest candidates to a name that a lookup didn't find, which its diagnostic names
//! rather than the whole search (goal closest-candidates). Closeness is rustc's: the edit distance
//! between the two, ignoring case, within a third of the name's length.

use crate::diagnostic::MAX_FIXES;

/// The candidates closest to `name`, nearest first, and at most [`MAX_FIXES`] of them, one for
/// each fix they become. A candidate is close when its distance is at most a third of the
/// name's length, at least one, and shorter than both: so no one-letter name is ever close.
#[must_use]
pub fn closest<'a>(name: &str, candidates: impl IntoIterator<Item = &'a str>) -> Vec<&'a str> {
    close(name, candidates, MAX_FIXES)
}

/// The candidates close to `name`, as [`closest`] finds them, nearest first, and at most
/// `most` of them.
#[must_use]
pub fn close<'a>(
    name: &str,
    candidates: impl IntoIterator<Item = &'a str>,
    most: usize,
) -> Vec<&'a str> {
    let length = name.chars().count();
    let limit = length.max(3) / 3;
    let mut found: Vec<(usize, &str)> = candidates
        .into_iter()
        .filter(|&c| c != name)
        .filter_map(|c| {
            let d = distance(&name.to_lowercase(), &c.to_lowercase());
            (d <= limit && d < length && d < c.chars().count()).then_some((d, c))
        })
        .collect();
    found.sort_unstable();
    found.dedup();
    found.into_iter().take(most).map(|(_, c)| c).collect()
}

/// The optimal string alignment distance between `a` and `b`: the fewest insertions, deletions,
/// substitutions and swaps of two neighbouring characters that turn one into the other.
fn distance(a: &str, b: &str) -> usize {
    let a: Vec<char> = a.chars().collect();
    let b: Vec<char> = b.chars().collect();
    let width = b.len() + 1;
    let mut d: Vec<usize> = vec![0; (a.len() + 1) * width];
    for (i, cell) in d.iter_mut().step_by(width).enumerate() {
        *cell = i;
    }
    for (j, cell) in d.iter_mut().take(width).enumerate() {
        *cell = j;
    }
    for i in 1..=a.len() {
        for j in 1..=b.len() {
            let cost = usize::from(a[i - 1] != b[j - 1]);
            let mut best = (d[(i - 1) * width + j] + 1)
                .min(d[i * width + j - 1] + 1)
                .min(d[(i - 1) * width + j - 1] + cost);
            if i > 1 && j > 1 && a[i - 1] == b[j - 2] && a[i - 2] == b[j - 1] {
                best = best.min(d[(i - 2) * width + j - 2] + 1);
            }
            d[i * width + j] = best;
        }
    }
    d[a.len() * width + b.len()]
}

#[cfg(test)]
mod tests {
    use super::{closest, distance};

    #[test]
    fn counts_a_swap_as_one_edit() {
        assert_eq!(distance("cuont", "count"), 1);
        assert_eq!(distance("size", "len"), 4);
        assert_eq!(distance("", "abc"), 3);
    }

    #[test]
    fn names_the_nearest_candidates_first() {
        let names = ["counts", "count", "total", "amount"];
        assert_eq!(closest("cuont", names), ["count"]);
        assert_eq!(closest("totl", ["total", "tot"]), ["tot", "total"]);
        assert_eq!(closest("Total", names), ["total"]);
    }

    #[test]
    fn finds_nothing_far_or_too_short() {
        let none: [&str; 0] = [];
        assert_eq!(closest("size", ["len", "push"]), none);
        assert_eq!(closest("x", ["y", "n"]), none);
        assert_eq!(closest("count", ["count"]), none);
    }
}
