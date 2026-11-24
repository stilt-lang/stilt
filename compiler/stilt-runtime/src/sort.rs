//! The stable sort of `sorted_by` and `sorted_desc_by` (std.list-sorting): a merge sort that takes
//! one buffer for the whole sort, half the items long, and sorts short runs by insertion
//! (goal debug-speed). How often, and in which order, it compares keys is unspecified, so
//! the order it asks in is free; it ends whatever its order answers. Keys whose order is the
//! structural `Ord` of an integer type are integers compared as such, by the standard
//! library's stable sort, without a call per comparison.

use std::cmp::Reverse;

/// Runs this short or shorter are sorted by insertion, which costs less than merging them: it
/// copies nothing out and back, and calls nothing more.
const RUN: usize = 16;

/// Sorts `items` so that no item comes after one it is `after`, keeping the order of the
/// others.
pub(crate) fn merge_sort<T: Copy>(items: &mut [T], after: &impl Fn(&T, &T) -> bool) {
    let mut buf = Vec::with_capacity(items.len() / 2);
    sort(items, &mut buf, after);
}

fn sort<T: Copy>(items: &mut [T], buf: &mut Vec<T>, after: &impl Fn(&T, &T) -> bool) {
    if items.len() <= RUN {
        insertion(items, after);
        return;
    }
    let mid = items.len() / 2;
    sort(&mut items[..mid], buf, after);
    sort(&mut items[mid..], buf, after);
    // Two halves already in order, as a sorted list's are, need no merge.
    if after(&items[mid - 1], &items[mid]) {
        merge(items, mid, buf, after);
    }
}

/// Moves each item left until the item before it doesn't come after it, so equal items keep
/// their order.
fn insertion<T: Copy>(items: &mut [T], after: &impl Fn(&T, &T) -> bool) {
    for i in 1..items.len() {
        let x = items[i];
        let mut j = i;
        while j > 0 && after(&items[j - 1], &x) {
            items[j] = items[j - 1];
            j -= 1;
        }
        items[j] = x;
    }
}

/// Merges the sorted halves `items[..mid]` and `items[mid..]`: the left half goes to `buf`, and
/// the merge writes from the front, never past the right half's next item. An item of the right
/// half goes first only when the left one comes after it, so equal items keep their order.
fn merge<T: Copy>(items: &mut [T], mid: usize, buf: &mut Vec<T>, after: &impl Fn(&T, &T) -> bool) {
    buf.clear();
    buf.extend_from_slice(&items[..mid]);
    let (mut i, mut j, mut k) = (0, mid, 0);
    while i < buf.len() && j < items.len() {
        if after(&buf[i], &items[j]) {
            items[k] = items[j];
            j += 1;
        } else {
            items[k] = buf[i];
            i += 1;
        }
        k += 1;
    }
    // What is left of the right half is in place already.
    let rest = buf.len() - i;
    items[k..k + rest].copy_from_slice(&buf[i..]);
}

/// Sorts `keyed` by its integer keys, signed or not, in descending order if `descending`,
/// keeping equal keys in their order. A narrow integer is held extended to a word, with its
/// sign if it has one, so the words compare as their integers do.
pub(crate) fn sort_integers(keyed: &mut [(u64, usize)], signed: bool, descending: bool) {
    match (signed, descending) {
        (true, false) => keyed.sort_by_key(|&(k, _)| k.cast_signed()),
        (true, true) => keyed.sort_by_key(|&(k, _)| Reverse(k.cast_signed())),
        (false, false) => keyed.sort_by_key(|&(k, _)| k),
        (false, true) => keyed.sort_by_key(|&(k, _)| Reverse(k)),
    }
}

#[cfg(test)]
mod tests {
    use super::{merge_sort, sort_integers};

    /// Sorts the positions of `keys` by key.
    fn sorted(keys: &[i64]) -> Vec<usize> {
        let mut items: Vec<(i64, usize)> = keys.iter().copied().zip(0..).collect();
        merge_sort(&mut items, &|a, b| a.0 > b.0);
        items.into_iter().map(|(_, i)| i).collect()
    }

    #[test]
    fn the_sort_is_stable() {
        assert_eq!(sorted(&[3, 1, 2, 1, 3, 0]), vec![5, 1, 3, 2, 0, 4]);
    }

    #[test]
    fn long_runs_merge_stably() {
        // Past the length sorted by insertion, with many equal keys.
        let keys: Vec<i64> = (0..1000).map(|i| (i * 7919) % 13).collect();
        let order = sorted(&keys);
        let mut expected: Vec<usize> = (0..keys.len()).collect();
        expected.sort_by_key(|&i| keys[i]);
        assert_eq!(order, expected);
    }

    #[test]
    fn a_sorted_list_stays_as_it_is() {
        let keys: Vec<i64> = (0..100).collect();
        assert_eq!(sorted(&keys), (0..100).collect::<Vec<_>>());
    }

    #[test]
    fn an_inconsistent_order_still_ends() {
        let mut order: Vec<usize> = (0..50).collect();
        merge_sort(&mut order, &|a, b| (a * 7 + b) % 3 == 0);
        order.sort_unstable();
        assert_eq!(order, (0..50).collect::<Vec<_>>());
    }

    /// The positions of `keys`, sorted as integers.
    fn by_integer(keys: &[i64], signed: bool, descending: bool) -> Vec<usize> {
        let mut keyed: Vec<(u64, usize)> =
            keys.iter().map(|k| k.cast_unsigned()).zip(0..).collect();
        sort_integers(&mut keyed, signed, descending);
        keyed.into_iter().map(|(_, i)| i).collect()
    }

    #[test]
    fn signed_keys_sort_below_zero_first() {
        assert_eq!(by_integer(&[3, -1, 0, -5], true, false), vec![3, 1, 2, 0]);
    }

    #[test]
    fn unsigned_keys_sort_past_the_signed_maximum_last() {
        // `u64.MAX` is held as the word of all ones.
        assert_eq!(by_integer(&[-1, 2, 0], false, false), vec![2, 1, 0]);
    }

    #[test]
    fn equal_integer_keys_keep_their_order_both_ways() {
        let keys = [2, 1, 2, 1];
        assert_eq!(by_integer(&keys, true, false), vec![1, 3, 0, 2]);
        assert_eq!(by_integer(&keys, true, true), vec![0, 2, 1, 3]);
    }
}
