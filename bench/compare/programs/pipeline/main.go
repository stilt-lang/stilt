// pipeline: records through closures: maps, filters, folds and sorts by key, and groups in a
// map.
package main

import (
	"cmp"
	"fmt"
	"slices"
	"strings"
)

type Item struct {
	id, group, score int
	name             string
}

func items(n int) []Item {
	out := make([]Item, 0, n)
	x := 3
	for i := range n {
		x = (x*1103515245 + 12345) % 2147483648
		out = append(out, Item{i, x % 13, x % 1000, fmt.Sprintf("n%d", x%97)})
	}
	return out
}

func mapItems(xs []Item, f func(Item) Item) []Item {
	out := make([]Item, 0, len(xs))
	for _, x := range xs {
		out = append(out, f(x))
	}
	return out
}

func filter(xs []Item, keep func(Item) bool) []Item {
	var out []Item
	for _, x := range xs {
		if keep(x) {
			out = append(out, x)
		}
	}
	return out
}

func fold[T any](xs []T, acc int, f func(int, T) int) int {
	for _, x := range xs {
		acc = f(acc, x)
	}
	return acc
}

func main() {
	all := items(100000)
	total := 0
	for round := range 10 {
		boosted := mapItems(all, func(it Item) Item { return Item{it.id, it.group, it.score + round, it.name} })
		kept := filter(boosted, func(it Item) bool { return it.score%3 != 0 })
		total += fold(kept, 0, func(acc int, it Item) int { return (acc + it.score*it.group) % 1000000007 })
		sorted := slices.Clone(kept)
		slices.SortStableFunc(sorted, func(a, b Item) int { return cmp.Compare(b.score, a.score) })
		best := make([]int, 0, 5)
		for _, it := range sorted[:min(5, len(sorted))] {
			best = append(best, it.id)
		}
		total += fold(best, 0, func(acc, id int) int { return acc + id })
	}
	groups := make(map[int]int)
	for _, it := range all {
		groups[it.group] += it.score
	}
	named := len(filter(all, func(it Item) bool { return strings.HasSuffix(it.name, "7") }))
	top := -1
	if i := slices.IndexFunc(all, func(it Item) bool { return it.score == 999 }); i >= 0 {
		top = all[i].id
	}
	anyHigh := slices.ContainsFunc(all, func(it Item) bool { return it.score > 998 })
	fmt.Printf("%d %d %d %d %t\n", total, groups[4], named, top, anyHigh)
}
