// sort: sorts a list of integers with the standard library's sort and with a quicksort that
// works in place.
package main

import (
	"cmp"
	"fmt"
	"slices"
)

func quicksort(xs []int, lo, hi int) {
	if lo >= hi {
		return
	}
	pivot := xs[(lo+hi)/2]
	i, j := lo, hi
	for i <= j {
		for xs[i] < pivot {
			i++
		}
		for xs[j] > pivot {
			j--
		}
		if i <= j {
			xs[i], xs[j] = xs[j], xs[i]
			i++
			j--
		}
	}
	quicksort(xs, lo, j)
	quicksort(xs, i, hi)
}

func checksum(xs []int) int {
	sum := 0
	for _, x := range xs {
		sum = (sum*31 + x) % 1000000007
	}
	return sum
}

func main() {
	xs := make([]int, 0, 400000)
	x := 1
	for range 400000 {
		x = (x*1103515245 + 12345) % 2147483648
		xs = append(xs, x%1000000)
	}
	sorted := slices.Clone(xs)
	slices.Sort(sorted)
	quick := slices.Clone(xs)
	quicksort(quick, 0, len(quick)-1)
	byDigit := slices.Clone(xs)
	slices.SortStableFunc(byDigit, func(a, b int) int { return cmp.Compare(a%10, b%10) })
	fmt.Printf("%d %d %d\n", checksum(sorted), checksum(quick), checksum(byDigit))
}
