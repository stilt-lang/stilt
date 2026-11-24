// map-heavy: inserts, finds, overwrites and removes integer and string keys in hash maps.
package main

import "fmt"

func next(x int) int {
	return (x*1103515245 + 12345) % 2147483648
}

func main() {
	n := 300000
	numbers := make(map[int]int)
	x := 42
	for i := range n {
		x = next(x)
		numbers[x%100000] = i
	}
	hits := 0
	for range n {
		x = next(x)
		if _, ok := numbers[x%200000]; ok {
			hits++
		}
	}
	for k := range 50000 {
		delete(numbers, k*2)
	}
	sum := 0
	for k, v := range numbers {
		sum += k ^ v
	}
	fmt.Printf("%d numbers, %d hits, checksum %d\n", len(numbers), hits, sum)

	words := make(map[string]int)
	for range n {
		x = next(x)
		words[fmt.Sprintf("w%d", x%5000)]++
	}
	longest, most := 0, 0
	for w, count := range words {
		longest = max(longest, len(w))
		most = max(most, count)
	}
	fmt.Printf("%d words, longest %d, most %d\n", len(words), longest, most)
}
