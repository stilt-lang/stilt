// nsieve: counts the primes below three bounds with the sieve of Eratosthenes, as the
// Benchmarks Game's former program does.
package main

import "fmt"

func primes(m int) int {
	flags := make([]bool, m+1)
	for i := range flags {
		flags[i] = true
	}
	count := 0
	for i := 2; i <= m; i++ {
		if flags[i] {
			count++
			for k := i + i; k <= m; k += i {
				flags[k] = false
			}
		}
	}
	return count
}

func main() {
	for shift := range 3 {
		m := (1 << (22 - shift)) * 10000 / 4096
		fmt.Printf("Primes up to %8d %8d\n", m, primes(m))
	}
}
