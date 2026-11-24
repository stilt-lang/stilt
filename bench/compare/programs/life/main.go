// life: runs Conway's Game of Life on a grid that wraps around, held as one list of cells.
package main

import "fmt"

func step(cells []bool, n int) []bool {
	next := make([]bool, 0, n*n)
	for y := range n {
		for x := range n {
			alive := 0
			for dy := range 3 {
				for dx := range 3 {
					if dy != 1 || dx != 1 {
						yy := (y + dy + n - 1) % n
						xx := (x + dx + n - 1) % n
						if cells[yy*n+xx] {
							alive++
						}
					}
				}
			}
			here := cells[y*n+x]
			next = append(next, alive == 3 || here && alive == 2)
		}
	}
	return next
}

func main() {
	n := 256
	cells := make([]bool, 0, n*n)
	x := 11
	for range n * n {
		x = (x*1103515245 + 12345) % 2147483648
		cells = append(cells, x%3 == 0)
	}
	for range 60 {
		cells = step(cells, n)
	}
	alive := 0
	for _, c := range cells {
		if c {
			alive++
		}
	}
	fmt.Printf("%d cells alive\n", alive)
}
