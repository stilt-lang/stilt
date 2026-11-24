// mandelbrot: counts the points of a grid that stay in the Mandelbrot set for 50 iterations,
// and the iterations of those that escape.
package main

import "fmt"

func main() {
	size := 600
	scale := float64(size)
	inside, escapes := 0, 0
	for y := range size {
		ci := 2.0*float64(y)/scale - 1.0
		for x := range size {
			cr := 2.0*float64(x)/scale - 1.5
			zr, zi := 0.0, 0.0
			i := 0
			escaped := false
			for i < 50 && !escaped {
				next := zr*zr - zi*zi + cr
				zi = 2.0*zr*zi + ci
				zr = next
				if zr*zr+zi*zi > 4.0 {
					escaped = true
				}
				i++
			}
			if escaped {
				escapes += i
			} else {
				inside++
			}
		}
	}
	fmt.Printf("%d points inside, %d iterations to escape\n", inside, escapes)
}
