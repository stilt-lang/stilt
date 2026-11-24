// matmul: multiplies two square matrices of floats, held as lists of rows.
package main

import "fmt"

func matrix(n, seed int) [][]float64 {
	rows := make([][]float64, 0, n)
	for i := range n {
		row := make([]float64, 0, n)
		for j := range n {
			row = append(row, float64((i*j+seed)%17)/17.0)
		}
		rows = append(rows, row)
	}
	return rows
}

func multiply(a, b [][]float64) [][]float64 {
	n := len(a)
	c := make([][]float64, 0, n)
	for i := range n {
		ai := a[i]
		row := make([]float64, 0, n)
		for j := range n {
			sum := 0.0
			for k := range n {
				sum += ai[k] * b[k][j]
			}
			row = append(row, sum)
		}
		c = append(c, row)
	}
	return c
}

func main() {
	n := 250
	c := multiply(matrix(n, 1), matrix(n, 2))
	trace := 0.0
	for i := range n {
		trace += c[i][i]
	}
	fmt.Printf("%.6f %.6f\n", c[n/2][n/3], trace)
}
