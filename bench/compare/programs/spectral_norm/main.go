// spectral-norm: the spectral norm of an infinite matrix, by the power method, as the
// Benchmarks Game's program computes it.
package main

import (
	"fmt"
	"math"
)

func a(i, j int) float64 {
	return 1.0 / float64((i+j)*(i+j+1)/2+i+1)
}

func times(v []float64) []float64 {
	out := make([]float64, 0, len(v))
	for i := range v {
		sum := 0.0
		for j, vj := range v {
			sum += a(i, j) * vj
		}
		out = append(out, sum)
	}
	return out
}

func timesTransposed(v []float64) []float64 {
	out := make([]float64, 0, len(v))
	for i := range v {
		sum := 0.0
		for j, vj := range v {
			sum += a(j, i) * vj
		}
		out = append(out, sum)
	}
	return out
}

func timesBoth(v []float64) []float64 {
	return timesTransposed(times(v))
}

func main() {
	n := 1000
	u := make([]float64, n)
	for i := range u {
		u[i] = 1.0
	}
	var v []float64
	for range 10 {
		v = timesBoth(u)
		u = timesBoth(v)
	}
	vbv, vv := 0.0, 0.0
	for i := range n {
		vbv += u[i] * v[i]
		vv += v[i] * v[i]
	}
	fmt.Printf("%.9f\n", math.Sqrt(vbv/vv))
}
