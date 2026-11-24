// fasta: writes random DNA sequences, from cumulative probabilities and a linear congruential
// generator, and a repeated one, as the Benchmarks Game's program does, in lines of 60.
package main

import (
	"bufio"
	"os"
)

const alu = "GGCCGGGCGCGGTGGCTCACGCCTGTAATCCCAGCACTTTGGGAGGCCGAGGCGGGCGGATCACCTGAGGTCAGGAGTTCGAGACCAGCCTGGCCAACATGGTGAAACCCCGTCTCTACTAAAAATACAAAAATTAGCCGGGCGTGGTGGCGCGCGCCTGTAATCCCAGCTACTCGGGAGGCTGAGGCAGGAGAATCGCTTGAACCCGGGAGGCGGAGGTTGCAGTGAGCCGAGATCGCGCCACTGCACTCCAGCCTGGGCGACAGAGCGAGACTCCGTCTCAAAAA"

func random(seed *int) float64 {
	*seed = (*seed*3877 + 29573) % 139968
	return float64(*seed) / 139968.0
}

func repeat(out *bufio.Writer, n int) {
	start := 0
	for left := n; left > 0; {
		width := min(left, 60)
		line := make([]byte, width)
		for i := range line {
			line[i] = alu[(start+i)%len(alu)]
		}
		out.Write(line)
		out.WriteByte('\n')
		start = (start + width) % len(alu)
		left -= width
	}
}

func randomly(out *bufio.Writer, symbols string, chances []float64, n int, seed *int) {
	cumulative := make([]float64, len(chances))
	sum := 0.0
	for i, c := range chances {
		sum += c
		cumulative[i] = sum
	}
	for left := n; left > 0; {
		width := min(left, 60)
		line := make([]byte, width)
		for i := range line {
			r := random(seed)
			k := 0
			for k < len(cumulative)-1 && r >= cumulative[k] {
				k++
			}
			line[i] = symbols[k]
		}
		out.Write(line)
		out.WriteByte('\n')
		left -= width
	}
}

func main() {
	out := bufio.NewWriter(os.Stdout)
	defer out.Flush()
	n := 100000
	seed := 42
	out.WriteString(">ONE Homo sapiens alu\n")
	repeat(out, n*2)
	out.WriteString(">TWO IUB ambiguity codes\n")
	iubChances := []float64{0.27, 0.12, 0.12, 0.27, 0.02, 0.02, 0.02, 0.02, 0.02, 0.02, 0.02, 0.02, 0.02, 0.02, 0.02}
	randomly(out, "acgtBDHKMNRSVWY", iubChances, n*3, &seed)
	out.WriteString(">THREE Homo sapiens frequency\n")
	sapiensChances := []float64{0.3029549426680, 0.1979883004921, 0.1975473066391, 0.3015094502008}
	randomly(out, "acgt", sapiensChances, n*5, &seed)
}
