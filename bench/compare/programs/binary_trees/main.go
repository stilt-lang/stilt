// binary-trees: builds perfect binary trees bottom-up and counts their nodes, as the
// Benchmarks Game's program does, on one thread.
package main

import "fmt"

type Node struct{ left, right *Node }

func bottomUp(depth int) *Node {
	if depth == 0 {
		return &Node{}
	}
	return &Node{bottomUp(depth - 1), bottomUp(depth - 1)}
}

func (n *Node) check() int {
	if n == nil {
		return 0
	}
	return 1 + n.left.check() + n.right.check()
}

func main() {
	minDepth, maxDepth := 4, 16
	stretch := maxDepth + 1
	fmt.Printf("stretch tree of depth %d\t check: %d\n", stretch, bottomUp(stretch).check())
	longLived := bottomUp(maxDepth)
	for depth := minDepth; depth <= maxDepth; depth += 2 {
		iterations := 1 << (maxDepth - depth + minDepth)
		total := 0
		for range iterations {
			total += bottomUp(depth).check()
		}
		fmt.Printf("%d\t trees of depth %d\t check: %d\n", iterations, depth, total)
	}
	fmt.Printf("long lived tree of depth %d\t check: %d\n", maxDepth, longLived.check())
}
