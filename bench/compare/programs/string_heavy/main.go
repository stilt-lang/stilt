// string-heavy: builds a text of words, then splits, searches, replaces, changes the case of
// and joins it.
package main

import (
	"fmt"
	"strings"
)

func main() {
	words := make([]string, 0, 200000)
	x := 7
	for range 200000 {
		x = (x*1103515245 + 12345) % 2147483648
		words = append(words, fmt.Sprintf("w%d", x%1000))
	}
	text := strings.Join(words, " ")
	parts := strings.Split(text, " ")
	lengths, sevens := 0, 0
	for _, p := range parts {
		lengths += len(p)
		if strings.HasSuffix(p, "7") {
			sevens++
		}
	}
	replaced := strings.ReplaceAll(text, "w1", "one-")
	upper := strings.ToUpper(replaced)
	digits := 0
	for i := range len(upper) {
		if upper[i] >= '0' && upper[i] <= '9' {
			digits++
		}
	}
	found := strings.Index(upper, "ONE-99 ")
	lines := strings.Split(strings.ReplaceAll(text, " w5", "\nw5"), "\n")
	longest := 0
	for _, line := range lines {
		longest = max(longest, len(line))
	}
	fmt.Printf("%d bytes, %d words, %d letters, %d sevens\n", len(text), len(parts), lengths, sevens)
	fmt.Printf("%d replaced, %d digits, found at %d\n", len(replaced), digits, found)
	trimmed := strings.TrimSpace("  " + upper[:20] + "  ")
	fmt.Printf("%d lines, longest %d, trimmed %s\n", len(lines), longest, trimmed)
}
