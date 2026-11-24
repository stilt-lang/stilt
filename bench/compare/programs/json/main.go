// json: writes a JSON document of 20000 records, parses it back into a tree with a
// recursive-descent parser, and sums what the tree holds.
package main

import (
	"fmt"
	"strings"
)

// A JSON value: nil, a bool, an int, a string, a []any or a []field.
type field struct {
	key   string
	value any
}

func document(n int) string {
	parts := make([]string, 0, n)
	for i := range n {
		active := "false"
		if i%3 == 0 {
			active = "true"
		}
		note := "null"
		if i%5 != 0 {
			note = fmt.Sprintf(`"line\none \"%d\""`, i)
		}
		parts = append(parts, fmt.Sprintf(
			`{"id": %d, "name": "item%d", "active": %s, "tags": ["a", "b%d"], "point": {"x": %d, "y": [1, 2, %d]}, "note": %s}`,
			i, i, active, i%4, i%7, i%11, note))
	}
	return "[" + strings.Join(parts, ", ") + "]"
}

type parser struct {
	text string
	pos  int
}

func (p *parser) skipSpace() {
	for p.pos < len(p.text) && (p.text[p.pos] == ' ' || p.text[p.pos] == '\n') {
		p.pos++
	}
}

func (p *parser) string() string {
	p.pos++
	var b strings.Builder
	start := p.pos
	for p.text[p.pos] != '"' {
		if p.text[p.pos] == '\\' {
			b.WriteString(p.text[start:p.pos])
			if p.text[p.pos+1] == 'n' {
				b.WriteByte('\n')
			} else {
				b.WriteByte(p.text[p.pos+1])
			}
			p.pos += 2
			start = p.pos
		} else {
			p.pos++
		}
	}
	b.WriteString(p.text[start:p.pos])
	p.pos++
	return b.String()
}

func (p *parser) number() int {
	n := 0
	for p.pos < len(p.text) && p.text[p.pos] >= '0' && p.text[p.pos] <= '9' {
		n = n*10 + int(p.text[p.pos]-'0')
		p.pos++
	}
	return n
}

func (p *parser) value() any {
	p.skipSpace()
	switch p.text[p.pos] {
	case '{':
		p.pos++
		var fields []field
		p.skipSpace()
		for p.text[p.pos] != '}' {
			p.skipSpace()
			key := p.string()
			p.skipSpace()
			p.pos++
			fields = append(fields, field{key, p.value()})
			p.skipSpace()
			if p.text[p.pos] == ',' {
				p.pos++
			}
		}
		p.pos++
		return fields
	case '[':
		p.pos++
		var items []any
		p.skipSpace()
		for p.text[p.pos] != ']' {
			items = append(items, p.value())
			p.skipSpace()
			if p.text[p.pos] == ',' {
				p.pos++
			}
		}
		p.pos++
		return items
	case '"':
		return p.string()
	case 't':
		p.pos += 4
		return true
	case 'f':
		p.pos += 5
		return false
	case 'n':
		p.pos += 4
		return nil
	}
	return p.number()
}

type totals struct{ numbers, texts, trues, nulls, nodes int }

func (t *totals) add(json any) {
	t.nodes++
	switch v := json.(type) {
	case nil:
		t.nulls++
	case bool:
		if v {
			t.trues++
		}
	case int:
		t.numbers += v
	case string:
		t.texts += len(v)
	case []any:
		for _, item := range v {
			t.add(item)
		}
	case []field:
		for _, f := range v {
			t.texts += len(f.key)
			t.add(f.value)
		}
	}
}

func main() {
	source := document(20000)
	p := parser{text: source}
	var t totals
	t.add(p.value())
	fmt.Printf("%d bytes, %d nodes\n", len(source), t.nodes)
	fmt.Printf("numbers %d, text %d, true %d, null %d\n", t.numbers, t.texts, t.trues, t.nulls)
}
