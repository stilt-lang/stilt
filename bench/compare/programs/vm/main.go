// vm: a stack machine interprets a loop that sums the squares of the integers below a bound,
// modulo a prime.
package main

import "fmt"

type Code int

const (
	Push Code = iota
	Load
	Store
	Add
	Mul
	Rem
	Lt
	JumpUnless
	Jump
	Halt
)

type Op struct {
	code Code
	arg  int
}

func program(bound int) []Op {
	return []Op{
		{Push, 0}, {Store, 0},
		{Push, 0}, {Store, 1},
		{Load, 0}, {Push, bound}, {Lt, 0}, {JumpUnless, 22},
		{Load, 1}, {Load, 0}, {Load, 0}, {Mul, 0}, {Add, 0}, {Push, 1000003}, {Rem, 0}, {Store, 1},
		{Load, 0}, {Push, 1}, {Add, 0}, {Store, 0},
		{Jump, 4}, {Halt, 0},
		{Load, 1}, {Halt, 0},
	}
}

type stack []int

func (s *stack) push(n int) { *s = append(*s, n) }

func (s *stack) pop() int {
	if len(*s) == 0 {
		return 0
	}
	n := (*s)[len(*s)-1]
	*s = (*s)[:len(*s)-1]
	return n
}

func run(code []Op) int {
	var s stack
	locals := []int{0, 0}
	pc := 0
	for {
		op := code[pc]
		switch op.code {
		case Push:
			s.push(op.arg)
		case Load:
			s.push(locals[op.arg])
		case Store:
			locals[op.arg] = s.pop()
		case Add:
			b, a := s.pop(), s.pop()
			s.push(a + b)
		case Mul:
			b, a := s.pop(), s.pop()
			s.push(a * b)
		case Rem:
			b, a := s.pop(), s.pop()
			s.push(a % b)
		case Lt:
			b, a := s.pop(), s.pop()
			if a < b {
				s.push(1)
			} else {
				s.push(0)
			}
		case JumpUnless:
			if s.pop() == 0 {
				pc = op.arg
				continue
			}
		case Jump:
			pc = op.arg
			continue
		case Halt:
			return s.pop()
		}
		pc++
	}
}

func main() {
	fmt.Println(run(program(1500000)))
}
