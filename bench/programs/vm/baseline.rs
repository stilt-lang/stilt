//! vm: a stack machine interprets a loop that sums the squares of the integers below a bound,
//! modulo a prime.

enum Op {
    Push(i64),
    Load(usize),
    Store(usize),
    Add,
    Mul,
    Rem,
    Lt,
    JumpUnless(usize),
    Jump(usize),
    Halt,
}

use Op::*;

fn program(bound: i64) -> Vec<Op> {
    vec![
        Push(0), Store(0),
        Push(0), Store(1),
        Load(0), Push(bound), Lt, JumpUnless(22),
        Load(1), Load(0), Load(0), Mul, Add, Push(1000003), Rem, Store(1),
        Load(0), Push(1), Add, Store(0),
        Jump(4), Halt,
        Load(1), Halt,
    ]
}

fn run(code: &[Op]) -> i64 {
    let mut stack = Vec::new();
    let mut locals = vec![0, 0];
    let mut pc = 0;
    loop {
        match code[pc] {
            Push(n) => stack.push(n),
            Load(i) => stack.push(locals[i]),
            Store(i) => locals[i] = stack.pop().unwrap_or(0),
            Add => {
                let b = stack.pop().unwrap_or(0);
                let a = stack.pop().unwrap_or(0);
                stack.push(a + b);
            }
            Mul => {
                let b = stack.pop().unwrap_or(0);
                let a = stack.pop().unwrap_or(0);
                stack.push(a * b);
            }
            Rem => {
                let b = stack.pop().unwrap_or(0);
                let a = stack.pop().unwrap_or(0);
                stack.push(a % b);
            }
            Lt => {
                let b = stack.pop().unwrap_or(0);
                let a = stack.pop().unwrap_or(0);
                stack.push(if a < b { 1 } else { 0 });
            }
            JumpUnless(target) => {
                if stack.pop().unwrap_or(0) == 0 {
                    pc = target;
                    continue;
                }
            }
            Jump(target) => {
                pc = target;
                continue;
            }
            Halt => return stack.pop().unwrap_or(0),
        }
        pc += 1;
    }
}

fn main() {
    let size = std::env::args().nth(1).and_then(|a| a.parse().ok()).unwrap_or(1500000);
    println!("{}", run(&program(size)));
}
