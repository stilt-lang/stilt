// vm: a stack machine interprets a loop that sums the squares of the integers below a bound,
// modulo a prime.

enum Op {
    case push(Int)
    case load(Int)
    case store(Int)
    case add, mul, rem, lt
    case jumpUnless(Int)
    case jump(Int)
    case halt
}

func program(_ bound: Int) -> [Op] {
    [
        .push(0), .store(0),
        .push(0), .store(1),
        .load(0), .push(bound), .lt, .jumpUnless(22),
        .load(1), .load(0), .load(0), .mul, .add, .push(1000003), .rem, .store(1),
        .load(0), .push(1), .add, .store(0),
        .jump(4), .halt,
        .load(1), .halt,
    ]
}

func run(_ code: [Op]) -> Int {
    var stack: [Int] = []
    var locals = [0, 0]
    var pc = 0
    while true {
        switch code[pc] {
        case let .push(n): stack.append(n)
        case let .load(i): stack.append(locals[i])
        case let .store(i): locals[i] = stack.popLast() ?? 0
        case .add:
            let b = stack.popLast() ?? 0, a = stack.popLast() ?? 0
            stack.append(a + b)
        case .mul:
            let b = stack.popLast() ?? 0, a = stack.popLast() ?? 0
            stack.append(a * b)
        case .rem:
            let b = stack.popLast() ?? 0, a = stack.popLast() ?? 0
            stack.append(a % b)
        case .lt:
            let b = stack.popLast() ?? 0, a = stack.popLast() ?? 0
            stack.append(a < b ? 1 : 0)
        case let .jumpUnless(target):
            if (stack.popLast() ?? 0) == 0 {
                pc = target
                continue
            }
        case let .jump(target):
            pc = target
            continue
        case .halt:
            return stack.popLast() ?? 0
        }
        pc += 1
    }
}

print(run(program(1500000)))
