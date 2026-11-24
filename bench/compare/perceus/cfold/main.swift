// cfold: builds an expression of 2^20 sums, reassociates it into a chain and folds its constants,
// then evaluates it before and after (Reinking et al., Perceus, PLDI 2021).

indirect enum Expr {
    case variable(Int)
    case val(Int)
    case add(Expr, Expr)
    case mul(Expr, Expr)
}

func make(_ n: Int, _ v: Int) -> Expr {
    if n == 0 { return v == 0 ? .variable(1) : .val(v) }
    return .add(make(n - 1, v + 1), make(n - 1, max(v - 1, 0)))
}

func appendAdd(_ a: Expr, _ b: Expr) -> Expr {
    if case let .add(x, y) = a { return .add(x, appendAdd(y, b)) }
    return .add(a, b)
}

func appendMul(_ a: Expr, _ b: Expr) -> Expr {
    if case let .mul(x, y) = a { return .mul(x, appendMul(y, b)) }
    return .mul(a, b)
}

func reassoc(_ e: Expr) -> Expr {
    switch e {
    case let .add(a, b): return appendAdd(reassoc(a), reassoc(b))
    case let .mul(a, b): return appendMul(reassoc(a), reassoc(b))
    default: return e
    }
}

func fold(_ e: Expr) -> Expr {
    switch e {
    case let .add(a, b):
        switch (fold(a), fold(b)) {
        case let (.val(x), .val(y)): return .val(x + y)
        case let (.val(x), .add(f, .val(y))), let (.val(x), .add(.val(y), f)): return .add(.val(x + y), f)
        case let (a, b): return .add(a, b)
        }
    case let .mul(a, b):
        switch (fold(a), fold(b)) {
        case let (.val(x), .val(y)): return .val(x * y)
        case let (.val(x), .mul(f, .val(y))), let (.val(x), .mul(.val(y), f)): return .mul(.val(x * y), f)
        case let (a, b): return .mul(a, b)
        }
    default:
        return e
    }
}

func eval(_ e: Expr) -> Int {
    switch e {
    case .variable: return 0
    case let .val(v): return v
    case let .add(a, b): return eval(a) + eval(b)
    case let .mul(a, b): return eval(a) * eval(b)
    }
}

let e = make(20, 1)
print(eval(e))
print(eval(fold(reassoc(e))))
