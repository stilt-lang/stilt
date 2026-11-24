// deriv: differentiates x^x ten times, simplifying each derivative as it is built, and prints the
// size of each (Reinking et al., Perceus, PLDI 2021).

indirect enum Expr {
    case val(Int)
    case variable(String)
    case add(Expr, Expr)
    case mul(Expr, Expr)
    case pow(Expr, Expr)
    case ln(Expr)
}

func pown(_ a: Int, _ n: Int) -> Int {
    var r = 1
    for _ in 0..<max(n, 0) { r *= a }
    return r
}

func add(_ a: Expr, _ b: Expr) -> Expr {
    switch (a, b) {
    case let (.val(n), .val(m)): return .val(n + m)
    case (.val(0), let f), (let f, .val(0)): return f
    case let (f, .val(n)): return add(.val(n), f)
    case let (.val(n), .add(.val(m), f)): return add(.val(n + m), f)
    case let (f, .add(.val(n), g)): return add(.val(n), add(f, g))
    case let (.add(f, g), h): return add(f, add(g, h))
    case let (f, g): return .add(f, g)
    }
}

func mul(_ a: Expr, _ b: Expr) -> Expr {
    switch (a, b) {
    case let (.val(n), .val(m)): return .val(n * m)
    case (.val(0), _), (_, .val(0)): return .val(0)
    case (.val(1), let f), (let f, .val(1)): return f
    case let (f, .val(n)): return mul(.val(n), f)
    case let (.val(n), .mul(.val(m), f)): return mul(.val(n * m), f)
    case let (f, .mul(.val(n), g)): return mul(.val(n), mul(f, g))
    case let (.mul(f, g), h): return mul(f, mul(g, h))
    case let (f, g): return .mul(f, g)
    }
}

func pow(_ a: Expr, _ b: Expr) -> Expr {
    switch (a, b) {
    case let (.val(m), .val(n)): return .val(pown(m, n))
    case (_, .val(0)): return .val(1)
    case (let f, .val(1)): return f
    case (.val(0), _): return .val(0)
    case let (f, g): return .pow(f, g)
    }
}

func ln(_ e: Expr) -> Expr {
    if case .val(1) = e { return .val(0) }
    return .ln(e)
}

/// The derivative of `e` by `x`.
func d(_ x: String, _ e: Expr) -> Expr {
    switch e {
    case .val: return .val(0)
    case let .variable(y): return .val(x == y ? 1 : 0)
    case let .add(f, g): return add(d(x, f), d(x, g))
    case let .mul(f, g): return add(mul(f, d(x, g)), mul(g, d(x, f)))
    case let .pow(f, g):
        return mul(pow(f, g), add(mul(mul(g, d(x, f)), pow(f, .val(-1))), mul(ln(f), d(x, g))))
    case let .ln(f): return mul(d(x, f), pow(f, .val(-1)))
    }
}

func count(_ e: Expr) -> Int {
    switch e {
    case .val, .variable: return 1
    case let .add(f, g), let .mul(f, g), let .pow(f, g): return count(f) + count(g)
    case let .ln(f): return count(f)
    }
}

let x = Expr.variable("x")
var f = pow(x, x)
for i in 1...10 {
    f = d("x", f)
    print("\(i) count: \(count(f))")
}
print("done")
