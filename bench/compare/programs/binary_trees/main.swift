// binary-trees: builds perfect binary trees bottom-up and counts their nodes, as the
// Benchmarks Game's program does, on one thread.

indirect enum Tree {
    case leaf
    case node(Tree, Tree)
}

func make(_ depth: Int) -> Tree {
    depth == 0 ? .node(.leaf, .leaf) : .node(make(depth - 1), make(depth - 1))
}

func check(_ tree: Tree) -> Int {
    if case let .node(left, right) = tree { return 1 + check(left) + check(right) }
    return 0
}

let minDepth = 4
let maxDepth = 16
let stretch = maxDepth + 1
print("stretch tree of depth \(stretch)\t check: \(check(make(stretch)))")
let longLived = make(maxDepth)
for depth in stride(from: minDepth, through: maxDepth, by: 2) {
    let iterations = 1 << (maxDepth - depth + minDepth)
    var total = 0
    for _ in 0..<iterations { total += check(make(depth)) }
    print("\(iterations)\t trees of depth \(depth)\t check: \(total)")
}
print("long lived tree of depth \(maxDepth)\t check: \(check(longLived))")
