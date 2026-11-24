// binarytrees: builds perfect binary trees bottom-up and counts their nodes, from a stretch tree of
// depth 22 down to trees of depth 4, while one of depth 21 lives throughout, as the Benchmarks
// Game's program does, on one thread (Reinking et al., Perceus, PLDI 2021).

indirect enum Tree {
    case tip
    case node(Tree, Tree)
}

func make(_ depth: Int) -> Tree {
    depth > 0 ? .node(make(depth - 1), make(depth - 1)) : .node(.tip, .tip)
}

func check(_ t: Tree) -> Int {
    if case let .node(l, r) = t { return check(l) + check(r) + 1 }
    return 0
}

let minDepth = 4
let maxDepth = 21
let stretch = maxDepth + 1
print("stretch tree of depth \(stretch)\t check: \(check(make(stretch)))")
let longLived = make(maxDepth)
for depth in stride(from: minDepth, through: maxDepth, by: 2) {
    let count = 1 << (maxDepth + minDepth - depth)
    var total = 0
    for _ in 0..<count { total += check(make(depth)) }
    print("\(count)\t trees of depth \(depth)\t check: \(total)")
}
print("long lived tree of depth \(maxDepth)\t check: \(check(longLived))")
