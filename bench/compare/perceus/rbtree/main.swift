// rbtree: inserts 4,200,000 keys into a red-black tree, the value of every tenth true, and folds
// over the tree to count the true values (Reinking et al., Perceus, PLDI 2021).

enum Color { case red, black }

indirect enum Tree {
    case leaf
    case node(Color, Tree, Int, Bool, Tree)
}

func isRed(_ t: Tree) -> Bool {
    if case .node(.red, _, _, _, _) = t { return true }
    return false
}

/// Rebalances a black node whose left child `l` is red.
func balanceLeft(_ l: Tree, _ k: Int, _ v: Bool, _ r: Tree) -> Tree {
    switch l {
    case let .node(_, .node(.red, a, ka, va, b), kb, vb, c),
         let .node(_, a, ka, va, .node(.red, b, kb, vb, c)):
        return .node(.red, .node(.black, a, ka, va, b), kb, vb, .node(.black, c, k, v, r))
    case let .node(_, a, ka, va, b):
        return .node(.black, .node(.red, a, ka, va, b), k, v, r)
    case .leaf:
        return .leaf
    }
}

/// Rebalances a black node whose right child `r` is red.
func balanceRight(_ l: Tree, _ k: Int, _ v: Bool, _ r: Tree) -> Tree {
    switch r {
    case let .node(_, .node(.red, a, ka, va, b), kb, vb, c),
         let .node(_, a, ka, va, .node(.red, b, kb, vb, c)):
        return .node(.red, .node(.black, l, k, v, a), ka, va, .node(.black, b, kb, vb, c))
    case let .node(_, a, ka, va, b):
        return .node(.black, l, k, v, .node(.red, a, ka, va, b))
    case .leaf:
        return .leaf
    }
}

func ins(_ t: Tree, _ k: Int, _ v: Bool) -> Tree {
    switch t {
    case .leaf:
        return .node(.red, .leaf, k, v, .leaf)
    case let .node(.red, l, kx, vx, r):
        if k < kx { return .node(.red, ins(l, k, v), kx, vx, r) }
        if k > kx { return .node(.red, l, kx, vx, ins(r, k, v)) }
        return .node(.red, l, k, v, r)
    case let .node(.black, l, kx, vx, r):
        if k < kx {
            return isRed(l) ? balanceLeft(ins(l, k, v), kx, vx, r) : .node(.black, ins(l, k, v), kx, vx, r)
        }
        if k > kx {
            return isRed(r) ? balanceRight(l, kx, vx, ins(r, k, v)) : .node(.black, l, kx, vx, ins(r, k, v))
        }
        return .node(.black, l, k, v, r)
    }
}

func insert(_ t: Tree, _ k: Int, _ v: Bool) -> Tree {
    if case let .node(_, l, kx, vx, r) = ins(t, k, v) { return .node(.black, l, kx, vx, r) }
    return .leaf
}

func fold<A>(_ t: Tree, _ acc: A, _ f: (Int, Bool, A) -> A) -> A {
    switch t {
    case .leaf: return acc
    case let .node(_, l, k, v, r): return fold(r, f(k, v, fold(l, acc, f)), f)
    }
}

func makeTree(_ n: Int) -> Tree {
    var t = Tree.leaf
    for k in stride(from: n - 1, through: 0, by: -1) {
        t = insert(t, k, k % 10 == 0)
    }
    return t
}

print(fold(makeTree(4_200_000), 0) { _, v, count in v ? count + 1 : count })
