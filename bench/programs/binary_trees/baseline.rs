//! binary-trees: builds perfect binary trees bottom-up and counts their nodes, as the
//! Benchmarks Game's program does, on one thread.

enum Tree {
    Leaf,
    Node(Box<(Tree, Tree)>),
}

fn make(depth: i64) -> Tree {
    if depth == 0 {
        Tree::Node(Box::new((Tree::Leaf, Tree::Leaf)))
    } else {
        Tree::Node(Box::new((make(depth - 1), make(depth - 1))))
    }
}

fn check(tree: &Tree) -> i64 {
    match tree {
        Tree::Leaf => 0,
        Tree::Node(children) => 1 + check(&children.0) + check(&children.1),
    }
}

pub(crate) fn main() {
    let min_depth = 4;
    let max_depth = std::env::args().nth(1).and_then(|a| a.parse().ok()).unwrap_or(16);
    let stretch = max_depth + 1;
    println!("stretch tree of depth {stretch}\t check: {}", check(&make(stretch)));
    let long_lived = make(max_depth);
    let mut depth = min_depth;
    while depth <= max_depth {
        let iterations = 1 << (max_depth - depth + min_depth);
        let mut total = 0;
        for _ in 0..iterations {
            total += check(&make(depth));
        }
        println!("{iterations}\t trees of depth {depth}\t check: {total}");
        depth += 2;
    }
    println!("long lived tree of depth {max_depth}\t check: {}", check(&long_lived));
}
