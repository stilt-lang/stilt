//! binarytrees: builds perfect binary trees bottom-up and counts their nodes, from a stretch tree
//! of depth 22 down to trees of depth 4, while one of depth 21 lives throughout, as the Benchmarks
//! Game's program does, on one thread (Reinking et al., Perceus, PLDI 2021).

struct Node {
    left: Tree,
    right: Tree,
}

type Tree = Option<Box<Node>>;

fn make(depth: i64) -> Tree {
    let (left, right) = if depth > 0 {
        (make(depth - 1), make(depth - 1))
    } else {
        (None, None)
    };
    Some(Box::new(Node { left, right }))
}

fn check(t: &Tree) -> i64 {
    match t {
        Some(n) => check(&n.left) + check(&n.right) + 1,
        None => 0,
    }
}

pub(crate) fn main() {
    let min_depth = 4;
    let max_depth = 21;
    let stretch = max_depth + 1;
    println!(
        "stretch tree of depth {stretch}\t check: {}",
        check(&make(stretch))
    );
    let long_lived = make(max_depth);
    let mut depth = min_depth;
    while depth <= max_depth {
        let count = 1 << (max_depth + min_depth - depth);
        let mut total = 0;
        for _ in 0..count {
            total += check(&make(depth));
        }
        println!("{count}\t trees of depth {depth}\t check: {total}");
        depth += 2;
    }
    println!(
        "long lived tree of depth {max_depth}\t check: {}",
        check(&long_lived)
    );
}
