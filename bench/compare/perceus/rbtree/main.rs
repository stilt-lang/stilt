//! rbtree: inserts 4,200,000 keys into a red-black tree, the value of every tenth true, and folds
//! over the tree to count the true values (Reinking et al., Perceus, PLDI 2021). Each insertion
//! owns the tree, so it rebuilds the path to the new key in the nodes it takes apart.

#[derive(Clone, Copy, PartialEq, Eq)]
enum Color {
    Red,
    Black,
}

struct Node {
    color: Color,
    left: Tree,
    key: i64,
    value: bool,
    right: Tree,
}

type Tree = Option<Box<Node>>;

fn node(color: Color, left: Tree, key: i64, value: bool, right: Tree) -> Box<Node> {
    Box::new(Node {
        color,
        left,
        key,
        value,
        right,
    })
}

fn is_red(t: &Tree) -> bool {
    matches!(t, Some(n) if n.color == Color::Red)
}

/// Rebalances a black node whose left child `l` is red.
fn balance_left(mut l: Box<Node>, key: i64, value: bool, right: Tree) -> Box<Node> {
    if is_red(&l.left) {
        if let Some(a) = l.left.as_mut() {
            a.color = Color::Black;
        }
        l.color = Color::Red;
        l.right = Some(node(Color::Black, l.right.take(), key, value, right));
        l
    } else if is_red(&l.right) {
        let mut b = l.right.take().expect("a red node");
        l.color = Color::Black;
        l.right = b.left.take();
        b.color = Color::Red;
        b.left = Some(l);
        b.right = Some(node(Color::Black, b.right.take(), key, value, right));
        b
    } else {
        l.color = Color::Red;
        node(Color::Black, Some(l), key, value, right)
    }
}

/// Rebalances a black node whose right child `r` is red.
fn balance_right(left: Tree, key: i64, value: bool, mut r: Box<Node>) -> Box<Node> {
    if is_red(&r.left) {
        let mut a = r.left.take().expect("a red node");
        r.color = Color::Black;
        r.left = a.right.take();
        a.color = Color::Red;
        a.right = Some(r);
        a.left = Some(node(Color::Black, left, key, value, a.left.take()));
        a
    } else if is_red(&r.right) {
        if let Some(b) = r.right.as_mut() {
            b.color = Color::Black;
        }
        r.color = Color::Red;
        r.left = Some(node(Color::Black, left, key, value, r.left.take()));
        r
    } else {
        r.color = Color::Red;
        node(Color::Black, left, key, value, Some(r))
    }
}

fn ins(t: Tree, key: i64, value: bool) -> Box<Node> {
    let Some(mut n) = t else {
        return node(Color::Red, None, key, value, None);
    };
    if key < n.key {
        if n.color == Color::Black && is_red(&n.left) {
            let l = ins(n.left.take(), key, value);
            return balance_left(l, n.key, n.value, n.right.take());
        }
        n.left = Some(ins(n.left.take(), key, value));
    } else if key > n.key {
        if n.color == Color::Black && is_red(&n.right) {
            let r = ins(n.right.take(), key, value);
            return balance_right(n.left.take(), n.key, n.value, r);
        }
        n.right = Some(ins(n.right.take(), key, value));
    } else {
        n.value = value;
    }
    n
}

fn insert(t: Tree, key: i64, value: bool) -> Tree {
    let mut n = ins(t, key, value);
    n.color = Color::Black;
    Some(n)
}

fn fold<A>(t: &Tree, acc: A, f: &impl Fn(i64, bool, A) -> A) -> A {
    match t {
        Some(n) => fold(&n.right, f(n.key, n.value, fold(&n.left, acc, f)), f),
        None => acc,
    }
}

fn make_tree(n: i64) -> Tree {
    let mut t = None;
    for k in (0..n).rev() {
        t = insert(t, k, k % 10 == 0);
    }
    t
}

pub(crate) fn main() {
    let t = make_tree(4_200_000);
    println!(
        "{}",
        fold(&t, 0, &|_, v, count| if v { count + 1 } else { count })
    );
}
