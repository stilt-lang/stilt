//! rbtree-ck: rbtree, keeping a list of every fifth tree it makes, which share most of their
//! nodes, and folding over the last to count its true values (Reinking et al., Perceus, PLDI
//! 2021). The trees are persistent, their nodes shared by counted references.

use std::rc::Rc;

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

type Tree = Option<Rc<Node>>;

fn node(color: Color, left: Tree, key: i64, value: bool, right: Tree) -> Tree {
    Some(Rc::new(Node {
        color,
        left,
        key,
        value,
        right,
    }))
}

fn red(t: &Tree) -> Option<&Node> {
    t.as_deref().filter(|n| n.color == Color::Red)
}

/// Rebalances a black node whose new left child `l` is red.
fn balance_left(l: &Tree, key: i64, value: bool, right: Tree) -> Tree {
    let l = l.as_deref()?;
    if let Some(a) = red(&l.left) {
        let a = node(
            Color::Black,
            a.left.clone(),
            a.key,
            a.value,
            a.right.clone(),
        );
        let c = node(Color::Black, l.right.clone(), key, value, right);
        node(Color::Red, a, l.key, l.value, c)
    } else if let Some(b) = red(&l.right) {
        let a = node(Color::Black, l.left.clone(), l.key, l.value, b.left.clone());
        let c = node(Color::Black, b.right.clone(), key, value, right);
        node(Color::Red, a, b.key, b.value, c)
    } else {
        let l = node(Color::Red, l.left.clone(), l.key, l.value, l.right.clone());
        node(Color::Black, l, key, value, right)
    }
}

/// Rebalances a black node whose new right child `r` is red.
fn balance_right(left: Tree, key: i64, value: bool, r: &Tree) -> Tree {
    let r = r.as_deref()?;
    if let Some(a) = red(&r.left) {
        let l = node(Color::Black, left, key, value, a.left.clone());
        let c = node(
            Color::Black,
            a.right.clone(),
            r.key,
            r.value,
            r.right.clone(),
        );
        node(Color::Red, l, a.key, a.value, c)
    } else if let Some(b) = red(&r.right) {
        let l = node(Color::Black, left, key, value, r.left.clone());
        let c = node(
            Color::Black,
            b.left.clone(),
            b.key,
            b.value,
            b.right.clone(),
        );
        node(Color::Red, l, r.key, r.value, c)
    } else {
        let r = node(Color::Red, r.left.clone(), r.key, r.value, r.right.clone());
        node(Color::Black, left, key, value, r)
    }
}

fn ins(t: &Tree, key: i64, value: bool) -> Tree {
    let Some(n) = t.as_deref() else {
        return node(Color::Red, None, key, value, None);
    };
    let black = n.color == Color::Black;
    if key < n.key {
        let l = ins(&n.left, key, value);
        if black && red(&n.left).is_some() {
            balance_left(&l, n.key, n.value, n.right.clone())
        } else {
            node(n.color, l, n.key, n.value, n.right.clone())
        }
    } else if key == n.key {
        node(n.color, n.left.clone(), key, value, n.right.clone())
    } else {
        let r = ins(&n.right, key, value);
        if black && red(&n.right).is_some() {
            balance_right(n.left.clone(), n.key, n.value, &r)
        } else {
            node(n.color, n.left.clone(), n.key, n.value, r)
        }
    }
}

fn set_black(t: &Tree) -> Tree {
    let n = t.as_deref()?;
    node(
        Color::Black,
        n.left.clone(),
        n.key,
        n.value,
        n.right.clone(),
    )
}

fn insert(t: &Tree, key: i64, value: bool) -> Tree {
    if red(t).is_some() {
        set_black(&ins(t, key, value))
    } else {
        ins(t, key, value)
    }
}

fn fold<A>(t: &Tree, acc: A, f: &impl Fn(i64, bool, A) -> A) -> A {
    match t.as_deref() {
        Some(n) => fold(&n.right, f(n.key, n.value, fold(&n.left, acc, f)), f),
        None => acc,
    }
}

fn make_trees(n: i64, every: i64) -> Vec<Tree> {
    let mut trees = Vec::new();
    let mut t = None;
    for k in (1..=n).rev() {
        t = insert(&t, k, k % 10 == 0);
        if k % every == 0 {
            trees.push(t.clone());
        }
    }
    trees.push(t);
    trees
}

pub(crate) fn main() {
    let trees = make_trees(4_200_000, 5);
    let last = trees.last().cloned().flatten();
    println!(
        "{}",
        fold(&last, 0, &|_, v, count| if v { count + 1 } else { count })
    );
}
