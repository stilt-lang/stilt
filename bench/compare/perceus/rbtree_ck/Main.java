// rbtree-ck: rbtree, keeping a list of every fifth tree it makes, which share most of their nodes,
// and folding over the last to count its true values (Reinking et al., Perceus, PLDI 2021).

import java.util.ArrayList;
import java.util.List;

public final class Main {
    enum Color { RED, BLACK }

    sealed interface Tree permits Leaf, Node {}

    record Leaf() implements Tree {}

    record Node(Color color, Tree left, int key, boolean value, Tree right) implements Tree {}

    interface Step<A> {
        A apply(int key, boolean value, A acc);
    }

    static final Tree LEAF = new Leaf();

    static boolean isRed(Tree t) {
        return t instanceof Node n && n.color() == Color.RED;
    }

    /** Rebalances a black node whose left child {@code l} is red. */
    static Tree balanceLeft(Tree l, int k, boolean v, Tree r) {
        return switch (l) {
            case Node(var c, Node(var red, var a, var ka, var va, var b), var kb, var vb, var d)
                    when red == Color.RED ->
                new Node(Color.RED, new Node(Color.BLACK, a, ka, va, b), kb, vb, new Node(Color.BLACK, d, k, v, r));
            case Node(var c, var a, var ka, var va, Node(var red, var b, var kb, var vb, var d))
                    when red == Color.RED ->
                new Node(Color.RED, new Node(Color.BLACK, a, ka, va, b), kb, vb, new Node(Color.BLACK, d, k, v, r));
            case Node(var c, var a, var ka, var va, var b) ->
                new Node(Color.BLACK, new Node(Color.RED, a, ka, va, b), k, v, r);
            case Leaf leaf -> leaf;
        };
    }

    /** Rebalances a black node whose right child {@code r} is red. */
    static Tree balanceRight(Tree l, int k, boolean v, Tree r) {
        return switch (r) {
            case Node(var c, Node(var red, var a, var ka, var va, var b), var kb, var vb, var d)
                    when red == Color.RED ->
                new Node(Color.RED, new Node(Color.BLACK, l, k, v, a), ka, va, new Node(Color.BLACK, b, kb, vb, d));
            case Node(var c, var a, var ka, var va, Node(var red, var b, var kb, var vb, var d))
                    when red == Color.RED ->
                new Node(Color.RED, new Node(Color.BLACK, l, k, v, a), ka, va, new Node(Color.BLACK, b, kb, vb, d));
            case Node(var c, var a, var ka, var va, var b) ->
                new Node(Color.BLACK, l, k, v, new Node(Color.RED, a, ka, va, b));
            case Leaf leaf -> leaf;
        };
    }

    static Tree ins(Tree t, int k, boolean v) {
        return switch (t) {
            case Leaf leaf -> new Node(Color.RED, leaf, k, v, leaf);
            case Node(var color, var l, var kx, var vx, var r) when color == Color.RED ->
                k < kx ? new Node(Color.RED, ins(l, k, v), kx, vx, r)
                    : k == kx ? new Node(Color.RED, l, k, v, r)
                    : new Node(Color.RED, l, kx, vx, ins(r, k, v));
            case Node(var color, var l, var kx, var vx, var r) -> {
                if (k < kx) {
                    yield isRed(l) ? balanceLeft(ins(l, k, v), kx, vx, r) : new Node(Color.BLACK, ins(l, k, v), kx, vx, r);
                } else if (k == kx) {
                    yield new Node(Color.BLACK, l, k, v, r);
                }
                yield isRed(r) ? balanceRight(l, kx, vx, ins(r, k, v)) : new Node(Color.BLACK, l, kx, vx, ins(r, k, v));
            }
        };
    }

    static Tree setBlack(Tree t) {
        return t instanceof Node(var c, var l, var k, var v, var r) ? new Node(Color.BLACK, l, k, v, r) : LEAF;
    }

    static Tree insert(Tree t, int k, boolean v) {
        return isRed(t) ? setBlack(ins(t, k, v)) : ins(t, k, v);
    }

    static <A> A fold(Tree t, A acc, Step<A> f) {
        return switch (t) {
            case Leaf leaf -> acc;
            case Node(var c, var l, var k, var v, var r) -> fold(r, f.apply(k, v, fold(l, acc, f)), f);
        };
    }

    static List<Tree> makeTrees(int n, int every) {
        List<Tree> trees = new ArrayList<>();
        Tree t = LEAF;
        for (int k = n; k > 0; k--) {
            t = insert(t, k, k % 10 == 0);
            if (k % every == 0) {
                trees.add(t);
            }
        }
        trees.add(t);
        return trees;
    }

    public static void main(String[] args) {
        List<Tree> trees = makeTrees(4_200_000, 5);
        Step<Integer> count = (key, value, total) -> value ? total + 1 : total;
        System.out.println(fold(trees.get(trees.size() - 1), 0, count));
    }
}
