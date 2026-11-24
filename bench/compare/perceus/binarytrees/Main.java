// binarytrees: builds perfect binary trees bottom-up and counts their nodes, from a stretch tree of
// depth 22 down to trees of depth 4, while one of depth 21 lives throughout, as the Benchmarks
// Game's program does, on one thread (Reinking et al., Perceus, PLDI 2021).

public final class Main {
    /** A node and its subtrees; null is a tip. */
    record Node(Node left, Node right) {}

    static Node make(int depth) {
        return depth > 0 ? new Node(make(depth - 1), make(depth - 1)) : new Node(null, null);
    }

    static int check(Node t) {
        return t == null ? 0 : check(t.left()) + check(t.right()) + 1;
    }

    public static void main(String[] args) {
        int minDepth = 4;
        int maxDepth = 21;
        int stretch = maxDepth + 1;
        System.out.println("stretch tree of depth " + stretch + "\t check: " + check(make(stretch)));
        Node longLived = make(maxDepth);
        for (int depth = minDepth; depth <= maxDepth; depth += 2) {
            int count = 1 << (maxDepth + minDepth - depth);
            int total = 0;
            for (int i = 0; i < count; i++) {
                total += check(make(depth));
            }
            System.out.println(count + "\t trees of depth " + depth + "\t check: " + total);
        }
        System.out.println("long lived tree of depth " + maxDepth + "\t check: " + check(longLived));
    }
}
