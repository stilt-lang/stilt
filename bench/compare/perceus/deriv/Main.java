// deriv: differentiates x^x ten times, simplifying each derivative as it is built, and prints the
// size of each (Reinking et al., Perceus, PLDI 2021).

public final class Main {
    sealed interface Expr permits Val, Var, Add, Mul, Pow, Ln {}

    record Val(int value) implements Expr {}

    record Var(String name) implements Expr {}

    record Add(Expr left, Expr right) implements Expr {}

    record Mul(Expr left, Expr right) implements Expr {}

    record Pow(Expr base, Expr exponent) implements Expr {}

    record Ln(Expr arg) implements Expr {}

    static int pown(int a, int n) {
        int r = 1;
        for (int i = 0; i < n; i++) {
            r *= a;
        }
        return r;
    }

    static Expr add(Expr a, Expr b) {
        if (a instanceof Val(var n) && b instanceof Val(var m)) return new Val(n + m);
        if (a instanceof Val(var n) && n == 0) return b;
        if (b instanceof Val(var n) && n == 0) return a;
        if (b instanceof Val(var n)) return add(new Val(n), a);
        if (a instanceof Val(var n) && b instanceof Add(Val(var m), var f)) return add(new Val(n + m), f);
        if (b instanceof Add(Val(var n), var g)) return add(new Val(n), add(a, g));
        if (a instanceof Add(var f, var g)) return add(f, add(g, b));
        return new Add(a, b);
    }

    static Expr mul(Expr a, Expr b) {
        if (a instanceof Val(var n) && b instanceof Val(var m)) return new Val(n * m);
        if (a instanceof Val(var n) && n == 0 || b instanceof Val(var m) && m == 0) return new Val(0);
        if (a instanceof Val(var n) && n == 1) return b;
        if (b instanceof Val(var n) && n == 1) return a;
        if (b instanceof Val(var n)) return mul(new Val(n), a);
        if (a instanceof Val(var n) && b instanceof Mul(Val(var m), var f)) return mul(new Val(n * m), f);
        if (b instanceof Mul(Val(var n), var g)) return mul(new Val(n), mul(a, g));
        if (a instanceof Mul(var f, var g)) return mul(f, mul(g, b));
        return new Mul(a, b);
    }

    static Expr pow(Expr a, Expr b) {
        if (a instanceof Val(var m) && b instanceof Val(var n)) return new Val(pown(m, n));
        if (b instanceof Val(var n) && n == 0) return new Val(1);
        if (b instanceof Val(var n) && n == 1) return a;
        if (a instanceof Val(var m) && m == 0) return new Val(0);
        return new Pow(a, b);
    }

    static Expr ln(Expr e) {
        return e instanceof Val(var n) && n == 1 ? new Val(0) : new Ln(e);
    }

    /** The derivative of {@code e} by {@code x}. */
    static Expr d(String x, Expr e) {
        return switch (e) {
            case Val v -> new Val(0);
            case Var(var y) -> new Val(x.equals(y) ? 1 : 0);
            case Add(var f, var g) -> add(d(x, f), d(x, g));
            case Mul(var f, var g) -> add(mul(f, d(x, g)), mul(g, d(x, f)));
            case Pow(var f, var g) ->
                mul(pow(f, g), add(mul(mul(g, d(x, f)), pow(f, new Val(-1))), mul(ln(f), d(x, g))));
            case Ln(var f) -> mul(d(x, f), pow(f, new Val(-1)));
        };
    }

    static int count(Expr e) {
        return switch (e) {
            case Val v -> 1;
            case Var v -> 1;
            case Add(var f, var g) -> count(f) + count(g);
            case Mul(var f, var g) -> count(f) + count(g);
            case Pow(var f, var g) -> count(f) + count(g);
            case Ln(var f) -> count(f);
        };
    }

    public static void main(String[] args) {
        Expr x = new Var("x");
        Expr f = pow(x, x);
        for (int i = 1; i <= 10; i++) {
            f = d("x", f);
            System.out.println(i + " count: " + count(f));
        }
        System.out.println("done");
    }
}
