// cfold: builds an expression of 2^20 sums, reassociates it into a chain and folds its constants,
// then evaluates it before and after (Reinking et al., Perceus, PLDI 2021).

public final class Main {
    sealed interface Expr permits Var, Val, Add, Mul {}

    record Var(int name) implements Expr {}

    record Val(int value) implements Expr {}

    record Add(Expr left, Expr right) implements Expr {}

    record Mul(Expr left, Expr right) implements Expr {}

    static Expr make(int n, int v) {
        if (n == 0) {
            return v == 0 ? new Var(1) : new Val(v);
        }
        return new Add(make(n - 1, v + 1), make(n - 1, Math.max(v - 1, 0)));
    }

    static Expr appendAdd(Expr a, Expr b) {
        return a instanceof Add(var x, var y) ? new Add(x, appendAdd(y, b)) : new Add(a, b);
    }

    static Expr appendMul(Expr a, Expr b) {
        return a instanceof Mul(var x, var y) ? new Mul(x, appendMul(y, b)) : new Mul(a, b);
    }

    static Expr reassoc(Expr e) {
        return switch (e) {
            case Add(var a, var b) -> appendAdd(reassoc(a), reassoc(b));
            case Mul(var a, var b) -> appendMul(reassoc(a), reassoc(b));
            default -> e;
        };
    }

    static Expr fold(Expr e) {
        return switch (e) {
            case Add(var a, var b) -> {
                Expr x = fold(a);
                Expr y = fold(b);
                if (x instanceof Val(var p)) {
                    if (y instanceof Val(var q)) yield new Val(p + q);
                    if (y instanceof Add(var f, Val(var q))) yield new Add(new Val(p + q), f);
                    if (y instanceof Add(Val(var q), var f)) yield new Add(new Val(p + q), f);
                }
                yield new Add(x, y);
            }
            case Mul(var a, var b) -> {
                Expr x = fold(a);
                Expr y = fold(b);
                if (x instanceof Val(var p)) {
                    if (y instanceof Val(var q)) yield new Val(p * q);
                    if (y instanceof Mul(var f, Val(var q))) yield new Mul(new Val(p * q), f);
                    if (y instanceof Mul(Val(var q), var f)) yield new Mul(new Val(p * q), f);
                }
                yield new Mul(x, y);
            }
            default -> e;
        };
    }

    static int eval(Expr e) {
        return switch (e) {
            case Var v -> 0;
            case Val(var v) -> v;
            case Add(var a, var b) -> eval(a) + eval(b);
            case Mul(var a, var b) -> eval(a) * eval(b);
        };
    }

    public static void main(String[] args) {
        Expr e = make(20, 1);
        System.out.println(eval(e));
        System.out.println(eval(fold(reassoc(e))));
    }
}
