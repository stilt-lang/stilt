// nqueens: finds every way to place 13 queens on a 13 by 13 board, one row at a time, each partial
// placement sharing the rows below it with the others that extend it, and counts them (Reinking et
// al., Perceus, PLDI 2021).

import java.util.ArrayList;
import java.util.List;

public final class Main {
    /** A queen's column and the board below it, the queens placed before; null is the empty board. */
    record Board(int queen, Board rest) {}

    /** Whether a queen in column {@code queen} is safe from those of {@code board}. */
    static boolean safe(int queen, Board board) {
        int diag = 1;
        for (Board b = board; b != null; b = b.rest()) {
            int q = b.queen();
            if (queen == q || queen == q + diag || queen == q - diag) {
                return false;
            }
            diag++;
        }
        return true;
    }

    /** Every board of {@code boards} with a queen added in a safe column of {@code n}. */
    static List<Board> extend(int n, List<Board> boards) {
        List<Board> next = new ArrayList<>();
        for (Board board : boards) {
            for (int queen = n; queen > 0; queen--) {
                if (safe(queen, board)) {
                    next.add(new Board(queen, board));
                }
            }
        }
        return next;
    }

    static int queens(int n) {
        List<Board> boards = new ArrayList<>();
        boards.add(null);
        for (int i = 0; i < n; i++) {
            boards = extend(n, boards);
        }
        return boards.size();
    }

    public static void main(String[] args) {
        System.out.println(queens(13));
    }
}
