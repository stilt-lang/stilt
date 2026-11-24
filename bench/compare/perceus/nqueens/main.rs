//! nqueens: finds every way to place 13 queens on a 13 by 13 board, one row at a time, each
//! partial placement sharing the rows below it with the others that extend it, and counts them
//! (Reinking et al., Perceus, PLDI 2021).

use std::rc::Rc;

/// The columns of the queens placed so far, the last placed first.
enum Board {
    Empty,
    Queen(i64, Rc<Board>),
}

/// Whether a queen in column `queen` is safe from those of `board`, the nearest `diag` rows away.
fn safe(queen: i64, mut diag: i64, mut board: &Board) -> bool {
    while let Board::Queen(q, rest) = board {
        if queen == *q || queen == q + diag || queen == q - diag {
            return false;
        }
        diag += 1;
        board = rest;
    }
    true
}

/// Every board of `boards` with a queen added in a safe column of `n`.
fn extend(n: i64, boards: &[Rc<Board>]) -> Vec<Rc<Board>> {
    let mut next = Vec::new();
    for board in boards {
        for queen in (1..=n).rev() {
            if safe(queen, 1, board) {
                next.push(Rc::new(Board::Queen(queen, board.clone())));
            }
        }
    }
    next
}

fn queens(n: i64) -> usize {
    let mut boards = vec![Rc::new(Board::Empty)];
    for _ in 0..n {
        boards = extend(n, &boards);
    }
    boards.len()
}

pub(crate) fn main() {
    println!("{}", queens(13));
}
