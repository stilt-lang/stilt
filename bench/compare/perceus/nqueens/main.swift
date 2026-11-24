// nqueens: finds every way to place 13 queens on a 13 by 13 board, one row at a time, each partial
// placement sharing the rows below it with the others that extend it, and counts them (Reinking et
// al., Perceus, PLDI 2021).

/// The columns of the queens placed so far, the last placed first.
indirect enum Board {
    case empty
    case queen(Int, Board)
}

/// Whether a queen in column `queen` is safe from those of `board`, the nearest `diag` rows away.
func safe(_ queen: Int, _ board: Board) -> Bool {
    var diag = 1
    var rest = board
    while case let .queen(q, next) = rest {
        if queen == q || queen == q + diag || queen == q - diag { return false }
        diag += 1
        rest = next
    }
    return true
}

/// Every board of `boards` with a queen added in a safe column of `n`.
func extend(_ n: Int, _ boards: [Board]) -> [Board] {
    var next: [Board] = []
    for board in boards {
        for queen in stride(from: n, through: 1, by: -1) where safe(queen, board) {
            next.append(.queen(queen, board))
        }
    }
    return next
}

func queens(_ n: Int) -> Int {
    var boards: [Board] = [.empty]
    for _ in 0..<n { boards = extend(n, boards) }
    return boards.count
}

print(queens(13))
