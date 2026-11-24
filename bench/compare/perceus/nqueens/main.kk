// nqueens: finds every way to place 13 queens on a 13 by 13 board, one row at a time, each partial
// placement sharing the rows below it with the others that extend it, and counts them (Reinking et
// al., Perceus, PLDI 2021). A board is the columns of its queens, the last placed first, in 32-bit
// integers, as the paper's program has them.
import std/num/int32

// Whether a queen in column `queen` is safe from those of `board`, the nearest `diag` rows away.
fun safe(queen : int32, diag : int32, ^board : list<int32>) : bool
  match board
    Cons(q, rest) -> queen != q && queen != q + diag && queen != q - diag && safe(queen, diag.inc, rest)
    Nil -> True

fun place(board : list<int32>, queen : int32, next : list<list<int32>>) : div list<list<int32>>
  if queen <= zero then next
  elif safe(queen, one, board) then place(board, queen.dec, Cons(Cons(queen, board), next))
  else place(board, queen.dec, next)

// Every board of `boards` with a queen added in a safe column of `n`, before `next`.
fun extend(n : int32, boards : list<list<int32>>, next : list<list<int32>>) : div list<list<int32>>
  match boards
    Cons(board, rest) -> extend(n, rest, place(board, n, next))
    Nil -> next

fun rows(n : int32, i : int, boards : list<list<int32>>) : div list<list<int32>>
  if i == 0 then boards else rows(n, i - 1, extend(n, boards, []))

pub fun main()
  println(rows(13.int32, 13, [[]]).length)
