(* nqueens: finds every way to place 13 queens on a 13 by 13 board, one row at a time, each partial
   placement sharing the rows below it with the others that extend it, and counts them (Reinking et
   al., Perceus, PLDI 2021). A board is the columns of its queens, the last placed first. *)

(* Whether a queen in column [queen] is safe from those of a board, the nearest [diag] rows away. *)
let rec safe queen diag = function
  | [] -> true
  | q :: rest ->
      queen <> q
      && queen <> q + diag
      && queen <> q - diag
      && safe queen (diag + 1) rest

(* Every board of [boards] with a queen added in a safe column of [n]. *)
let extend n boards =
  let rec place board queen next =
    if queen <= 0 then next
    else
      place board (queen - 1)
        (if safe queen 1 board then (queen :: board) :: next else next)
  in
  List.fold_left (fun next board -> place board n next) [] boards

let queens n =
  let rec go i boards =
    if i = 0 then boards else go (i - 1) (extend n boards)
  in
  List.length (go n [ [] ])

let () = Printf.printf "%d\n" (queens 13)
