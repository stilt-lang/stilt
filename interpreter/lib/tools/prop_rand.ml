(* tests.seeds and tests.draws. *)

let seed text =
  let h = ref 0xcbf29ce484222325L in
  String.iter
    (fun c ->
      h :=
        Int64.mul (Int64.logxor !h (Int64.of_int (Char.code c))) 0x100000001b3L)
    text;
  !h

type t = { mutable state : int64 }

let create seed i = { state = Int64.add seed (Int64.of_int i) }

let next g =
  g.state <- Int64.add g.state 0x9e3779b97f4a7c15L;
  let mix z shift k =
    Int64.mul (Int64.logxor z (Int64.shift_right_logical z shift)) k
  in
  let z = mix g.state 30 0xbf58476d1ce4e5b9L in
  let z = mix z 27 0x94d049bb133111ebL in
  Int64.logxor z (Int64.shift_right_logical z 31)

let below g n = Int64.unsigned_rem (next g) n
let below_int g n = Int64.to_int (below g (Int64.of_int n))
