(* Random choices. Every choice draws from one state, so a seed fixes the whole
   program. *)

type t = Random.State.t

let make seed = Random.State.make [| seed |]

(* An integer from 0 to [n - 1]. *)
let below r n = Random.State.int r n

(* An integer from [lo] to [hi], both included. *)
let between r lo hi = lo + below r (hi - lo + 1)

(* [true] with probability [p]. *)
let chance r p = Random.State.float r 1.0 < p
let one r xs = List.nth xs (below r (List.length xs))

(* One of the choices, each as likely as its weight. Choices of weight 0 are
   never taken, and at least one weight must be positive. *)
let weighted r choices =
  let total = List.fold_left (fun sum (w, _) -> sum + w) 0 choices in
  let rec go n = function
    | (w, x) :: rest -> if n < w then x else go (n - w) rest
    | [] -> invalid_arg "Pick.weighted"
  in
  go (below r total) choices

(* [n] values made by [f], in order. *)
let times n f = List.init n (fun _ -> f ())
let bits64 r = Random.State.bits64 r

(* Runs one of the thunks, each as likely as its weight. *)
let run r choices = weighted r choices ()
