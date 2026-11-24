(* Iterators (views.making-iterator, views.adapters, views.laziness and views.consumers): an iterator is a description of its
   source and adapters, which a consumer turns into a cursor each time it
   reads it, so that nothing runs before a consumer asks and every consumer
   starts from the first element (views.laziness). *)

open Value
open Eval_state
open Eval_operators
open Eval_targets

(* Each step of a cursor asks for one element. *)
type cursor = unit -> value option

let elements xs : cursor =
  let rest = ref xs in
  fun () ->
    match !rest with
    | [] -> None
    | x :: more ->
        rest := more;
        Some x

let range first last : cursor =
  let i = ref first in
  fun () ->
    if !i < last then (
      let x = !i in
      i := Int64.succ x;
      Some (Int x))
    else None

(* [take(n)] asks for no element after its [n]th, and [take_while] for none
   after the first its closure rejects (views.laziness). *)
let taken n (next : cursor) : cursor =
  let given = ref 0L in
  fun () ->
    if !given >= n then None
    else
      match next () with
      | Some x ->
          given := Int64.succ !given;
          Some x
      | None ->
          given := n;
          None

let taken_while keep (next : cursor) : cursor =
  let over = ref false in
  fun () ->
    if !over then None
    else
      match next () with
      | Some x when keep x -> Some x
      | Some _ | None ->
          over := true;
          None

(* [skip] and [skip_while] ask and drop, when they are first asked. *)
let skipped n (next : cursor) : cursor =
  let skipping = ref true in
  fun () ->
    if !skipping then (
      skipping := false;
      let rec drop i =
        i >= n || (Option.is_some (next ()) && drop (Int64.succ i))
      in
      if drop 0L then next () else None)
    else next ()

let skipped_while drop (next : cursor) : cursor =
  let skipping = ref true in
  let rec ask () =
    match next () with
    | Some x when !skipping && drop x -> ask ()
    | found ->
        skipping := false;
        found
  in
  ask

let enumerated start (next : cursor) : cursor =
  let i = ref start in
  fun () ->
    Option.map
      (fun x ->
        let index = !i in
        (* An index past [i64]'s range overflows, as [List.enumerate]'s
           does. *)
        i := Ints.add { bits = 64; signed = true } index 1L;
        Tuple [ Int index; x ])
      (next ())

(* [zip] asks [self] and then [other] for each pair, and ends with the first
   that ends; [chain] asks [other] once [self] ends (views.laziness). *)
let zipped (first : cursor) (second : cursor) : cursor =
 fun () ->
  match first () with
  | None -> None
  | Some x -> Option.map (fun y -> Tuple [ x; y ]) (second ())

let chained (first : cursor) (second : cursor) : cursor =
  let second_now = ref false in
  fun () ->
    if !second_now then second ()
    else
      match first () with
      | Some x -> Some x
      | None ->
          second_now := true;
          second ()

(* A cursor over [it], whose adapters call their closures from the call at
   [loc], each on an element as it reaches the adapter (views.laziness). *)
let rec cursor t fr loc it : cursor =
  let call f x = t.apply t fr loc (target_of_fn t f) [| x |] in
  let holds f x = truth (call f x) in
  let inner it = cursor t fr loc it in
  match it with
  | Elements xs -> elements xs
  | Range (first, last) -> range first last
  | Mapped (it, f) ->
      let next = inner it in
      fun () -> Option.map (call f) (next ())
  | Filtered (it, keep) ->
      let next = inner it in
      let rec ask () =
        match next () with Some x when not (holds keep x) -> ask () | r -> r
      in
      ask
  | Taken (it, n) -> taken n (inner it)
  | Skipped (it, n) -> skipped n (inner it)
  | Taken_while (it, keep) -> taken_while (holds keep) (inner it)
  | Skipped_while (it, drop) -> skipped_while (holds drop) (inner it)
  | Enumerated (it, start) -> enumerated start (inner it)
  | Zipped (a, b) ->
      let first = inner a in
      zipped first (inner b)
  | Chained (a, b) ->
      let first = inner a in
      chained first (inner b)

(* [each x] runs for each element in turn, until it gives [false], as a [for]
   loop's body does (views.for-over-view). *)
let iterate t fr loc it each =
  let next = cursor t fr loc it in
  let rec go () =
    match next () with Some x -> if each x then go () | None -> ()
  in
  go ()

(* Reads elements until [stop] gives a result, and gives [finish ()] if the
   iterator ends first. *)
let read_until t fr loc it stop finish =
  let next = cursor t fr loc it in
  let rec go () =
    match next () with
    | None -> finish ()
    | Some x -> ( match stop x with Some r -> r | None -> go ())
  in
  go ()

(* The greatest or least element, the first of equal ones (views.consumers). [better
   c] tells whether an element that compares [c] with the best so far takes
   its place. *)
let extreme t fr loc ty it better =
  let best = ref None in
  read_until t fr loc it
    (fun x ->
      (match !best with
      | Some b when not (better (Eval_traits.order t fr loc ty x b)) -> ()
      | _ -> best := Some x);
      None)
    (fun () -> option !best)

(* Every element, the last first. *)
let until_end t fr loc it =
  let seen = ref [] in
  read_until t fr loc it
    (fun x ->
      seen := x :: !seen;
      None)
    (fun () -> !seen)

(* The consumers of views.consumers, each of which reads the elements it needs, in
   order, and calls its callback as it reads them. *)
let consume t fr loc name targs it args =
  let call i xs =
    match args.(i) with
    | Fn f -> t.apply t fr loc (target_of_fn t f) xs
    | _ -> invalid_arg "Eval_iters.consume"
  in
  let until stop finish = read_until t fr loc it stop finish in
  let found x = Some (some x) in
  let accepted x = truth (call 1 [| x |]) in
  match (name, args) with
  | "collect", _ -> List (Vec.of_list (List.rev (until_end t fr loc it)))
  | "fold", _ ->
      let acc = ref args.(1) in
      until
        (fun x ->
          acc := call 2 [| !acc; x |];
          None)
        (fun () -> !acc)
  | "count", _ -> Int (Int64.of_int (List.length (until_end t fr loc it)))
  | "any", _ ->
      until
        (fun x -> if accepted x then Some (Bool true) else None)
        (fun () -> Bool false)
  | "all", _ ->
      until
        (fun x -> if accepted x then None else Some (Bool false))
        (fun () -> Bool true)
  | "find", _ ->
      until (fun x -> if accepted x then found x else None) (fun () -> none)
  | "first", _ -> until found (fun () -> none)
  | "last", _ -> option (List.nth_opt (until_end t fr loc it) 0)
  | "nth", [| _; Int n |] when n < 0L -> none
  | "nth", [| _; Int n |] ->
      let i = ref 0L in
      until
        (fun x ->
          if !i = n then found x
          else (
            i := Int64.succ !i;
            None))
        (fun () -> none)
  | "max", _ -> extreme t fr loc (List.hd targs) it (fun c -> c > 0)
  | "min", _ -> extreme t fr loc (List.hd targs) it (fun c -> c < 0)
  | _ -> invalid_arg ("Eval_iters.consume: " ^ name)
