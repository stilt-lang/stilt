(* The rules of acceptance of one body (facts.rules-of-acceptance): six shapes
   of code, each with a name, that decide what [without panic] and [without
   div] accept. The reference interpreter keeps every check, so it reads these
   rules alone. *)

open Tast
module C = Accept_code
module W = Accept_walk
module R = Accept_rules

type verdict = R.verdict = Proved of R.rule | Unproved of string
type table = (Ast.loc, (expr * verdict) list) Hashtbl.t
type t = { checks : table; loops : table; recursion : verdict option }

(* facts.terms: a constant whose value is written as an integer literal, with or
   without a [-]. *)
let constants (program : program) =
  let table = Hashtbl.create 16 in
  let add key = function
    | Code ({ desc = Int text; _ } as e) when C.is_int e.ty ->
        Hashtbl.replace table key (C.num_of_literal text)
    | Code ({ desc = Unary (Neg, { desc = Int text; _ }); _ } as e)
      when C.is_int e.ty ->
        Hashtbl.replace table key (C.negate (C.num_of_literal text))
    | _ -> ()
  in
  List.iter (fun (i, d) -> add (i, None) d) program.constants;
  List.iter (fun ((i, n), d) -> add (i, Some n) d) program.member_constants;
  fun (e : expr) ->
    match e.desc with
    | Constant i -> Hashtbl.find_opt table (i, None)
    | Member_constant (i, n, _) -> Hashtbl.find_opt table (i, Some n)
    | _ -> None

let record (table : table) (e : expr) v =
  let found = Option.value (Hashtbl.find_opt table e.loc) ~default:[] in
  Hashtbl.replace table e.loc ((e, v) :: found)

let find (table : table) (e : expr) =
  Option.bind (Hashtbl.find_opt table e.loc) (List.assq_opt e)

(* The function's [let] parameters of integer types, by their places. *)
let int_params env key params =
  let types =
    match Option.bind key (Implicit_names.signature env) with
    | Some (s : Env.fn_sig) when List.length s.params = List.length params ->
        List.map snd s.params
    | _ -> List.map (fun _ -> Types.Error) params
  in
  List.concat
    (List.mapi
       (fun i (((mode : Ast.mode), v), ty) ->
         if mode = Let && C.is_int ty then [ (i, v) ] else [])
       (List.combine params types))

let body env ~constant ~key ~params code =
  let w = Accept_visit.run env ~constant ~self:key code in
  let cx = { R.env; w; signs = Accept_signs.of_walk w } in
  let checks = Hashtbl.create 16 and loops = Hashtbl.create 4 in
  List.iter
    (fun (p : W.pending) -> Option.iter (record checks p.node) (R.verdict cx p))
    w.pending;
  List.iter
    (fun (l : W.looped) ->
      record loops l.loop
        (match Accept_loops.counting cx l with
        | Ok () -> Proved Counting_loop
        | Error need -> Unproved need))
    w.looped;
  {
    checks;
    loops;
    recursion = Accept_loops.shrinks cx (int_params env key params);
  }

(* An operation the walk never reached keeps its check. *)
let verdict table e = Option.value (find table e) ~default:(Unproved "")
let access t e = verdict t.checks e
let division t e = verdict t.checks e
let loop t e = verdict t.loops e
let shrinks t = match t.recursion with Some (Unproved _) -> false | _ -> true

let recursion_note t =
  match t.recursion with Some (Unproved note) -> Some note | _ -> None
