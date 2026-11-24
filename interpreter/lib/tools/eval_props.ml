(* tests.property-cases, tests.running-cases, tests.shrinking and tests.property-verdict. *)

open Value
open Eval_state
module P = Prop_types

type failure = False | Raise of string | Panic of string * string

type failed = {
  case : int;
  counterexample : string list;
  failure : failure;
  shrinks : int;
}

type verdict = { seed : int64; cases : int; failed : failed option }

let cases = 100

(* tests.shrinking: a run fails in the same way when it returns [false] where the case
   did, raises where it raised, or panics with the same kind. *)
let same a b =
  match (a, b) with
  | False, False | Raise _, Raise _ -> true
  | Panic (k, _), Panic (l, _) -> k = l
  | _ -> false

let run t fr (p : Tast.property) (closure : Tast.expr) =
  let params, error =
    match closure.ty with
    | Fn (params, _, row) -> (List.map snd params, row.raise)
    | _ -> invalid_arg "Eval_props.run"
  in
  let g, nodes =
    match P.build t.env params with
    | Ok built -> built
    | Error _ -> invalid_arg "Eval_props.run"
  in
  let loc = p.loc in
  let insert kty d k v = Eval_traits.insert t fr loc kty d k v in
  let f =
    match Eval_exprs.expr t fr closure with
    | Fn (Closure c) -> c
    | _ -> invalid_arg "Eval_props.run"
  in
  (* tests.running-cases. *)
  let attempt values =
    match t.apply t fr loc (Closure_body f) (Array.of_list values) with
    | Bool true -> None
    | _ -> Some False
    | exception Raised e -> (
        (* The raised value is shown by the run, whose panic it may be. *)
        let ty = Option.value error ~default:Types.never in
        match Eval_traits.show t fr loc "show" ty e with
        | shown -> Some (Raise shown)
        | exception Panicked { kind; detail; _ } -> Some (Panic (kind, detail)))
    | exception Panicked { kind; detail; _ } -> Some (Panic (kind, detail))
  in
  let seed = Prop_rand.seed p.text in
  let rec case i =
    if i = cases then { seed; cases; failed = None }
    else
      let values = Prop_gen.case insert g ~seed nodes i in
      match attempt values with
      | None -> case (i + 1)
      | Some failure ->
          let shrunk =
            Prop_shrink.shrink
              ~candidates:(fun j ->
                Prop_shrink.candidates insert g (List.nth nodes j))
              ~run:attempt ~same values failure
          in
          let counterexample =
            List.map2 (Prop_show.show g) nodes shrunk.values
          in
          let failed =
            {
              case = i;
              counterexample;
              failure = shrunk.failure;
              shrinks = shrunk.shrinks;
            }
          in
          { seed; cases = i + 1; failed = Some failed }
  in
  case 0

let json v =
  let failed =
    match v.failed with
    | None -> []
    | Some f ->
        let failure, detail =
          match f.failure with
          | False -> ("false", [])
          | Raise d -> ("raise", [ d ])
          | Panic (k, d) -> ("panic: " ^ k, [ d ])
        in
        [
          Printf.sprintf {|"case": %d|} f.case;
          Printf.sprintf {|"counterexample": [%s]|}
            (String.concat ", " (List.map Json.string f.counterexample));
          Printf.sprintf {|"failure": %s|} (Json.string failure);
        ]
        @ List.map
            (fun d -> Printf.sprintf {|"detail": %s|} (Json.string d))
            detail
        @ [ Printf.sprintf {|"shrinks": %d|} f.shrinks ]
  in
  "{"
  ^ String.concat ", "
      ([
         Printf.sprintf {|"seed": "%016Lx"|} v.seed;
         Printf.sprintf {|"cases": %d|} v.cases;
       ]
      @ failed)
  ^ "}"
