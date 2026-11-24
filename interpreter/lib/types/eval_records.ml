(* Records and tuples: literals, reads of their fields and elements, updates
   (records.anonymous-literals and records.update), and the values that spreads stand for (variadics.spread-expressions). Each takes the evaluator of expressions, [expr]. *)

open Tast
open Value
open Eval_state
open Eval_types
module T = Types

type eval = Eval_state.t -> Eval_state.frame -> Tast.expr -> Value.value

let field v f =
  match v with
  | Record (_, fields) -> List.assoc f fields
  | _ -> invalid_arg "Eval_records.field"

let tuple_field v i =
  match v with
  | Tuple xs -> List.nth xs i
  | _ -> invalid_arg "Eval_records.tuple_field"

(* Evaluated as written, stored as declared: a declared record's fields in
   its declaration's order, an anonymous record's in the alphabetical order
   of their names (records.field-order). *)
let record ~expr t fr item fields =
  let given =
    List.fold_left (fun given (f, x) -> given @ [ (f, expr t fr x) ]) [] fields
  in
  let declared =
    if item = T.anonymous then List.sort String.compare (List.map fst given)
    else
      match Env.type_info t.env item with
      | Some { def = Record declared; _ } -> List.map fst declared
      | _ -> invalid_arg "Eval_records.record"
  in
  Record (item, List.map (fun f -> (f, List.assoc f given)) declared)

(* records.update-fields: the base, then the fields in written order, which replace
   the base's own. *)
let update ~expr t fr base fields =
  let b = expr t fr base in
  let given =
    List.fold_left (fun given (f, x) -> given @ [ (f, expr t fr x) ]) [] fields
  in
  match b with
  | Record (item, own) ->
      Record
        ( item,
          List.map
            (fun (f, v) ->
              (f, Option.value (List.assoc_opt f given) ~default:v))
            own )
  | _ -> invalid_arg "Eval_records.update"

(* variadics.spread-expressions: the values of a spread, its body evaluated once for each
   element of its pack, from the first to the last, with each pack tuple it
   names bound to its element there, and the pack to that element's type. *)
let spread ~expr t fr (s : spread) =
  let pack =
    match s.pack with Param v -> v | _ -> invalid_arg "Eval_records.spread"
  in
  let elements =
    match T.resolve (concrete fr s.pack) with
    | Tuple es -> es
    | _ -> invalid_arg "Eval_records.spread"
  in
  let tuples =
    List.map
      (fun (v : Hir.var) ->
        match Hashtbl.find fr.locals v.id with
        | Tuple xs -> (v, Tuple xs, xs)
        | _ -> invalid_arg "Eval_records.spread")
      s.tuples
  in
  let one i ty =
    List.iter
      (fun ((v : Hir.var), _, xs) ->
        Hashtbl.replace fr.locals v.id (List.nth xs i))
      tuples;
    expr t { fr with tenv = (pack, ty) :: fr.tenv } s.body
  in
  Fun.protect
    ~finally:(fun () ->
      List.iter
        (fun ((v : Hir.var), whole, _) -> Hashtbl.replace fr.locals v.id whole)
        tuples)
    (fun () ->
      List.rev
        (snd
           (List.fold_left
              (fun (i, values) ty -> (i + 1, one i ty :: values))
              (0, []) elements)))

(* The values of a tuple's or a list's elements, a spread's in its place. *)
let elements ~expr t fr es =
  List.concat_map
    (fun (e : Tast.expr) ->
      match e.desc with Spread s -> spread ~expr t fr s | _ -> [ expr t fr e ])
    es
