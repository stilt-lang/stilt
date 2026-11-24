(* Statements that change variables in scope: assignments, changes to a field,
   a list or a map, and calls that pass variables [inout]. *)

open Code
open Context
open Ty
open Expr

let compound_assign b sc ~depth v =
  let r = b.p.r in
  let e = expr b sc ~depth:(depth - 1) ~known:false v.ty in
  let op =
    match v.ty with
    | Int _ -> Pick.one r [ "+%="; "-%="; "*%="; "&="; "|="; "^=" ]
    | _ -> Pick.one r [ "+="; "-="; "*="; "/=" ]
  in
  line (v.name ^ " " ^ op ^ " " ^ e.text)

let field_assign b sc ~depth v =
  let r = b.p.r in
  let field, ty =
    match v.ty with
    | Tuple ts ->
        let i = Pick.below r (List.length ts) in
        (string_of_int i, List.nth ts i)
    | Named name -> (
        match decl b name with
        | Record fields -> Pick.one r fields
        | Variants _ -> invalid_arg "Changes.field_assign")
    | _ -> invalid_arg "Changes.field_assign"
  in
  let e = expr b (without [ v.name ] sc) ~depth:(depth - 1) ~known:false ty in
  line (v.name ^ "." ^ field ^ " = " ^ e.text)

(* A change to a list through a method that takes [inout self]. The
   arguments don't read the list, which the call changes (modes.overlap). *)
let list_change b sc ~depth v =
  let r = b.p.r in
  let t =
    match v.ty with List t -> t | _ -> invalid_arg "Changes.list_change"
  in
  let others = without [ v.name ] sc in
  let item () = (expr b others ~depth:(depth - 1) ~known:false t).text in
  Pick.run r
    [
      (4, fun () -> line (v.name ^ ".push(" ^ item () ^ ")"));
      (1, fun () -> line (v.name ^ ".insert(0, " ^ item () ^ ")"));
      (1, fun () -> line ("let _ = " ^ v.name ^ ".pop()"));
      ( 1,
        fun () ->
          line
            (v.name ^ ".retain("
            ^ closure b others ~depth:(depth - 1) t Bool
            ^ ")") );
      ( 1,
        fun () ->
          line
            (Printf.sprintf "if %s.len() > 0 { %s[0] = %s }" v.name v.name
               (item ())) );
    ]

let map_change b sc ~depth v =
  let r = b.p.r in
  let k, t =
    match v.ty with
    | Map (k, t) -> (k, t)
    | _ -> invalid_arg "Changes.map_change"
  in
  let others = without [ v.name ] sc in
  let key = (expr b others ~depth:(depth - 1) ~known:false k).text in
  let item () = (expr b others ~depth:(depth - 1) ~known:false t).text in
  Pick.run r
    [
      (3, fun () -> line (Printf.sprintf "%s[%s] = %s" v.name key (item ())));
      ( 1,
        fun () -> line (Printf.sprintf "%s.insert(%s, %s)" v.name key (item ()))
      );
      (1, fun () -> line (Printf.sprintf "let _ = %s.remove(%s)" v.name key));
    ]

(* Distinct changeable variables for the [inout] parameters of [f], in
   order, or [None] if the scope lacks them. *)
let inout_args sc f =
  let rec pick used = function
    | [] -> Some []
    | (true, t) :: rest -> (
        match
          List.find_opt
            (fun v -> v.ty = t && not (List.mem v.name used))
            (changeable sc)
        with
        | Some v ->
            Option.map (fun vs -> Some v :: vs) (pick (v.name :: used) rest)
        | None -> None)
    | (false, _) :: rest -> Option.map (fun vs -> None :: vs) (pick used rest)
  in
  pick [] f.params

(* A call that passes [inout] arguments, as a statement. Its other arguments
   don't read the variables passed [inout] (modes.law). *)
let inout_call b sc ~depth f =
  spend b sc f.cost;
  let slots = Option.get (inout_args sc f) in
  let passed = List.filter_map (Option.map (fun v -> v.name)) slots in
  let others = without passed sc in
  let args =
    List.map2
      (fun slot (_, t) ->
        match slot with
        | Some v -> "inout " ^ v.name
        | None -> (expr b others ~depth:(depth - 1) ~known:false t).text)
      slots f.params
  in
  let text = call_text f.fname args in
  let marked =
    if not f.raises then text
    else if sc.may_raise then "try " ^ text
    else "try " ^ text ^ " catch " ^ handler b others ~depth f.ret
  in
  line (if f.ret = Unit then marked else "let _ = " ^ marked)

(* The statements that change a variable in scope, each with its weight and
   the scope after it, which is [sc]. *)
let changes b sc ~depth =
  let r = b.p.r in
  let changeable = changeable sc in
  let where test = List.filter (fun v -> test v.ty) changeable in
  let lists = where (function List _ -> true | _ -> false) in
  let maps = where (function Map _ -> true | _ -> false) in
  let numbers = where (function Int _ | Float _ -> true | _ -> false) in
  let records =
    where (function
      | Tuple _ -> true
      | Named name -> (
          match decl b name with Record _ -> true | Variants _ -> false)
      | _ -> false)
  in
  let inout_calls =
    List.filter
      (fun f ->
        List.exists fst f.params && affordable b sc f.cost
        && inout_args sc f <> None)
      b.p.fns
  in
  [
    ( (if changeable = [] then 0 else 4),
      fun () ->
        let v = Pick.one r changeable in
        (* The value doesn't read the variable, so values can't double on
           each pass of a loop. *)
        let e = expr b (without [ v.name ] sc) ~depth ~known:false v.ty in
        (sc, line (v.name ^ " = " ^ e.text)) );
    ( (if numbers = [] then 0 else 3),
      fun () -> (sc, compound_assign b sc ~depth (Pick.one r numbers)) );
    ( (if records = [] then 0 else 2),
      fun () -> (sc, field_assign b sc ~depth (Pick.one r records)) );
    ( (if lists = [] then 0 else 3),
      fun () -> (sc, list_change b sc ~depth (Pick.one r lists)) );
    ( (if maps = [] then 0 else 3),
      fun () -> (sc, map_change b sc ~depth (Pick.one r maps)) );
    ( (if inout_calls = [] then 0 else 2),
      fun () -> (sc, inout_call b sc ~depth (Pick.one r inout_calls)) );
  ]
