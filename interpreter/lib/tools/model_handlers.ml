(* Effects and handlers as the calculus writes them (formal/Stilt/Handling.lean): a
   performance, a handler literal, a [with] and a [resume]. What a handler's body writes
   to the output, and the shared values it changes, stay in the world the performance
   resumes in. *)

open Model_json
open Model_types
open Model_ops
open Model_forms

type callbacks = {
  expr : Tast.expr -> Model_json.t;
  block : Tast.block -> Model_json.t;
}

(* [E.op(args)]: its arguments as one value, [()] for none and a tuple for several
   (handlers.performing-operation). *)
let perform cb cx (_ : Tast.expr) eff name targs (args : Tast.arg list) =
  let key = effect_key cx eff targs in
  let arg =
    match args with
    | [ a ] -> cb.expr a.value
    | args ->
        op (Str "tuple") (List.map (fun (a : Tast.arg) -> cb.expr a.value) args)
  in
  let arg = match args with [] -> unit_e | _ -> arg in
  tag "perform" [ Str key; Str name; arg ]

(* [resume(v)], a performance of the reserved operation, whose value is the rest of the
   block's (handlers.resuming). *)
let resume cb v =
  let v = match v with Some x -> cb.expr x | None -> unit_e in
  tag "perform" [ Str "resume"; Str "resume"; v ]

(* The parameters of an operation's body, bound from its argument [arg] of the type [a]. *)
let params cx (a : Types.ty) result arg (ps : Tast.pattern list) body =
  let types =
    match (ps, norm a) with [ _ ], _ -> [ a ] | _, Tuple ts -> ts | _ -> []
  in
  if List.length types <> List.length ps then
    outside "an operation's parameters";
  let one i (p : Tast.pattern) t acc =
    let v =
      if List.length ps = 1 then arg
      else tag "field" [ arg; Str (string_of_int i) ]
    in
    match p.pat with
    | P_bind x -> tag "letIn" [ Str (var_name x); ty cx t; v; acc ]
    | _ -> tag "match" [ v; result; Arr [ arm cx p acc ] ]
  in
  let rec go i ps ts =
    match (ps, ts) with
    | p :: ps, t :: ts -> one i p t (go (i + 1) ps ts)
    | _ -> body
  in
  go 0 ps types

(* An operation's body as a closure: it takes the argument, binds it, and gives its value
   (handlers.handler-literals). *)
let clause cb cx (e : Tast.expr) answer (name, a, b) (f : Tast.expr) =
  match f.desc with
  | Closure (ps, _, body) ->
      let arg = temp ("operation-" ^ name) e.loc in
      let result_ty = Option.value answer ~default:b in
      let result = ty cx result_ty in
      let raising =
        match norm f.ty with
        | Fn (_, _, r) -> raises_in cx r
        | _ -> fun g -> g ()
      in
      let body = raising (fun () -> cb.expr body) in
      let body = params cx a result (var_e arg) ps body in
      let resume =
        match answer with Some r -> Arr [ ty cx b; ty cx r ] | None -> Null
      in
      tag "closure"
        [
          Arr [ Arr [ Str "let"; Str arg; ty cx a; Null ] ];
          result;
          Arr [ Bool true; Null; Arr []; Arr []; resume ];
          body;
        ]
  | _ -> outside "an operation of a handler that isn't a closure literal"

(* A handler literal: the record of its operations' bodies (handlers.handler-literals). *)
let handler cb cx (e : Tast.expr) (h : Tast.handler) =
  match norm e.ty with
  | Handler ht ->
      let key = handler_record cx ht in
      let ops = operations cx ht.eff ht.hargs in
      let field (name, f) =
        match List.find_opt (fun (n, _, _) -> n = name) ops with
        | Some op -> Arr [ Str name; clause cb cx e ht.answer op f ]
        | None -> outside "an operation its effect lacks"
      in
      tag "record" [ Str key; Arr (List.map field h.ops) ]
  | _ -> outside "a handler of a type the model lacks"

(* [with h { block }] (handlers.with and handlers.resuming). A handler that takes control
   and drops the rest of the block lets go of the shared values a [when] in that rest
   holds (shared.when). *)
let with_ cb cx (h : Tast.expr) eff targs (b : Tast.block) =
  let key = effect_key cx eff targs in
  let control =
    match norm h.ty with
    | Handler { answer = Some _; _ } -> true
    | Handler _ -> false
    | _ -> outside "a handler of a type the model lacks"
  in
  let h = cb.expr h in
  tag "with" [ Str key; Bool control; h; cb.block b ]

(* A handler literal, a [with] or a [resume]. *)
let form cb cx (e : Tast.expr) =
  match e.desc with
  | With (h, eff, _, b) when eff = async_item ->
      (* tasks.with-waits: the tasks under it have ended once its block has, in the
         sequential run, where each runs to its end when it starts. *)
      tag "seq" [ cb.expr h; cb.block b ]
  | Handler h -> handler cb cx e h
  | With (h, eff, targs, b) -> with_ cb cx h eff targs b
  | Resume v -> resume cb v
  | _ -> outside "an expression the model lacks"
