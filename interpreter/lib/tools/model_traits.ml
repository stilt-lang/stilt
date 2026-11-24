open Model_json
open Model_types
open Model_ops
open Model_forms

(* The calculus has [Set] as a type of its own (std.sets), shown and compared by its own
   operations, so the prelude's impls for it, which read its record's field, don't run. *)
let written cx trait name t : target option =
  match norm t with
  | Con (owner, _)
    when declared_record owner
         && Model_fns.code cx (Impl (trait, owner, name)) <> None ->
      Some (Impl (trait, owner, name))
  | _ -> None

let call_values cx target types values result =
  let inst = Model_fns.instance cx target [] types in
  let f = tag "fnRef" [ Str inst.fkey; Arr []; Arr [] ] in
  call_e cx f (List.map (fun v -> tag "value" [ v ]) values) result

let method_of cx (b : Ast.binary) t =
  match b with
  | Eq | Ne -> written cx eq_trait "eq" t
  | Lt | Le | Gt | Ge -> written cx ord_trait "compare" t
  | _ -> None

let through_written cx b t = method_of cx b t <> None

(* [x == y] is [Eq.eq(x, y)], and [x < y] tests the [Ordering] that
   [Ord.compare(x, y)] gives (traits.operators). *)
let operator cx (b : Ast.binary) (tx, x) (ty, y) =
  let called =
    let result =
      match b with
      | Eq | Ne -> prelude_ty "bool"
      | _ -> Types.Con (ordering_item, [])
    in
    call_values cx (Option.get (method_of cx b tx)) [ tx; ty ] [ x; y ] result
  in
  let is ctor =
    let ordering = declared cx ordering_item [] in
    op
      (tag "structural" [ Str "eq"; Arr [] ])
      [ called; tag "variant" [ Str ordering; Str ctor; Arr [] ] ]
  in
  match b with
  | Eq -> called
  | Ne -> op (Str "not") [ called ]
  | Lt -> is "Less"
  | Gt -> is "Greater"
  | Le -> op (Str "not") [ is "Greater" ]
  | _ -> op (Str "not") [ is "Less" ]

(* [x.compare(y)] through the prelude's structural impl of [Ord]: [Less] when
   its order puts [x] first, [Greater] when it puts [y] first, and [Equal]
   otherwise, [x] and [y] each evaluated once, in order (traits.structural-calls).
   The order is the impl's, not the operators', so floats compare by the total
   order of traits.floats. *)
let compare cx (e : Tast.expr) (t : Types.ty) x y =
  let pair (t, cs) = Arr [ Str t; Arr (List.map (fun c -> Str c) cs) ] in
  let orders = Arr (List.map pair (ctor_orders cx t)) in
  let a = temp "compare-left" e.loc and b = temp "compare-right" e.loc in
  let test c = op (tag "structural" [ Str c; orders ]) [ var_e a; var_e b ] in
  let ordering = declared cx { home = "std.prelude"; name = "Ordering" } [] in
  let case c = tag "variant" [ Str ordering; Str c; Arr [] ] in
  let result = ty cx e.ty in
  let pick =
    tag "if"
      [
        test "lt";
        result;
        case "Less";
        tag "if" [ test "gt"; result; case "Greater"; case "Equal" ];
      ]
  in
  tag "letIn" [ Str a; ty cx t; x; tag "letIn" [ Str b; ty cx t; y; pick ] ]

(* Whether a type holds a string, which a structural [Show] writes quoted when it is
   nested and bare when it isn't (std.show-output). *)
let rec holds_str cx t =
  match norm t with
  | Types.Con ({ home = "std.prelude"; name = "str" }, []) -> true
  | Con ({ home = "std.prelude"; name }, [])
    when List.mem name Types.integer_types
         || List.mem name [ "f32"; "f64"; "bool"; "Never" ] ->
      false
  | Tuple ts -> List.exists (holds_str cx) ts
  | Con (i, args) when not (List.mem i [ list_item; option_item ]) -> (
      match Env.type_info cx.env i with
      | Some { Env.def = Env.Record fields; _ } ->
          List.exists
            (fun (_, f) ->
              holds_str cx (instantiated cx { key = ""; item = i; args } f))
            fields
      | Some { Env.def = Env.Variants ctors; _ } ->
          List.exists
            (fun (_, ts) ->
              List.exists
                (fun f ->
                  holds_str cx (instantiated cx { key = ""; item = i; args } f))
                ts)
            ctors
      | _ -> true)
  | Con (_, args) -> List.exists (holds_str cx) args
  | _ -> true

let concat parts = op (Str "concat") parts
let strs = Types.Con (list_item, [ prelude_ty "str" ])

(* The texts that [show_part] gives each element of [iterable], of type [elem], joined by
   [, ] between [opening] and [closing]. *)
let joined cx name elem iterable show_part (opening, closing) =
  let x = name "element" and parts = name "parts" in
  let push =
    tag "assign"
      [
        Arr [ Str parts; Arr [] ];
        op (tag "list" [ Str "push" ]) [ var_e parts; show_part (var_e x) ];
      ]
  in
  tag "varIn"
    [
      Str parts;
      ty cx strs;
      tag "list" [ Str "str"; Arr [] ];
      tag "seq"
        [
          tag "for" [ Str x; ty cx elem; iterable; push ];
          concat
            [
              str_lit opening;
              op (tag "list" [ Str "join" ]) [ str_lit ", "; var_e parts ];
              str_lit closing;
            ];
        ];
    ]

(* Texts with [, ] between them. *)
let rec separated = function
  | [] -> []
  | [ x ] -> [ x ]
  | x :: rest -> x :: str_lit ", " :: separated rest

(* How the prelude's [Show] writes a value of type [t] when one of its parts has an impl of
   [Show] of its own, which the structural [Show] calls (traits.structural-impls,
   std.show-output): a list as its elements' texts between [[]] and [,], an option as
   [Some(…)] or [None], a map as [{k: v, …}], a tuple between [(] and [)], and a part with
   a written impl by that impl's [show_nested], or its [show] at the top or when it writes
   no [show_nested] (traits.show). [None] when [t] holds anything else the structural
   [Show] would write unlike its parts' top-level texts: a string, or a type the calculus
   can't take apart. *)
let rec composed cx depth t =
  let nested =
    if depth = 0 then None else written cx show_trait "show_nested" t
  in
  match (nested, written cx show_trait "show" t) with
  | Some show, _ | None, Some show ->
      Some (fun v -> call_values cx show [ t ] [ v ] (prelude_ty "str"))
  | None, None when structural cx t ->
      if holds_str cx t then None
      else Some (fun v -> op (Str "showValue") [ v ])
  | None, None -> (
      let name base = Printf.sprintf "show-%s/%d" base depth in
      let part t = composed cx (depth + 1) t in
      match norm t with
      | Types.Con (i, [ e ]) when i = list_item ->
          Option.map
            (fun show_e v ->
              let l = name "list" in
              tag "letIn"
                [
                  Str l; ty cx t; v; joined cx name e (var_e l) show_e ("[", "]");
                ])
            (part e)
      | Con (i, [ e ]) when i = option_item ->
          Option.map (composed_option cx name t) (part e)
      | Con (i, [ k; e ]) when i = map_item -> (
          match (part k, part e) with
          | Some show_k, Some show_e ->
              Some (composed_map cx name (k, e) (show_k, show_e))
          | _ -> None)
      | Tuple ts ->
          let shows = List.map part ts in
          if List.mem None shows then None
          else Some (composed_tuple cx name t (List.filter_map Fun.id shows))
      | _ -> None)

and composed_option cx name t show_e v =
  let x = name "payload" in
  let some =
    Arr
      [
        option_pattern cx t [ tag "bind" [ Str x ] ];
        Arr [ Str x ];
        concat [ str_lit "Some("; show_e (var_e x); str_lit ")" ];
      ]
  in
  tag "match"
    [ v; Str "str"; Arr [ some; Arr [ Str "wild"; Arr []; str_lit "None" ] ] ]

(* std.show-output: a map as [{k: v, …}] in insertion order, which its entries keep
   (std.maps). *)
and composed_map cx name (k, e) (show_k, show_e) v =
  let field x n = tag "field" [ x; Str n ] in
  let entry x =
    concat [ show_k (field x "0"); str_lit ": "; show_e (field x "1") ]
  in
  joined cx name (Types.Tuple [ k; e ]) (map_op "entries" [ v ]) entry ("{", "}")

(* traits.structural-impls: a tuple as its elements' texts, a 1-tuple with a trailing
   [,]. *)
and composed_tuple cx name t shows v =
  let tup = name "tuple" in
  let parts =
    List.mapi
      (fun k show -> show (tag "field" [ var_e tup; Str (string_of_int k) ]))
      shows
  in
  let close = if List.length shows = 1 then ",)" else ")" in
  tag "letIn"
    [
      Str tup;
      ty cx t;
      v;
      concat ((str_lit "(" :: separated parts) @ [ str_lit close ]);
    ]

(* A splice's text: by the impl of [Show] the program writes for its type, or as the
   prelude shows it, around the impls the program writes for its parts. *)
let shown cx t v =
  match written cx show_trait "show" t with
  | Some show -> call_values cx show [ t ] [ v ] (prelude_ty "str")
  | None when structural cx t -> show ~structural:true t v
  | None -> (
      match composed cx 0 t with
      | Some show_v -> show_v v
      | None -> show ~structural:false t v)

(* A call of a structural impl's method at [Self], its arguments exported: [compare] the
   [Ordering] of the structural order, and [x.show()] and [x.eq(y)] what a splice and [==]
   give (traits.structural-calls). *)
let structural_call cx (e : Tast.expr) (t : Hir.item) name self args =
  match (t.name, name, args) with
  | "Ord", "compare", [ x; y ] when structural_by cx "Ord" self ->
      compare cx e self x y
  | "Show", "show", [ x ] when structural cx self -> shown cx self x
  | "Eq", "eq", [ x; y ] when structural_by cx "Eq" self ->
      binary_at cx Eq self self x y
  | _ -> outside "the method %s.%s" (item_name t) name

(* The components that the structural impls of [trait] compare, first to last, on a tuple
   or on a record without an impl of [trait] of its own, the record's fields in declaration
   order (traits.structural-calls), each with how a value reaches it. *)
let components cx trait t =
  let at n v = tag "field" [ v; Str n ] in
  match norm t with
  | Types.Tuple (_ :: _ as ts) ->
      Some (List.mapi (fun i t -> (at (string_of_int i), t)) ts)
  | Con (i, args)
    when declared_record i && Env.trait_impl cx.env ~trait i = None -> (
      match Env.type_info cx.env i with
      | Some { Env.def = Env.Record fields; _ } ->
          let sub = instantiated cx { key = ""; item = i; args } in
          Some (List.map (fun (f, t) -> (at f, sub t)) fields)
      | _ -> None)
  | _ -> None

(* Whether [==] (with [Eq]) or [<] (with [Ord]) on a tuple or a record reaches a component's
   written impl through the structural one: each component compared by its own impl, the
   written one or the structural one, so the comparison is composed of them
   (traits.structural-calls). *)
let rec composed_by cx (trait : Hir.item) b t =
  let name = trait.name in
  let part t =
    method_of cx b t <> None
    || structural_by cx name t || composed_by cx trait b t
  in
  (not (structural_by cx name t))
  &&
  match components cx trait t with
  | Some parts -> List.for_all (fun (_, t) -> part t) parts
  | None -> false

let composed_eq cx t = composed_by cx eq_trait Ast.Eq t
let composed_ord cx t = composed_by cx ord_trait Ast.Lt t

(* [x == y] on such a value: its components compared from first to last, stopping at the
   first unequal pair, as [&&] stops (traits.structural-calls), [x] and [y] each evaluated
   once, in order; [!=] is its negation. *)
let rec tuple_eq cx (e : Tast.expr) b t x y =
  let parts = Option.get (components cx eq_trait t) in
  let a = temp "eq-left" e.loc and c = temp "eq-right" e.loc in
  let bool = prelude_ty "bool" in
  let one (at, t) =
    let l = at (var_e a) and r = at (var_e c) in
    if composed_eq cx t then tuple_eq cx e Ast.Eq t l r
    else if method_of cx Eq t <> None then operator cx Eq (t, l) (t, r)
    else binary_at cx Eq t t l r
  in
  let all =
    match List.map one parts with
    | [] -> tag "bool" [ Bool true ]
    | first :: rest ->
        List.fold_left (fun acc p -> binary And bool bool acc p) first rest
  in
  let all = if b = Ast.Ne then op (Str "not") [ all ] else all in
  tag "letIn" [ Str a; ty cx t; x; tag "letIn" [ Str c; ty cx t; y; all ] ]

let ordering_ty = Types.Con (ordering_item, [])

(* The [Ordering] a written or structural [compare] gives of [l] and [r], of type [t]. *)
let ordering_of cx (e : Tast.expr) t l r =
  match method_of cx Lt t with
  | Some target -> call_values cx target [ t; t ] [ l; r ] ordering_ty
  | None -> compare cx { e with ty = ordering_ty } t l r

(* [x.compare(y)] on such a value: lexicographic, the first component whose [compare]
   isn't [Equal] deciding, [x] and [y] each evaluated once, in order
   (traits.structural-calls). *)
let rec composed_compare cx (e : Tast.expr) t x y =
  let parts = Option.get (components cx ord_trait t) in
  let a = temp "compare-left" e.loc and c = temp "compare-right" e.loc in
  let ordering = declared cx ordering_item [] in
  let equal = tag "variant" [ Str ordering; Str "Equal"; Arr [] ] in
  let result = ty cx ordering_ty in
  let step i (at, t) rest =
    let l = at (var_e a) and r = at (var_e c) in
    let o = Printf.sprintf "%s/%d" (temp "ordering" e.loc) i in
    let this =
      if composed_ord cx t then composed_compare cx e t l r
      else ordering_of cx e t l r
    in
    let same = op (tag "structural" [ Str "eq"; Arr [] ]) [ var_e o; equal ] in
    tag "letIn"
      [ Str o; result; this; tag "if" [ same; result; rest; var_e o ] ]
  in
  let pick =
    List.fold_right
      (fun (i, p) rest -> step i p rest)
      (List.mapi (fun i p -> (i, p)) parts)
      equal
  in
  tag "letIn" [ Str a; ty cx t; x; tag "letIn" [ Str c; ty cx t; y; pick ] ]

(* [x < y] and the other ordering operators on such a value test the [Ordering] that its
   composed [compare] gives (traits.operators). *)
let composed_operator cx (e : Tast.expr) (b : Ast.binary) t x y =
  let ordering = declared cx ordering_item [] in
  let is ctor =
    op
      (tag "structural" [ Str "eq"; Arr [] ])
      [
        composed_compare cx e t x y;
        tag "variant" [ Str ordering; Str ctor; Arr [] ];
      ]
  in
  match b with
  | Lt -> is "Less"
  | Gt -> is "Greater"
  | Le -> op (Str "not") [ is "Greater" ]
  | _ -> op (Str "not") [ is "Less" ]

(* Whether the operator [b] on a value of type [t] is composed of its components' impls. *)
let composed_at cx (b : Ast.binary) t =
  match b with
  | Eq | Ne -> composed_eq cx t
  | Lt | Le | Gt | Ge -> composed_ord cx t
  | _ -> false

(* The operator [b], the expression [e], on a value that {!composed_at}. *)
let composed_binary cx e (b : Ast.binary) t x y =
  match b with
  | Eq | Ne -> tuple_eq cx e b t x y
  | _ -> composed_operator cx e b t x y
