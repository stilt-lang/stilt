open Model_json
open Model_types
open Model_ops
open Model_forms

type callbacks = {
  expr : Tast.expr -> Model_json.t;
  stored :
    Tast.expr ->
    Tast.expr list ->
    (Model_json.t -> Model_json.t list -> Model_json.t) ->
    Model_json.t;
}

(* std.maps: the functions the calculus has, a map a value, so an [inout self]
   one writes its result back to its receiver's place. *)
let rec map_call (on : callbacks) cx (e : Tast.expr) name args =
  let values = List.map (fun (a : Tast.arg) -> on.expr a.value) args in
  let map_ty =
    match args with
    | (a : Tast.arg) :: _ when is_map a.value.ty -> a.value.ty
    | _ -> e.ty
  in
  match (name, args, Model_keys.keyed cx map_ty) with
  | _, _, Some (k, v) -> keyed_call on cx e name args (k, v)
  | _, _, None -> map_native on cx e name args values

(* std.maps: a native of a map whose keys the calculus can't find, as the export writes
   such a map (Model_keys). *)
and keyed_call (on : callbacks) cx (e : Tast.expr) name args (k, v) =
  let values = List.map (fun (a : Tast.arg) -> on.expr a.value) args in
  let at = Model_composed.at cx in
  let entries = Model_keys.entry_ty k v in
  match (name, values) with
  | "new", [] -> tag "list" [ ty cx entries; Arr [] ]
  | "len", [ m ] -> op (tag "list" [ Str "len" ]) [ m ]
  | "is_empty", [ m ] -> op (tag "list" [ Str "isEmpty" ]) [ m ]
  | "contains", [ m; key ] -> Model_keys.contains at cx k v m key
  | "get_or", [ m; key; d ] -> Model_keys.get_or at cx k v m key d
  | "get", [ m; key ] -> Model_keys.get at cx k v m key
  | "keys", [ m ] -> Model_keys.keys cx k v m
  | "values", [ m ] -> Model_keys.values cx k v m
  | "entries", [ m ] -> Model_keys.entries cx k v m
  | "insert", _ -> (
      match args with
      | { value = receiver; _ } :: rest ->
          on.stored receiver
            (List.map (fun (a : Tast.arg) -> a.value) rest)
            (fun read vs ->
              match vs with
              | [ key; x ] -> Model_keys.insert at cx k v read key x
              | _ -> outside "the function Map.insert")
      | [] -> outside "the function Map.insert")
  | "remove", _ -> (
      match args with
      | [ m; key ] ->
          let pair = temp "removed" e.loc in
          let stored =
            on.stored m.value [] (fun _ _ ->
                tag "field" [ var_e pair; Str "0" ])
          in
          tag "letIn"
            [
              Str pair;
              ty cx (Types.Tuple [ Model_keys.repr k v; e.ty ]);
              Model_keys.remove at cx k v (on.expr m.value) (on.expr key.value);
              tag "seq" [ stored; tag "field" [ var_e pair; Str "1" ] ];
            ]
      | _ -> outside "the function Map.remove")
  | _ ->
      outside "the function Map.%s of a map whose keys have written impls" name

and map_native (on : callbacks) cx (e : Tast.expr) name args values =
  match (name, args) with
  | "get", [ m; k ] -> map_get on cx e m.value k.value
  | "remove", [ m; k ] -> map_remove on cx e m.value k.value
  | ( ( "new" | "with_default" | "len" | "is_empty" | "contains" | "get_or"
      | "keys" | "values" | "entries" ),
      _ ) ->
      let op_name =
        match name with
        | "is_empty" -> "isEmpty"
        | "get_or" -> "getOr"
        | "with_default" -> "withDefault"
        | n -> n
      in
      map_op op_name values
  | "insert", { value = receiver; _ } :: rest ->
      on.stored receiver
        (List.map (fun (a : Tast.arg) -> a.value) rest)
        (fun read vs -> map_op "insert" (read :: vs))
  | _ -> outside "the function Map.%s" name

(* [m.get(k)]: [Some] of the value of [k], or [None] when it has no entry, even when the
   map has a default (std.maps). *)
and map_get on cx e m k =
  let read = temp "get-map" e.loc and key = temp "get-key" e.loc in
  let some =
    option cx e.ty "Some" [ map_op "index" [ var_e read; var_e key ] ]
  in
  let pick =
    tag "if"
      [
        map_op "contains" [ var_e read; var_e key ];
        ty cx e.ty;
        some;
        option cx e.ty "None" [];
      ]
  in
  tag "letIn"
    [
      Str read;
      ty cx m.ty;
      on.expr m;
      tag "letIn" [ Str key; ty cx k.ty; on.expr k; pick ];
    ]

(* [m.remove(k)]: the map stored without the entry of [k], and [Some] of its value, or
   [None] when it has no entry, the map stored as it was (std.maps). *)
and map_remove on cx e m k =
  let key = temp "remove-key" e.loc and x = temp "removed" e.loc in
  let removed =
    on.stored m [] (fun read _ -> map_op "remove" [ read; var_e key ])
  in
  let some =
    tag "letIn"
      [
        Str x;
        ty cx (option_payload e.ty);
        map_op "index" [ on.expr m; var_e key ];
        tag "seq" [ removed; option cx e.ty "Some" [ var_e x ] ];
      ]
  in
  let pick =
    tag "if"
      [
        map_op "contains" [ on.expr m; var_e key ];
        ty cx e.ty;
        some;
        option cx e.ty "None" [];
      ]
  in
  tag "letIn" [ Str key; ty cx k.ty; on.expr k; pick ]

(* std.sets: the functions the calculus has, a set a value, so an [inout self] one writes
   its result back to its receiver's place. *)
let set_call (on : callbacks) name args =
  let set_op o operands = op (tag "set" [ o ]) operands in
  let values = List.map (fun (a : Tast.arg) -> on.expr a.value) args in
  let combine c = set_op (tag "combine" [ Str c ]) values in
  let relate r = set_op (tag "relate" [ Str r ]) values in
  match (name, args) with
  | "new", _ -> set_op (Str "new") values
  | "from_list", _ -> set_op (Str "fromList") values
  | "len", _ -> set_op (Str "len") values
  | "is_empty", _ -> set_op (Str "isEmpty") values
  | "contains", _ -> set_op (Str "contains") values
  | "to_list", _ -> set_op (Str "toList") values
  | "union", _ -> combine "union"
  | "intersection", _ -> combine "intersection"
  | "difference", _ -> combine "difference"
  | "symmetric_difference", _ -> combine "symmetricDifference"
  | "is_subset", _ -> relate "subset"
  | "is_superset", _ -> relate "superset"
  | "is_disjoint", _ -> relate "disjoint"
  | ("insert" | "remove"), { value = receiver; _ } :: rest ->
      on.stored receiver
        (List.map (fun (a : Tast.arg) -> a.value) rest)
        (fun read vs -> set_op (Str name) (read :: vs))
  | _ -> outside "the function Set.%s" name

let set_natives =
  [
    "new";
    "from_list";
    "len";
    "is_empty";
    "contains";
    "to_list";
    "union";
    "intersection";
    "difference";
    "symmetric_difference";
    "is_subset";
    "is_superset";
    "is_disjoint";
    "insert";
    "remove";
  ]

let map_natives =
  [
    "new";
    "with_default";
    "len";
    "is_empty";
    "contains";
    "get_or";
    "keys";
    "values";
    "entries";
    "insert";
    "get";
    "remove";
  ]

let list_op name operands = op (tag "list" [ Str name ]) operands

(* [xs.get(i)]: [None] unless [0 <= i < len] (std.lists). *)
let get (on : callbacks) cx (e : Tast.expr) (l : Tast.expr) (i : Tast.expr) =
  let xs = temp "get-list" e.loc and k = temp "get-index" e.loc in
  let i64 = prelude_ty "i64" and bool = prelude_ty "bool" in
  let inside =
    binary And bool bool
      (binary Le i64 i64 (int_lit i64 "0" ~negated:false) (var_e k))
      (binary Lt i64 i64 (var_e k) (list_op "len" [ var_e xs ]))
  in
  let some = option cx e.ty "Some" [ tag "index" [ var_e xs; var_e k ] ] in
  let pick = tag "if" [ inside; ty cx e.ty; some; option cx e.ty "None" [] ] in
  let inner = tag "letIn" [ Str k; ty cx i.ty; on.expr i; pick ] in
  tag "letIn" [ Str xs; ty cx l.ty; on.expr l; inner ]

(* [xs.pop()]: [Some] of the last element, the list stored without it, or
   [None] for an empty list, which stays as it was (std.lists). *)
let pop (on : callbacks) cx (e : Tast.expr) receiver =
  let n = temp "pop-length" e.loc and x = temp "popped" e.loc in
  let i64 = prelude_ty "i64" in
  let zero = int_lit i64 "0" ~negated:false in
  let last = binary Sub i64 i64 (var_e n) (int_lit i64 "1" ~negated:false) in
  let shortened =
    on.stored receiver [] (fun read _ -> list_op "slice" [ read; zero; last ])
  in
  let some =
    tag "letIn"
      [
        Str x;
        ty cx (option_payload e.ty);
        tag "index" [ on.expr receiver; last ];
        tag "seq" [ shortened; option cx e.ty "Some" [ var_e x ] ];
      ]
  in
  let empty = binary Eq i64 i64 (var_e n) zero in
  let pick = tag "if" [ empty; ty cx e.ty; option cx e.ty "None" []; some ] in
  tag "letIn" [ Str n; ty cx i64; list_op "len" [ on.expr receiver ]; pick ]

(* The stable sort of the list [xs] by the keys [ks], both of the calculus,
   ascending or descending by [Ord.compare] on keys of type [k], whose [Ord]
   must be structural (std.lists). *)
let by_keys cx ~descending k t ks xs =
  if not (Model_impls.native_order cx k) then
    Model_impls.sorted_by_keys cx ~descending k t ks xs
  else
    let pair (t, cs) = Arr [ Str t; Arr (List.map (fun c -> Str c) cs) ] in
    let orders = Arr (List.map pair (ctor_orders cx k)) in
    op (tag "sortedByKey" [ Bool descending; orders ]) [ ks; xs ]

(* [xs.sorted_by(key)], the list [xs] and the function [key] of the calculus
   given: [key] called once for each element, in order, before the sort, each
   key pushed onto a list the sort then reads (std.lists). *)
let sorted_by cx (e : Tast.expr) ~descending (key_ty : Types.ty) xs key =
  let k =
    match norm key_ty with
    | Fn (_, k, _) -> k
    | _ -> outside "a sort by a key that isn't a function"
  in
  let t = elem e.ty in
  let n = temp "sort-list" e.loc and f = temp "sort-key" e.loc in
  let ks = temp "sort-keys" e.loc and x = temp "sort-element" e.loc in
  let call = call_e cx (var_e f) [ tag "value" [ var_e x ] ] k in
  let push =
    tag "assign" [ Arr [ Str ks; Arr [] ]; list_op "push" [ var_e ks; call ] ]
  in
  let loop = tag "for" [ Str x; ty cx t; var_e n; push ] in
  let keys = Types.Con (list_item, [ k ]) in
  let sorted = by_keys cx ~descending k t (var_e ks) (var_e n) in
  let collect =
    tag "varIn"
      [
        Str ks;
        ty cx keys;
        tag "list" [ ty cx k; Arr [] ];
        tag "seq" [ loop; sorted ];
      ]
  in
  tag "letIn"
    [ Str n; ty cx e.ty; xs; tag "letIn" [ Str f; ty cx key_ty; key; collect ] ]

(* The sorts of std.lists: [sorted_by] and [sorted_desc_by] by a key, [sorted]
   and [sorted_desc] by the elements themselves, and the [sort] forms, which
   store what the [sorted] form of their name gives in their receiver. *)
let sort_call (on : callbacks) cx (e : Tast.expr) name (args : Tast.arg list) =
  let descending =
    String.ends_with ~suffix:"desc" name
    || String.ends_with ~suffix:"desc_by" name
  in
  let in_place = String.starts_with ~prefix:"sort_" name || name = "sort" in
  let receiver, key =
    match args with
    | [ r ] -> (r.value, None)
    | [ r; k ] -> (r.value, Some k.value)
    | _ -> outside "the function List.%s" name
  in
  let result (l : Tast.expr) = { e with ty = l.ty } in
  let sorted read operands =
    match (key, operands) with
    | None, [] ->
        let x = temp "sort-list" e.loc in
        let t = elem receiver.ty in
        tag "letIn"
          [
            Str x;
            ty cx receiver.ty;
            read;
            by_keys cx ~descending t t (var_e x) (var_e x);
          ]
    | Some (k : Tast.expr), [ f ] ->
        sorted_by cx (result receiver) ~descending k.ty read f
    | _ -> outside "the function List.%s" name
  in
  let operands = Option.to_list key in
  if in_place then on.stored receiver operands sorted
  else sorted (on.expr receiver) (List.map on.expr operands)

let natives =
  [
    "new"; "len"; "is_empty"; "push"; "pop"; "get"; "slice"; "insert"; "remove";
  ]
  @ [ "sorted"; "sorted_desc"; "sorted_by"; "sorted_desc_by" ]
  @ [ "sort"; "sort_desc"; "sort_by"; "sort_desc_by" ]

(* std.lists: the functions the calculus has, a list a value, so [push] writes
   its result back to its receiver's place. *)
let list_call (on : callbacks) cx (e : Tast.expr) name args =
  let values = List.map (fun (a : Tast.arg) -> on.expr a.value) args in
  match (name, args) with
  | "new", [] -> tag "list" [ ty cx (elem e.ty); Arr [] ]
  | "len", _ -> list_op "len" values
  | "is_empty", _ -> list_op "isEmpty" values
  | "get", [ l; i ] -> get on cx e l.value i.value
  | "slice", _ -> list_op "slice" values
  | ( ( "sorted" | "sorted_desc" | "sorted_by" | "sorted_desc_by" | "sort"
      | "sort_desc" | "sort_by" | "sort_desc_by" ),
      _ ) ->
      sort_call on cx e name args
  | ("push" | "insert"), { value = receiver; _ } :: rest ->
      on.stored receiver
        (List.map (fun (a : Tast.arg) -> a.value) rest)
        (fun read vs -> list_op name (read :: vs))
  | "remove", [ { value = receiver; _ }; i ] ->
      (* std.lists: [xs.remove(i)] gives element [i] and stores the list
         without it; reading the element first panics as storing does. *)
      let n = temp "removed" e.loc in
      let k = temp "remove-index" e.loc in
      let element = tag "index" [ on.expr receiver; var_e k ] in
      let store =
        on.stored receiver [] (fun read _ ->
            list_op "removeAt" [ read; var_e k ])
      in
      tag "letIn"
        [
          Str k;
          ty cx i.value.ty;
          on.expr i.value;
          tag "letIn"
            [ Str n; ty cx e.ty; element; tag "seq" [ store; var_e n ] ];
        ]
  | "pop", [ { value = receiver; _ } ] -> pop on cx e receiver
  | _ -> outside "the function List.%s" name

(* The length [n] of the array type [Array<T, n>] that a call gives. *)
let array_length (t : Types.ty) =
  match Types.resolve t with
  | Con ({ home = "std.array"; name = "Array" }, [ _; n ]) -> (
      match Types.resolve n with
      | Value text -> int_of_string_opt text
      | _ -> None)
  | _ -> None

(* [array.fill(x)] at [Array<T, n>]: [n] copies of [x], as the array of them, or after
   [x] a panic of the kind [bounds] when [n] is negative (generics.arrays). *)
let array_fill (on : callbacks) cx (e : Tast.expr) (x : Tast.expr) =
  match array_length e.ty with
  | Some n when n < 0 -> op (tag "panic" [ Str "bounds" ]) [ on.expr x ]
  | Some n when n <= 10_000 ->
      let v = temp "fill" e.loc in
      tag "letIn"
        [
          Str v;
          ty cx x.ty;
          on.expr x;
          tag "record"
            [
              Str (record_name cx e.ty);
              Arr
                [
                  Arr
                    [
                      Str array_field;
                      tag "list"
                        [ ty cx x.ty; Arr (List.init n (fun _ -> var_e v)) ];
                    ];
                ];
            ];
        ]
  | _ -> outside "an array of a length the model doesn't hold"

(* [array.from_list(xs)] at [Option<Array<T, n>>]: [Some] of the elements when [xs] has
   [n] of them, and [None] otherwise (generics.arrays). *)
let array_from_list (on : callbacks) cx (e : Tast.expr) (l : Tast.expr) =
  match array_length (option_payload e.ty) with
  | Some n ->
      let xs = temp "from-list" e.loc and i64 = prelude_ty "i64" in
      let fits =
        binary Eq i64 i64
          (list_op "len" [ var_e xs ])
          (int_lit i64 (string_of_int n) ~negated:false)
      in
      let pick =
        tag "if"
          [
            fits;
            ty cx e.ty;
            option cx e.ty "Some"
              [
                tag "record"
                  [
                    Str (record_name cx (option_payload e.ty));
                    Arr [ Arr [ Str array_field; var_e xs ] ];
                  ];
              ];
            option cx e.ty "None" [];
          ]
      in
      tag "letIn" [ Str xs; ty cx l.ty; on.expr l; pick ]
  | None -> outside "an array of a length the model doesn't hold"
