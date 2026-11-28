open Model_json
open Model_types
open Model_forms

(* How a value is stored into a place: an assignment to a path from a
   variable, or, for a place through a map's element, an expression built from
   the value. *)
type store = Path of Model_json.t | Through of (Model_json.t -> Model_json.t)

(* The index of [v[i]] through the writable binding [w], the index [i] read into [j]: the
   index into its source, or [-1] when it lies outside the binding's part, which no list
   has (projections.places-through-views). *)
let through (w : writable) j i =
  tag "through" [ Str j; Str w.start; Str w.stop; i ]

let write store w =
  match store with Path p -> tag "assign" [ p; w ] | Through f -> f w

(* How a map's element is stored and read: by the calculus's own map, or as the export
   writes a map whose keys have impls that the program writes (Model_keys). *)
let element cx t read key =
  match Model_keys.keyed cx t with
  | Some (kt, v) ->
      let at = Model_composed.at cx in
      ( (fun w -> Model_keys.insert at cx kt v read key w),
        Model_keys.index at cx kt v read key )
  | None ->
      ((fun w -> map_op "insert" [ read; key; w ]), map_op "index" [ read; key ])

(* [v[i]] through the writable binding [w], a place of its source's parameter
   (projections.places-through-views): its index's temporary, the store and the read. *)
let through_writable ~expr cx (w : writable) (i : Tast.expr) =
  let n = Printf.sprintf "index/%d:%d" i.loc.line i.loc.col in
  let at = through w (temp "through" i.loc) (var_e n) in
  ( [ (n, ty cx i.ty, expr i) ],
    Path (Arr [ Str w.src; Arr [ tag "index" [ at ] ] ]),
    tag "index" [ var_e w.src; at ] )

(* Whether a place goes through a map's element (std.map-element-places). *)
let rec through_map (e : Tast.expr) =
  match e.desc with
  | Field (b, _) | Tuple_field (b, _) -> through_map b
  | Index (b, _) -> is_map b.ty || through_map b
  | _ -> false

(* Whether a place's root is a writable binding, whose indexes are its source's. *)
let rec through_writable_root cx (e : Tast.expr) =
  match e.desc with
  | Local v -> writable_of cx v <> None
  | Field (b, _) | Tuple_field (b, _) | Index (b, _) ->
      through_writable_root cx b
  | _ -> false

(* Whether an assignment to [p] is the calculus's form of one through a map's element
   (std.map-element-places): its root is a binding of its own, and it goes through exactly one
   element of a map that the calculus holds, followed by at least one field or list index. *)
let element_place cx (p : Tast.expr) =
  let rec steps (e : Tast.expr) =
    match e.desc with
    | Local v -> if writable_of cx v = None then Some [] else None
    | Field (b, _) | Tuple_field (b, _) ->
        Option.map (fun s -> s @ [ None ]) (steps b)
    | Index (b, _) ->
        Option.map
          (fun s -> s @ [ (if is_map b.ty then Some b.ty else None) ])
          (steps b)
    | _ -> None
  in
  match steps p with
  | Some s -> (
      match List.filter_map Fun.id s with
      | [ m ] ->
          Model_keys.keyed cx m = None && List.nth s (List.length s - 1) = None
      | _ -> false)
  | None -> false

(* Whether the calculus has [p op= e] as its form (values.compound-assignment-order):
   at a place that [p = e] stores, or at the last key of a map that the calculus holds,
   neither through a writable binding. *)
let compound_place cx (p : Tast.expr) =
  (not (through_writable_root cx p))
  &&
  match p.desc with
  | Index (b, _) when is_map b.ty ->
      (not (through_map b)) && Option.is_none (Model_keys.keyed cx b.ty)
  | _ -> not (through_map p)

(* A place whose index expressions and keys are temporaries: their bindings,
   how a value is stored into it, and the expression that reads it. A place
   through a map's element stores the changed element back with [m[k] = …],
   reading [m[k]] first when the place goes on past it (std.map-element-places). *)
let rec receiver ~expr cx (e : Tast.expr) =
  let extend (lets, store, read) (b : Tast.expr) step get =
    let store =
      match store with
      | Path (Arr [ root; Arr steps ]) ->
          Path (Arr [ root; Arr (steps @ [ step ]) ])
      | Path _ -> outside "a place the model lacks"
      | Through write_b ->
          let n = temp "element" b.loc in
          Through
            (fun w ->
              write_b
                (tag "varIn"
                   [
                     Str n;
                     ty cx b.ty;
                     read;
                     tag "seq"
                       [
                         tag "assign" [ Arr [ Str n; Arr [ step ] ]; w ];
                         var_e n;
                       ];
                   ]))
    in
    (lets, store, get read)
  in
  match e.desc with
  | Local v when writable_of cx v <> None ->
      outside "a writable binding as a place of its own"
  | Index ({ desc = Local v; _ }, i) when writable_of cx v <> None ->
      through_writable ~expr cx (Option.get (writable_of cx v)) i
  | Local v ->
      ( [],
        Path (Arr [ Str (var_name v); Arr [] ]),
        tag "var" [ Str (var_name v) ] )
  | Field (b, f) ->
      extend (receiver ~expr cx b) b (tag "field" [ Str f ]) (fun r ->
          tag "field" [ r; Str f ])
  | Tuple_field (b, i) ->
      let f = string_of_int i in
      extend (receiver ~expr cx b) b (tag "field" [ Str f ]) (fun r ->
          tag "field" [ r; Str f ])
  | Index (b, k) when is_map b.ty ->
      let n = temp "key" k.loc in
      let lets, store, read = receiver ~expr cx b in
      let key = var_e n in
      let insert, index = element cx b.ty read key in
      ( lets @ [ (n, ty cx k.ty, expr k) ],
        Through (fun w -> write store (insert w)),
        index )
  | Index (b, i) ->
      let n = Printf.sprintf "index/%d:%d" i.loc.line i.loc.col in
      let lets, store, read = receiver ~expr cx b in
      let lets, store, read =
        if is_array b.ty then (
          (match store with
          | Through _ -> outside "an array's element through a map's element"
          | Path _ -> ());
          extend (lets, store, read) b (tag "field" [ Str array_field ])
            (fun r -> tag "field" [ r; Str array_field ]))
        else (lets, store, read)
      in
      let var = tag "var" [ Str n ] in
      extend
        (lets @ [ (n, ty cx i.ty, expr i) ], store, read)
        b (tag "index" [ var ])
        (fun r -> tag "index" [ r; var ])
  | _ -> outside "a place the model lacks"
