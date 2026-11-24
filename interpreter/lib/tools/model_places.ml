open Model_json
open Model_types
open Model_forms

(* How a value is stored into a place: an assignment to a path from a
   variable, or, for a place through a map's element, an expression built from
   the value. *)
type store = Path of Model_json.t | Through of (Model_json.t -> Model_json.t)

let write store w =
  match store with Path p -> tag "assign" [ p; w ] | Through f -> f w

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
      ( lets @ [ (n, ty cx k.ty, expr k) ],
        Through (fun w -> write store (map_op "insert" [ read; key; w ])),
        map_op "index" [ read; key ] )
  | Index (b, i) ->
      let n = Printf.sprintf "index/%d:%d" i.loc.line i.loc.col in
      let lets, store, read = receiver ~expr cx b in
      let var = tag "var" [ Str n ] in
      extend
        (lets @ [ (n, ty cx i.ty, expr i) ], store, read)
        b (tag "index" [ var ])
        (fun r -> tag "index" [ r; var ])
  | _ -> outside "a place the model lacks"
