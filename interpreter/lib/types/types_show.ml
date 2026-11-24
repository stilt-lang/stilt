(* Types as a program would write them, for messages. *)

open Types

let rec to_string t =
  match resolve t with
  | Con (item, []) -> item.name
  | Con (item, args) ->
      Printf.sprintf "%s<%s>" item.name
        (String.concat ", " (List.map to_string args))
  | Param p -> p.name
  | App (h, args) ->
      Printf.sprintf "%s<%s>" (to_string h)
        (String.concat ", " (List.map to_string args))
  | Tuple [ t ] when not (Packs.is_spread t) ->
      Printf.sprintf "(%s,)" (to_string t)
  | Tuple ts ->
      Printf.sprintf "(%s)" (String.concat ", " (List.map to_string ts))
  | Record fields ->
      Printf.sprintf "{ %s }"
        (String.concat ", "
           (List.map (fun (f, t) -> f ^ ": " ^ to_string t) fields))
  | Spread (_, t) -> ".." ^ to_string t
  | Fn (params, ret, row) ->
      let param (mode, t) =
        (match (mode : mode) with Let -> "" | Inout -> "inout ") ^ to_string t
      in
      let ret =
        match resolve ret with Tuple [] -> "" | t -> " -> " ^ to_string t
      in
      let row = match row_to_string row with "" -> "" | row -> " / " ^ row in
      Printf.sprintf "fn(%s)%s%s"
        (String.concat ", " (List.map param params))
        ret row
  | Forall p ->
      let generic ((v : Hir.var), bounds) =
        match bounds with
        | [] -> v.name
        | bs ->
            v.name ^ ": " ^ String.concat " + " (List.map bound_to_string bs)
      in
      let body = to_string p.body in
      Printf.sprintf "fn<%s>%s"
        (String.concat ", " (List.map generic p.generics))
        (String.sub body 2 (String.length body - 2))
  (* handlers.handler-types *)
  | Handler h ->
      let answer =
        match h.answer with Some t -> " -> " ^ to_string t | None -> ""
      in
      let row =
        match row_to_string h.hrow with "" -> "" | row -> " / " ^ row
      in
      Printf.sprintf "handler %s%s%s"
        (effect_to_string (h.eff, h.hargs))
        answer row
  | Var _ as v -> (
      match unsolved v with
      | Some { kind = Int_literal; _ } -> "{integer}"
      | Some { kind = Float_literal; _ } -> "{float}"
      | _ -> "_")
  (* generics.constant-arguments: a value argument is shown as its value. *)
  | Value v -> v
  | Error -> "{error}"

and bound_to_string b =
  match b.args with
  | [] -> b.trait.name
  | args ->
      Printf.sprintf "%s<%s>" b.trait.name
        (String.concat ", " (List.map to_string args))

and effect_to_string (e, args) =
  match args with
  | [] -> e.Hir.name
  | args ->
      Printf.sprintf "%s<%s>" e.name
        (String.concat ", " (List.map to_string args))

and row_to_string r =
  let r = row_contents r in
  let elements =
    (if r.io then [ "io" ] else [])
    @ (match r.raise with
      | Some t -> [ "raise<" ^ to_string t ^ ">" ]
      | None -> [])
    @ List.map effect_to_string r.effects
    @ List.filter_map
        (fun (p : row_param) -> if p.implicit then None else Some p.var.name)
        (match r.tail with Row_params ps -> ps | Closed | Row_var _ -> [])
  in
  match elements with
  | [] -> ""
  | [ e ] -> e
  | es -> "{" ^ String.concat ", " es ^ "}"
