(* Values built from literals and constructors, of every type. *)

open Code
open Context
open Ty

(* An integer literal of kind [k]. A literal takes its type from the context
   and defaults to [i64] (numbers.literal-defaults), so one whose type must be known is
   a constant, or an [i64] converted with a wrapping conversion. *)
let int_lit r ~known k =
  if known && k <> I64 then
    Pick.run r
      [
        (1, fun () -> atom (int_name k ^ ".MAX"));
        (1, fun () -> atom (int_name k ^ ".MIN"));
        ( 4,
          fun () ->
            method_on (compound (Lit.int r I64)) ("wrap_to_" ^ int_name k) [] );
      ]
  else
    let text = Lit.int r k in
    if text.[0] = '-' then compound ~known text else atom ~known text

let float_lit r ~known k =
  let name = float_name k in
  if Pick.chance r 0.1 then
    atom (name ^ "." ^ Pick.one r [ "PI"; "E"; "NAN"; "INFINITY" ])
  else
    let text = Lit.float r in
    let lit =
      if text.[0] = '-' then compound ~known text else atom ~known text
    in
    if known && k = F32 then method_on lit "to_f32" [] else lit

(* A value built from literals and constructors. *)
let value expr b sc ~depth ~known ty =
  let r = b.p.r in
  let sub ?(known = false) t = expr b sc ~depth:(depth - 1) ~known t in
  let texts cs = String.concat ", " (List.map (fun c -> c.text) cs) in
  match ty with
  | Int k -> int_lit r ~known k
  | Float k -> float_lit r ~known k
  | Bool -> atom (if Pick.chance r 0.5 then "true" else "false")
  | Str -> atom (Lit.string r)
  | Unit -> atom "()"
  | Tuple ts ->
      let items = List.map (fun t -> sub ~known t) ts in
      atom
        ~known:(List.for_all (fun c -> c.known) items)
        ("(" ^ texts items ^ ")")
  | List t ->
      if Pick.chance r 0.15 then atom ~known:false "[]"
      else
        let first = sub ~known t in
        let rest = Pick.times (Pick.between r 0 3) (fun () -> sub t) in
        atom ~known:first.known ("[" ^ texts (first :: rest) ^ "]")
  | Option t ->
      if Pick.chance r 0.25 then atom ~known:false "None"
      else
        let x = sub ~known t in
        atom ~known:x.known ("Some(" ^ x.text ^ ")")
  | Map (_, v) ->
      if Pick.chance r 0.7 then atom ~known:false "Map.new()"
      else atom ~known:false ("Map.with_default(" ^ (sub v).text ^ ")")
  | Named name -> (
      match decl b name with
      | Record fields ->
          let inits = List.map (fun (f, t) -> f ^ ": " ^ (sub t).text) fields in
          atom (name ^ " { " ^ String.concat ", " inits ^ " }")
      | Variants cases ->
          let case, payload = Pick.one r cases in
          if payload = [] then atom case
          else atom (call_text case (List.map (fun t -> (sub t).text) payload)))
