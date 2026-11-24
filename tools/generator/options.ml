(* The forms that make an [Option]: lookups, the methods of options, fields
   read through an option, and conversions that can fail. *)

open Code
open Context
open Ty

(* Records with a field of type [t] or [Option<t>], which a field access
   reads through an [Option] of the record. A field whose type is an
   [Option] isn't wrapped again (types.fields-through-option). *)
let through decls t =
  List.concat_map
    (fun (name, dcl) ->
      match dcl with
      | Record fields when not (has_map decls (Named name)) ->
          List.filter_map
            (fun (f, ft) ->
              let wrapped = match t with Option _ -> false | _ -> true in
              if (ft = t && wrapped) || ft = Option t then Some (Named name, f)
              else None)
            fields
      | _ -> [])
    decls

(* Options of [t] made by a lookup in a list, by a method of another option,
   or by reading a field through an option. *)
let lookups expr b sc ~depth t =
  let r = b.p.r in
  let d = depth - 1 in
  let list () = expr b sc ~depth:d ~known:true (List t) in
  let through = through b.p.decls t in
  let fixable = not (has_map b.p.decls t) in
  [
    ( (if fixable then 3 else 0),
      fun () ->
        Pick.run r
          [
            ( 2,
              fun () -> method_on (list ()) (Pick.one r [ "first"; "last" ]) []
            );
            ( 1,
              fun () ->
                method_on (list ()) "get"
                  [ (expr b sc ~depth:d ~known:false (Int I64)).text ] );
            ( 1,
              fun () ->
                method_on (list ()) "find"
                  [ Closures.closure expr b sc ~depth:d t Bool ] );
          ] );
    ( (if fixable then 2 else 0),
      fun () ->
        let u = random_ty b.p ~maps:false 1 in
        let o = expr b sc ~depth:d ~known:true (Option u) in
        method_on o "map"
          [ Closures.closure expr b sc ~depth:d ~known:true u t ] );
    ( (if fixable then 1 else 0),
      fun () ->
        let o = expr b sc ~depth:d ~known:true (Option t) in
        method_on o "filter" [ Closures.closure expr b sc ~depth:d t Bool ] );
    ( (if through = [] then 0 else 3),
      fun () ->
        let owner, f = Pick.one r through in
        let o = expr b sc ~depth:d ~known:true (Option owner) in
        atom (operand o ^ "." ^ f) );
  ]

(* Options of [t] made by a conversion that can fail, or a search. *)
let conversions expr b sc ~depth t =
  let r = b.p.r in
  let d = depth - 1 in
  let narrower =
    match t with
    | Int k -> List.filter (fun j -> not (widens ~from:j ~into:k)) int_kinds
    | _ -> []
  in
  [
    ( (match t with Int _ | Float _ -> 1 | _ -> 0),
      fun () ->
        let s =
          if Pick.chance r 0.5 then
            atom (Printf.sprintf "\"%d\"" (Pick.below r 300))
          else expr b sc ~depth:d ~known:true Str
        in
        method_on s ("to_" ^ to_string t) [] );
    ( (if narrower = [] then 0 else 1),
      fun () ->
        let x = expr b sc ~depth:d ~known:true (Int (Pick.one r narrower)) in
        method_on x ("to_" ^ to_string t) [] );
    ( (if t = Int I64 then 1 else 0),
      fun () ->
        method_on (expr b sc ~depth:d ~known:true Str) "find" [ Lit.string r ]
    );
  ]

let option_ops expr b sc ~depth t =
  lookups expr b sc ~depth t @ conversions expr b sc ~depth t
