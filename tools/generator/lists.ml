(* The forms that make a list: the methods of other lists, the pieces of a
   string, and lists of pairs. *)

open Code
open Context
open Ty

(* The fields of type [t] of the records that hold no map, as the key paths
   [.f] that read them, each with its record's type. *)
let key_paths decls t =
  List.concat_map
    (fun (name, dcl) ->
      match dcl with
      | Record fields when not (has_map decls (Named name)) ->
          List.filter_map
            (fun (f, ft) -> if ft = t then Some (Named name, "." ^ f) else None)
            fields
      | _ -> [])
    decls

(* Lists of [t] made by a method of another list. *)
let list_methods expr b sc ~depth t =
  let r = b.p.r in
  let d = depth - 1 in
  let source () = expr b sc ~depth:d ~known:true (List t) in
  let other () = random_ty b.p ~maps:false 1 in
  let fixable = not (has_map b.p.decls t) in
  let key_paths = key_paths b.p.decls t in
  [
    ( (if fixable then 3 else 0),
      fun () ->
        let u = other () in
        let xs = expr b sc ~depth:d ~known:true (List u) in
        method_on xs "map"
          [ Closures.closure expr b sc ~depth:d ~known:true u t ] );
    ( 2,
      fun () ->
        method_on (source ()) "filter"
          [ Closures.closure expr b sc ~depth:d t Bool ] );
    ( 2,
      fun () ->
        let xs = source () in
        Pick.run r
          [
            (1, fun () -> method_on xs "reversed" []);
            ( 1,
              fun () ->
                method_on xs
                  (Pick.one r [ "take"; "skip"; "take_last"; "skip_last" ])
                  [ string_of_int (Pick.between r 0 4) ] );
            ( 1,
              fun () ->
                method_on xs "concat"
                  [ (expr b sc ~depth:d ~known:false (List t)).text ] );
          ] );
    ( (if Ty.ordered ~decls:b.p.decls t then 1 else 0),
      fun () ->
        method_on (source ())
          (Pick.one r [ "sorted"; "sorted_desc"; "deduped" ])
          [] );
    ( 1,
      fun () ->
        let key = leaf_ty r in
        method_on (source ())
          (Pick.one r [ "sorted_by"; "sorted_desc_by" ])
          [ Closures.closure expr b sc ~depth:d ~known:true t key ] );
    ( (if fixable then 1 else 0),
      fun () ->
        let u = other () in
        let xs = expr b sc ~depth:d ~known:true (List u) in
        method_on xs "filter_map"
          [ Closures.closure expr b sc ~depth:d ~known:true u (Option t) ] );
    ( (if key_paths = [] then 0 else 2),
      fun () ->
        let u, path = Pick.one r key_paths in
        method_on (expr b sc ~depth:d ~known:true (List u)) "map" [ path ] );
  ]

(* Lists of the pieces of a string: substrings, characters, lines, or bytes. *)
let pieces expr b sc ~depth t =
  let r = b.p.r in
  let d = depth - 1 in
  [
    ( (if t = Str then 2 else 0),
      fun () ->
        let s = expr b sc ~depth:d ~known:true Str in
        Pick.run r
          [
            (2, fun () -> method_on s "split" [ Lit.string r ]);
            (1, fun () -> method_on s "chars" []);
            (1, fun () -> method_on s "lines" []);
            (1, fun () -> method_on s "split_whitespace" []);
          ] );
    ( (if t = Int U8 then 1 else 0),
      fun () -> method_on (expr b sc ~depth:d ~known:true Str) "bytes" [] );
  ]

(* Lists of pairs: a list enumerated, or two lists zipped. *)
let pairs expr b sc ~depth t =
  let r = b.p.r in
  let d = depth - 1 in
  match t with
  | Tuple [ Int I64; u ] when not (has_map b.p.decls u) ->
      [
        ( 1,
          fun () ->
            method_on
              (expr b sc ~depth:d ~known:true (List u))
              "enumerate"
              [ string_of_int (Pick.between r 0 2) ] );
      ]
  | Tuple [ x; y ] when not (has_map b.p.decls t) ->
      [
        ( 1,
          fun () ->
            (* [zip]'s parameter is generic, so its argument fixes its own
               type. *)
            method_on
              (expr b sc ~depth:d ~known:true (List x))
              "zip"
              [ (expr b sc ~depth:d ~known:true (List y)).text ] );
      ]
  | _ -> []

let list_ops expr b sc ~depth t =
  list_methods expr b sc ~depth t
  @ pieces expr b sc ~depth t @ pairs expr b sc ~depth t
