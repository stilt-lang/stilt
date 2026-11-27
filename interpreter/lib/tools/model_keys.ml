(* A map whose keys have an [Eq] and a [Hash] that the program writes, at the key type or at a
   part of it (traits.hash-follows-written-eq): the calculus finds a key only by its own
   comparison, so the export writes such a map as the list of its entries in insertion order
   (std.maps), each with its key's hash, and each function that finds a key as a function of
   its own, which calls the key type's [hash] once, on the key, and then its [eq] on each
   stored key of the same hash, in insertion order, until one returns [true], the key the
   receiver and the stored key the argument (std.finding-keys). *)

open Model_json
open Model_types
open Model_ops
open Model_forms
open Model_code

let entry_ty k v = Types.Tuple [ u64; k; v ]
let repr k v = Types.Con (list_item, [ entry_ty k v ])
let hash_of e = field_e e "0"
let key_of e = field_e e "1"
let value_of e = field_e e "2"
let option_ty v = Types.Con (option_item, [ v ])

(* The name of the export's function [what] for maps of [k] to [v]. *)
let name cx what k v =
  Printf.sprintf "std.prelude.Map<%s, %s>.%s"
    (to_string (ty cx k))
    (to_string (ty cx v))
    what

(* The position of the entry of [key] in the map [m], or [-1]: the first stored key, in
   insertion order, of the hash [h] that [eq] finds equal to [key]. *)
let find (at : at) cx k v m key h =
  let key_name = name cx "find" k v in
  declare cx key_name
    [ ("m", repr k v); ("k", k); ("h", u64) ]
    i64
    (fun () ->
      let stored = tag "index" [ var_e "m"; var_e "i" ] in
      let same =
        and_e
          (binary Eq u64 u64 (hash_of stored) (var_e "h"))
          (at Eq k [ var_e "k"; key_of stored ])
      in
      let unfound = binary Lt i64 i64 (var_e "r") (int 0) in
      let below = binary Lt i64 i64 (var_e "i") (list_len (var_e "m")) in
      var_in cx "r" i64 (int (-1))
        (var_in cx "i" i64 (int 0)
           (tag "seq"
              [
                tag "while"
                  [
                    and_e unfound below;
                    tag "seq" [ when_e same (assign "r" (var_e "i")); incr "i" ];
                  ];
                var_e "r";
              ])));
  helper_call cx key_name [ m; key; h ] i64

(* A function of the export's on [m] and [k], its body given the key's hash and its
   entry's position, bound as [h] and [p]: [k]'s [hash] is called once, on [k]. *)
let finding (at : at) cx what k v extra result body =
  let key_name = name cx what k v in
  declare cx key_name
    ([ ("m", repr k v); ("k", k) ] @ extra)
    result
    (fun () ->
      let_e cx "h" u64
        (at Hash k [ var_e "k" ])
        (let_e cx "p" i64
           (find at cx k v (var_e "m") (var_e "k") (var_e "h"))
           (body ())));
  key_name

let found = binary Ge i64 i64 (var_e "p") (int 0)
let stored_entry = tag "index" [ var_e "m"; var_e "p" ]

(* [m[k]]: the value of [k], or a panic with [missing-key] when it has no entry (std.maps),
   the panic of the calculus's own map, empty, at [()]. *)
let index (at : at) cx k v m key =
  let missing = map_op "index" [ map_op "new" []; unit_e ] in
  let f =
    finding at cx "index" k v [] v (fun () ->
        tag "if" [ found; ty cx v; value_of stored_entry; missing ])
  in
  helper_call cx f [ m; key ] v

(* [m.insert(k, x)] and [m[k] = x]: the map with [x] the value of [k], a key it finds
   keeping the stored key and its position, and any other going to the end (std.maps). *)
let insert (at : at) cx k v m key x =
  let f =
    finding at cx "insert" k v
      [ ("x", v) ]
      (repr k v)
      (fun () ->
        let entry = op (Str "tuple") [ var_e "h"; var_e "k"; var_e "x" ] in
        let set =
          var_in cx "n" (repr k v) (var_e "m")
            (tag "seq"
               [
                 tag "assign"
                   [
                     Arr
                       [
                         Str "n";
                         Arr
                           [
                             tag "index" [ var_e "p" ]; tag "field" [ Str "2" ];
                           ];
                       ];
                     var_e "x";
                   ];
                 var_e "n";
               ])
        in
        tag "if"
          [
            found;
            ty cx (repr k v);
            set;
            op (tag "list" [ Str "push" ]) [ var_e "m"; entry ];
          ])
  in
  helper_call cx f [ m; key; x ] (repr k v)

(* [m.contains(k)], [m.get_or(k, d)] and [m.get(k)]: whether [k] has an entry, its value or
   [d], and [Some] of its value or [None] (std.maps). *)
let contains (at : at) cx k v m key =
  let f = finding at cx "contains" k v [] bool_ty (fun () -> found) in
  helper_call cx f [ m; key ] bool_ty

let get_or (at : at) cx k v m key d =
  let f =
    finding at cx "get_or" k v
      [ ("d", v) ]
      v
      (fun () -> tag "if" [ found; ty cx v; value_of stored_entry; var_e "d" ])
  in
  helper_call cx f [ m; key; d ] v

let get (at : at) cx k v m key =
  let some = option cx (option_ty v) "Some" [ value_of stored_entry ] in
  let f =
    finding at cx "get" k v [] (option_ty v) (fun () ->
        tag "if"
          [
            found; ty cx (option_ty v); some; option cx (option_ty v) "None" [];
          ])
  in
  helper_call cx f [ m; key ] (option_ty v)

(* [m.remove(k)]: the map without the entry of [k], and [Some] of its value, or the map as
   it was and [None] when it has no entry (std.maps), as a pair. *)
let remove (at : at) cx k v m key =
  let pair = Types.Tuple [ repr k v; option_ty v ] in
  let f =
    finding at cx "remove" k v [] pair (fun () ->
        let without =
          op (tag "list" [ Str "removeAt" ]) [ var_e "m"; var_e "p" ]
        in
        let some = option cx (option_ty v) "Some" [ value_of stored_entry ] in
        tag "if"
          [
            found;
            ty cx pair;
            op (Str "tuple") [ without; some ];
            op (Str "tuple") [ var_e "m"; option cx (option_ty v) "None" [] ];
          ])
  in
  helper_call cx f [ m; key ] pair

(* The list of what [part] gives of each entry of [m], in insertion order: [entries()],
   [keys()] and [values()], and what a [for] over the map iterates (std.maps). *)
let listed cx what k v elem part m =
  let key_name = name cx what k v in
  let elems = Types.Con (list_item, [ elem ]) in
  declare cx key_name
    [ ("m", repr k v) ]
    elems
    (fun () ->
      let push =
        assign "out"
          (op (tag "list" [ Str "push" ]) [ var_e "out"; part (var_e "e") ])
      in
      var_in cx "out" elems
        (tag "list" [ ty cx elem; Arr [] ])
        (tag "seq"
           [
             tag "for" [ Str "e"; ty cx (entry_ty k v); var_e "m"; push ];
             var_e "out";
           ]));
  helper_call cx key_name [ m ] elems

let entries cx k v m =
  listed cx "entries" k v
    (Types.Tuple [ k; v ])
    (fun e -> op (Str "tuple") [ key_of e; value_of e ])
    m

let keys cx k v m = listed cx "keys" k v k key_of m
let values cx k v m = listed cx "values" k v v value_of m

(* traits.map-equality: maps of different lengths are unequal, and otherwise each key of
   the first, in insertion order, is found in the second, by its stored hash, and the two
   values compared with [eq], stopping at the first difference. *)
let equal (at : at) cx k v a b =
  let e = var_e "entry" in
  let p = find at cx k v b (key_of e) (hash_of e) in
  let differs =
    tag "if"
      [
        binary Lt i64 i64 (var_e "q") (int 0);
        Str "bool";
        true_e;
        not_e (at Eq v [ value_of e; value_of (tag "index" [ b; var_e "q" ]) ]);
      ]
  in
  let step = let_e cx "q" i64 p (when_e differs (assign "r" false_e)) in
  tag "if"
    [
      binary Ne i64 i64 (list_len a) (list_len b);
      Str "bool";
      false_e;
      var_in cx "r" bool_ty true_e
        (tag "seq"
           [
             tag "for"
               [ Str "entry"; ty cx (entry_ty k v); a; when_e (var_e "r") step ];
             var_e "r";
           ]);
    ]

(* std.show-output: a map as [{k: v, …}], in insertion order. *)
let shown (at : at) cx k v a =
  let one x =
    concat
      [
        at (Show true) k [ key_of x ];
        str_lit ": ";
        at (Show true) v [ value_of x ];
      ]
  in
  joined cx (entry_ty k v) a one ("{", "}")

(* The key and value types of a map whose keys the calculus can't find, if [t] is one. *)
let keyed cx t =
  match norm t with
  | Types.Con (i, [ k; v ]) when i = map_item && not (key cx k) -> Some (k, v)
  | _ -> None
