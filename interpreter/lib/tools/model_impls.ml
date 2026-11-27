(* Operators, splices, calls and sorts through the impls of the prelude's traits, written or
   structural (traits.operators, traits.structural-impls and std.lists). *)

open Model_json
open Model_types
open Model_ops
open Model_forms
open Model_code
open Model_composed

(* Whether the operator [b] on values of type [t] calls an impl that the program writes,
   at [t] or at a part of it: [==] and [!=] through [Eq], the others through [Ord]. *)
let through_impls cx (b : Ast.binary) t =
  match b with
  | Eq | Ne -> not (native cx Eq t)
  | Lt | Le | Gt | Ge -> not (native cx Compare t)
  | _ -> false

(* [x == y] is [Eq.eq(x, y)], and [x < y] tests the [Ordering] that [Ord.compare(x, y)]
   gives (traits.operators), [x] and [y] each evaluated once, in order. *)
let binary cx (b : Ast.binary) t x y =
  let is c = same_ordering cx (at cx Compare t [ x; y ]) c in
  match b with
  | Eq -> at cx Eq t [ x; y ]
  | Ne -> not_e (at cx Eq t [ x; y ])
  | Lt -> is "Less"
  | Gt -> is "Greater"
  | Le -> not_e (is "Greater")
  | _ -> not_e (is "Less")

(* A splice's text: by the impl of [Show] that the program writes for its type, or as the
   prelude shows it, around the impls the program writes for its parts (traits.show). *)
let shown cx t v = at cx (Show false) t [ v ]

(* A call of a prelude trait's method at a [Self] whose impl the program doesn't write:
   the structural impl's, or the built-in one's (traits.structural-calls). *)
let structural_call cx (t : Hir.item) name self args =
  match (t.name, name) with
  | "Eq", "eq" -> at cx Eq self args
  | "Ord", "compare" -> at cx Compare self args
  | "Hash", "hash" -> at cx Hash self args
  | "Show", "show" -> at cx (Show false) self args
  | "Show", "show_nested" -> at cx (Show true) self args
  | _ -> outside "the method %s.%s" (item_name t) name

(* The position [p] that the key [ks[i]] takes in [order], the positions of the keys before
   it sorted: after each key that it doesn't come before. *)
let inserted cx ~descending k =
  let at_ks v = tag "index" [ var_e "ks"; v ] in
  let before_p = Model_ops.binary Sub i64 i64 (var_e "p") (int 1) in
  let after = if descending then "Less" else "Greater" in
  let moves =
    and_e
      (Model_ops.binary Gt i64 i64 (var_e "p") (int 0))
      (same_ordering cx
         (at cx Compare k
            [
              at_ks (tag "index" [ var_e "order"; before_p ]); at_ks (var_e "i");
            ])
         after)
  in
  var_in cx "p" i64
    (list_len (var_e "order"))
    (tag "seq"
       [
         tag "while" [ moves; assign "p" before_p ];
         assign "order"
           (op
              (tag "list" [ Str "insert" ])
              [ var_e "order"; var_e "p"; var_e "i" ]);
       ])

(* The stable sort of the list [xs] by its keys [ks], of type [k], by [Ord.compare],
   ascending or descending (std.lists): each key inserted after those before it that it
   doesn't come before, which keeps equal keys in their order. *)
let sorted_by_keys cx ~descending k t ks xs =
  let key =
    Printf.sprintf "std.prelude.sorted%s by %s of %s"
      (if descending then "_desc" else "")
      (to_string (ty cx k))
      (to_string (ty cx t))
  in
  let ts = Types.Con (list_item, [ t ]) in
  let push =
    assign "out"
      (op
         (tag "list" [ Str "push" ])
         [ var_e "out"; tag "index" [ var_e "xs"; var_e "j" ] ])
  in
  let body () =
    var_in cx "order"
      (Types.Con (list_item, [ i64 ]))
      (tag "list" [ ty cx i64; Arr [] ])
      (var_in cx "i" i64 (int 0)
         (tag "seq"
            [
              tag "while"
                [
                  Model_ops.binary Lt i64 i64 (var_e "i")
                    (list_len (var_e "ks"));
                  tag "seq" [ inserted cx ~descending k; incr "i" ];
                ];
              var_in cx "out" ts
                (tag "list" [ ty cx t; Arr [] ])
                (tag "seq"
                   [
                     tag "for" [ Str "j"; ty cx i64; var_e "order"; push ];
                     var_e "out";
                   ]);
            ]))
  in
  declare cx key [ ("ks", Types.Con (list_item, [ k ])); ("xs", ts) ] ts body;
  helper_call cx key [ ks; xs ] ts

(* Whether the prelude's [Ord] at [t] is the calculus's structural order. *)
let native_order cx t = native cx Compare t
