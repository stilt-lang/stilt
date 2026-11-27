(* The prelude's structural impls of [Eq], [Ord], [Hash] and [Show] at a type one of whose
   parts has an impl that the program writes (traits.structural-impls): the calculus's
   operations compare and show only values whose impls are all structural, and hash none,
   so the export writes each such impl at each type it is used at as a function of its
   own, which calls the impls of the type's components from first to last
   (traits.structural-calls). *)

open Model_json
open Model_types
open Model_ops
open Model_forms
open Model_code

(* The written impl's function that [k] calls at [t], if the program writes one for [t]'s
   head: a nested text by [show_nested] when the impl writes it, and by [show] otherwise,
   as its default does (traits.prelude-traits). *)
let written cx k t =
  match k with
  | Eq -> Model_traits.written cx eq_trait "eq" t
  | Compare -> Model_traits.written cx ord_trait "compare" t
  | Hash -> Model_traits.written cx hash_trait "hash" t
  | Show nested -> (
      let show = Model_traits.written cx show_trait "show" t in
      match (nested, Model_traits.written cx show_trait "show_nested" t) with
      | true, Some nested -> Some nested
      | _ -> show)

(* Whether the calculus's operations give [k] at [t], every impl in it structural. *)
let native cx k t =
  match k with
  | Eq -> structural_by cx "Eq" t
  | Compare -> structural_by cx "Ord" t
  | Hash -> key cx t
  | Show _ -> structural cx t

(* The constructors of each variant type that [t] holds, in declaration order, which the
   calculus's structural comparisons take (traits.structural-calls). *)
let orders cx t =
  let pair (n, cs) = Arr [ Str n; Arr (List.map (fun c -> Str c) cs) ] in
  Arr (List.map pair (ctor_orders cx t))

(* Whether [==] at [t] is an operator of its own: on the numeric types, [bool] and [str]. *)
let scalar t =
  int_kind t <> None
  || float_kind t <> None
  ||
  match norm t with
  | Types.Con ({ home = "std.prelude"; name = "bool" | "str" }, []) -> true
  | _ -> false

let set t =
  match norm t with
  | Types.Con ({ home = "std.prelude"; name = "Set" }, [ _ ]) -> true
  | _ -> false

(* [k] at [t] by the calculus's operations: [==], the structural order, a value's text,
   nested as the text of a list of it shows it, between its brackets (std.show-output), and
   a hash of [0], which every value of a type whose [Eq] is structural may have, since
   equal values have equal hashes (traits.prelude-traits) and which keys share a hash is
   unspecified (std.finding-keys). *)
let native_e cx k t xs =
  match (k, xs) with
  | Hash, [ _ ] -> int_lit u64 "0" ~negated:false
  | Eq, [ x; y ] when scalar t || is_map t || set t ->
      binary_at cx Ast.Eq t t x y
  | Eq, [ x; y ] -> op (tag "structural" [ Str "eq"; orders cx t ]) [ x; y ]
  | Compare, [ x; y ] ->
      let orders = orders cx t in
      let test c = op (tag "structural" [ Str c; orders ]) [ x; y ] in
      let o = ty cx ordering_ty in
      tag "if"
        [
          test "lt";
          o;
          ordering cx "Less";
          tag "if" [ test "gt"; o; ordering cx "Greater"; ordering cx "Equal" ];
        ]
  | Show true, [ x ] when Model_traits.holds_str cx t ->
      let s = "nested-text" in
      let listed = op (Str "showValue") [ tag "list" [ ty cx t; Arr [ x ] ] ] in
      let last = binary Sub i64 i64 (op (Str "len") [ var_e s ]) (int 1) in
      let_e cx s str_ty listed (op (Str "slice") [ var_e s; int 1; last ])
  | Show _, [ x ] -> show ~structural:true t x
  | _ -> outside "a structural impl's call"

(* The components of a tuple or of a record without an impl of [k]'s trait of its own,
   first to last, a record's in declaration order, each with how a value reaches it. *)
let components cx t =
  match norm t with
  | Types.Tuple ts -> Some (List.mapi (fun i t -> (string_of_int i, t)) ts)
  | Con (i, args) when declared_record i -> (
      match Env.type_info cx.env i with
      | Some { Env.def = Env.Record fields; _ } ->
          let sub =
            instantiated cx { key = ""; item = i; args; generic = false }
          in
          Some (List.map (fun (f, t) -> (f, sub t)) fields)
      | _ -> None)
  | _ -> None

(* The constructors of a variant type, each with its payload's types at [t]'s arguments. *)
let ctors cx t =
  match norm t with
  | Types.Con (i, args) -> (
      match Env.type_info cx.env i with
      | Some { Env.def = Env.Variants cs; _ } ->
          let sub =
            instantiated cx { key = ""; item = i; args; generic = false }
          in
          Some
            ( declared cx i args,
              List.map (fun (c, ts) -> (c, List.map sub ts)) cs )
      | _ -> None)
  | _ -> None

(* [k] at [t] on the operands [xs], each evaluated once, in order: the written impl's
   function, the calculus's operations, or the structural impl's function at [t]. *)
let rec at cx k t xs =
  match written cx k t with
  | Some target ->
      Model_traits.call_values cx target
        (List.map (fun _ -> t) xs)
        xs (result_of k)
  | None when native cx k t -> native_e cx k t xs
  | None ->
      let k = match k with Show _ -> Show false | k -> k in
      let key =
        Printf.sprintf "std.prelude.%s for %s" (name_of k) (to_string (ty cx t))
      in
      let params =
        match k with Show _ | Hash -> [ "a" ] | _ -> [ "a"; "b" ]
      in
      declare cx key
        (List.map (fun n -> (n, t)) params)
        (result_of k)
        (fun () -> body cx k t);
      helper_call cx key xs (result_of k)

and body cx k t =
  let a = var_e "a" and b = var_e "b" in
  match (components cx t, ctors cx t, norm t) with
  | Some parts, _, _ -> (
      let reach v = List.map (fun (f, t) -> (field_e v f, t)) parts in
      match k with
      | Eq -> all_equal cx (List.combine (reach a) (reach b))
      | Compare -> lexicographic cx "o" (List.combine (reach a) (reach b))
      | Hash -> hashed cx (int_lit u64 "0" ~negated:false) (reach a)
      | Show _ -> shown_parts cx t (reach a))
  | None, Some (name, cs), _ -> (
      match k with
      | Eq -> variant_eq cx name cs
      | Compare -> variant_compare cx name cs
      | Hash -> variant_hash cx name cs
      | Show _ -> variant_show cx name cs)
  | None, None, Con (i, [ e ]) when i = list_item -> list_body cx k e
  | None, None, Con (i, [ kt; v ]) when i = map_item -> (
      let at = at cx in
      match k with
      | Eq when key cx kt -> map_equal cx kt v
      | Eq -> Model_keys.equal at cx kt v a b
      | Show _ when key cx kt -> map_shown cx kt v
      | Show _ -> Model_keys.shown at cx kt v a
      | Compare | Hash -> outside "the order or the hash of a map")
  | _ -> outside "a structural impl at a type the model lacks"

(* traits.structural-calls: components compared with [eq] from first to last, stopping at
   the first unequal pair, as [&&] stops. *)
and all_equal cx pairs =
  List.fold_right
    (fun ((l, t), (r, _)) rest ->
      match rest with
      | Arr [ Str "bool"; Bool true ] -> at cx Eq t [ l; r ]
      | rest -> and_e (at cx Eq t [ l; r ]) rest)
    pairs true_e

(* traits.structural-calls: lexicographic, the first component whose [compare] isn't
   [Equal] deciding. *)
and lexicographic cx base pairs =
  let step i ((l, t), (r, _)) rest =
    let o = Printf.sprintf "%s/%d" base i in
    let_e cx o ordering_ty
      (at cx Compare t [ l; r ])
      (tag "if"
         [
           same_ordering cx (var_e o) "Equal"; ty cx ordering_ty; rest; var_e o;
         ])
  in
  List.fold_right
    (fun (i, p) rest -> step i p rest)
    (List.mapi (fun i p -> (i, p)) pairs)
    (ordering cx "Equal")

(* traits.structural-calls: hashing calls [hash] on every component, first to last, each
   hash mixed into the one before. *)
and hashed cx start parts =
  List.fold_left (fun h (v, t) -> mix h (at cx Hash t [ v ])) start parts

(* std.show-output: a tuple between [(] and [)], a 1-tuple with a trailing [,], a record
   as its unqualified name and its fields, each part nested. *)
and shown_parts cx t parts =
  let nested (v, t) = at cx (Show true) t [ v ] in
  match norm t with
  | Types.Tuple _ ->
      let close = if List.length parts = 1 then ",)" else ")" in
      concat
        ((str_lit "(" :: separated (List.map nested parts)) @ [ str_lit close ])
  | Con (i, _) when parts = [] -> str_lit (i.name ^ " {}")
  | Con (i, _) ->
      let names = Option.get (components cx t) in
      let one (f, _) p = concat [ str_lit (f ^ ": "); nested p ] in
      concat
        ((str_lit (i.name ^ " { ") :: separated (List.map2 one names parts))
        @ [ str_lit " }" ])
  | _ -> outside "a structural impl at a type the model lacks"

(* [match a { C(x/0, …) => match b { C(y/0, …) => same, _ => other }, … }]. *)
and both cx name cs result same other =
  let inner (c, ts) =
    ctor_arm name (c, ts) "x" (fun xs ->
        tag "match"
          [
            var_e "b";
            ty cx result;
            Arr
              [
                ctor_arm name (c, ts) "y" (fun ys ->
                    same (List.combine xs ts) (List.combine ys ts));
                Arr [ Str "wild"; Arr []; other ];
              ];
          ])
  in
  tag "match" [ var_e "a"; ty cx result; Arr (List.map inner cs) ]

(* traits.structural-calls: different variants are unequal without comparing any payload. *)
and variant_eq cx name cs =
  both cx name cs bool_ty
    (fun xs ys -> all_equal cx (List.combine xs ys))
    false_e

(* traits.structural-calls: variants compare first by their order in the type's
   declaration, then by payload. *)
and variant_compare cx name cs =
  let index v =
    tag "match"
      [
        v;
        ty cx i64;
        Arr
          (List.mapi
             (fun n (c, ts) -> ctor_arm name (c, ts) "z" (fun _ -> int n))
             cs);
      ]
  in
  let payloads =
    both cx name cs ordering_ty
      (fun xs ys -> lexicographic cx "o" (List.combine xs ys))
      (ordering cx "Equal")
  in
  let_e cx "ia" i64
    (index (var_e "a"))
    (let_e cx "ib" i64
       (index (var_e "b"))
       (native_ordering cx (var_e "ia") (var_e "ib") payloads))

(* traits.structural-calls: a variant's hash is its position's, its payload's mixed in. *)
and variant_hash cx name cs =
  let one n (c, ts) =
    ctor_arm name (c, ts) "x" (fun xs ->
        hashed cx
          (int_lit u64 (string_of_int n) ~negated:false)
          (List.combine xs ts))
  in
  tag "match" [ var_e "a"; ty cx u64; Arr (List.mapi one cs) ]

(* std.show-output: a variant as its name, and its payload between [(] and [)]. *)
and variant_show cx name cs =
  let one (c, ts) =
    ctor_arm name (c, ts) "x" (fun xs ->
        match ts with
        | [] -> str_lit c
        | _ ->
            let parts =
              List.map2 (fun x t -> at cx (Show true) t [ x ]) xs ts
            in
            concat ((str_lit (c ^ "(") :: separated parts) @ [ str_lit ")" ]))
  in
  tag "match" [ var_e "a"; Str "str"; Arr (List.map one cs) ]

(* traits.structural-calls: lists of different lengths are unequal without comparing any
   element, and are otherwise compared element by element, stopping at the first unequal
   pair; in order, the first pair that differs decides, and a list that runs out first is
   the lesser; hashing hashes every element; std.show-output: a list as its elements
   between [[] and []]. *)
and list_body cx k e =
  let a = var_e "a" and b = var_e "b" in
  let at_i v = tag "index" [ v; var_e "i" ] in
  let below n = binary Lt i64 i64 (var_e "i") n in
  let loop cond step = tag "while" [ cond; tag "seq" [ step; incr "i" ] ] in
  let counted init cond step result =
    init (var_in cx "i" i64 (int 0) (tag "seq" [ loop cond step; result ]))
  in
  match k with
  | Eq ->
      let step =
        when_e (not_e (at cx Eq e [ at_i a; at_i b ])) (assign "r" false_e)
      in
      tag "if"
        [
          binary Ne i64 i64 (list_len a) (list_len b);
          Str "bool";
          false_e;
          counted
            (var_in cx "r" bool_ty true_e)
            (and_e (var_e "r") (below (list_len a)))
            step (var_e "r");
        ]
  | Compare ->
      let cond =
        and_e
          (same_ordering cx (var_e "o") "Equal")
          (and_e (below (list_len a)) (below (list_len b)))
      in
      let by_length =
        native_ordering cx (list_len a) (list_len b) (ordering cx "Equal")
      in
      counted
        (var_in cx "o" ordering_ty (ordering cx "Equal"))
        cond
        (assign "o" (at cx Compare e [ at_i a; at_i b ]))
        (tag "if"
           [
             same_ordering cx (var_e "o") "Equal";
             ty cx ordering_ty;
             by_length;
             var_e "o";
           ])
  | Hash ->
      counted
        (var_in cx "h" u64 (int_lit u64 "0" ~negated:false))
        (below (list_len a))
        (assign "h" (mix (var_e "h") (at cx Hash e [ at_i a ])))
        (var_e "h")
  | Show _ -> joined cx e a (fun x -> at cx (Show true) e [ x ]) ("[", "]")

(* traits.map-equality, of a map whose keys the calculus finds: maps of different lengths
   are unequal, and otherwise each key of the first, in insertion order, is found in the
   second and the two values compared with [eq], stopping at the first difference. *)
and map_equal cx kt v =
  let a = var_e "a" and b = var_e "b" in
  let key = field_e (var_e "entry") "0"
  and value = field_e (var_e "entry") "1" in
  let found =
    tag "if"
      [
        map_op "contains" [ b; key ];
        Str "unit";
        when_e
          (not_e (at cx Eq v [ value; map_op "index" [ b; key ] ]))
          (assign "r" false_e);
        assign "r" false_e;
      ]
  in
  tag "if"
    [
      binary Ne i64 i64 (map_op "len" [ a ]) (map_op "len" [ b ]);
      Str "bool";
      false_e;
      var_in cx "r" bool_ty true_e
        (tag "seq"
           [
             tag "for"
               [
                 Str "entry";
                 ty cx (Types.Tuple [ kt; v ]);
                 map_op "entries" [ a ];
                 when_e (var_e "r") found;
               ];
             var_e "r";
           ]);
    ]

(* std.show-output: a map as [{k: v, …}], in insertion order. *)
and map_shown cx kt v =
  let one x =
    concat
      [
        at cx (Show true) kt [ field_e x "0" ];
        str_lit ": ";
        at cx (Show true) v [ field_e x "1" ];
      ]
  in
  joined cx
    (Types.Tuple [ kt; v ])
    (map_op "entries" [ var_e "a" ])
    one ("{", "}")
