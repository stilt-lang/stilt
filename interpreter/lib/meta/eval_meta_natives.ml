(* The accessors of [std.meta] (meta.shapes, meta.fields and meta.variant-cases), all native. Each
   takes the type arguments of its impl, the shape's type [T] first, and
   performs nothing but the allocation of what it makes (meta.accessor-effects). *)

open Value
open Eval_state
open Eval_types
module T = Types
module S = Meta_shapes

let set_item = T.prelude_item "Set"

(* meta.shape-accessors: an integer's decimal text, and the integer that text writes as
   [text] would, of [T]'s range. *)
let integer name ty args =
  let k =
    match numeric ty with
    | Integer k -> k
    | _ -> invalid_arg "Eval_meta_natives.integer"
  in
  match (name, args) with
  | "text", [| _; Int x |] -> Str (Ints.to_string k x)
  | "parse", [| _; Str s |] -> (
      match Ints.parse k s with
      | Some x when Ints.to_string k x = s -> some (Int x)
      | _ -> none)
  | _ -> invalid_arg ("Eval_meta_natives.integer: " ^ name)

(* meta.shape-accessors: a value as a value of the type [U], and back: an [f32] exactly
   and rounded back as numbers.conversions rounds, a set as its elements and a map as its
   entries, in insertion order, kept by the element or key type's own [Eq]
   and [Hash]. A map made so has no default. *)
let convert t fr loc name ty args =
  let pairs d = List.map (fun (k, v) -> Tuple [ k; v ]) (Dict.entries d) in
  let filled kty xs entry =
    List.fold_left
      (fun d x ->
        let k, v = entry x in
        Eval_traits.insert t fr loc kty d k v)
      (Dict.empty None) (Vec.to_list xs)
  in
  match (name, S.case_of t.env ty, args) with
  | "get", Some (Holds ("Set", _)), [| _; Record (_, [ (_, Map d) ]) |] ->
      List (Vec.of_list (List.map fst (Dict.entries d)))
  | "get", Some (Holds ("Map", _)), [| _; Map d |] ->
      List (Vec.of_list (pairs d))
  | "make", Some (Leaf "Float"), [| _; Float x |]
    when numeric ty = Floating true ->
      Float (Floats.round32 x)
  | "make", Some (Holds ("Set", [ e ])), [| _; List xs |] ->
      Record (set_item, [ ("elements", Map (filled e xs (fun x -> (x, unit)))) ])
  | "make", Some (Holds ("Map", [ k; _ ])), [| _; List xs |] ->
      let entry = function
        | Tuple [ k; v ] -> (k, v)
        | _ -> invalid_arg "Eval_meta_natives.convert"
      in
      Map (filled k xs entry)
  | ("get" | "make"), _, [| _; v |] -> v
  | _ -> invalid_arg ("Eval_meta_natives.convert: " ^ name)

(* generics.array-sizes: an array type's size, its second argument. *)
let size ty =
  match T.resolve ty with
  | Con (_, [ _; T.Value n ]) -> Int64.of_string n
  | _ -> invalid_arg "Eval_meta_natives.size"

let sized name ty args =
  match (name, args) with
  | "get", [| _; v |] -> v
  | "make", [| _; List xs |] ->
      if Int64.of_int (Vec.length xs) = size ty then some (List xs) else none
  | "len", [| _ |] -> Int (size ty)
  | _ -> invalid_arg ("Eval_meta_natives.sized: " ^ name)

(* meta.building: a value of a tuple or a record type made of the values [f] gives
   each field, called once on each in order, at the field's type. *)
let build t fr loc ty f =
  let fields = Eval_meta.fields t ty in
  let values =
    List.mapi
      (fun i (_, fty) ->
        match Eval_targets.instantiate [ fty ] f with
        | Fn fn ->
            t.apply t fr loc
              (Eval_targets.target_of_fn t fn)
              [| Int (Int64.of_int i) |]
        | _ -> invalid_arg "Eval_meta_natives.build")
      fields
  in
  let named = List.combine (List.map fst fields) values in
  match T.resolve ty with
  | Tuple _ -> Tuple values
  | Record _ -> Record (T.anonymous, named)
  | Con (item, _) -> Record (item, named)
  | _ -> invalid_arg "Eval_meta_natives.build"

let position = function
  | Int i -> Int64.to_int i
  | _ -> invalid_arg "Eval_meta_natives.position"

let field_value v name i =
  match v with
  | Tuple xs -> List.nth xs i
  | Record (_, fields) -> List.assoc name fields
  | _ -> invalid_arg "Eval_meta_natives.field_value"

let field t name ty args =
  let fields = Eval_meta.fields t ty in
  let i = position args.(0) in
  let fname = fst (List.nth fields i) in
  match (name, args) with
  | "name", [| _ |] -> Str fname
  | "index", [| _ |] -> Int (Int64.of_int i)
  | "get", [| _; v |] -> field_value v fname i
  | _ -> invalid_arg ("Eval_meta_natives.field: " ^ name)

(* meta.variant-cases: a variant, its payload as a tuple. *)
let case t name ty args =
  let variants = Eval_meta.variants t ty in
  let i = position args.(0) in
  let item = fst (List.nth variants i) in
  match (name, args) with
  | "name", [| _ |] -> Str item.name
  | "index", [| _ |] -> Int (Int64.of_int i)
  | "get", [| _; Variant (w, xs) |] ->
      if w = item then some (Tuple xs) else none
  | "make", [| _; Tuple xs |] -> Variant (item, xs)
  | _ -> invalid_arg ("Eval_meta_natives.case: " ^ name)

let native t fr loc owner name targs args =
  let ty = concrete fr (List.hd targs) in
  match (owner, name, args) with
  | "Integer", _, _ -> integer name ty args
  | "Convert", _, _ -> convert t fr loc name ty args
  | "Sized", _, _ -> sized name ty args
  | ("Fields" | "Cases"), "len", _ ->
      let n =
        if owner = "Fields" then List.length (Eval_meta.fields t ty)
        else List.length (Eval_meta.variants t ty)
      in
      Int (Int64.of_int n)
  | "Fields", "build", [| _; f |] -> build t fr loc ty f
  | "Field", _, _ -> field t name ty args
  | "Case", _, _ -> case t name ty args
  | _ -> invalid_arg ("Eval_meta_natives.native: " ^ owner ^ "." ^ name)
