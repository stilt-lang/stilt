(* Types at run time: the types of a body with its type arguments, the numeric
   types, the components of compound values, and the literals whose values
   their types decide. *)

open Tast
open Value
open Eval_state
module T = Types

(* Types *)

let concrete fr ty = match fr.tenv with [] -> ty | tenv -> T.subst tenv [] ty

let concrete_callee fr = function
  | Trait_method (trait, name, ty) -> Trait_method (trait, name, concrete fr ty)
  | (Function _ | Member _ | Operation _) as c -> c

(* generics.value-parameters-in-body: the value that the frame's type arguments give the
   value parameter [v], of type [ty]. *)
let value_param fr (v : Hir.var) ty =
  match (concrete fr (T.Param v), T.numeric_name ty) with
  | T.Value "true", None -> Bool true
  | T.Value "false", None -> Bool false
  | T.Value text, Some name -> (
      match Option.bind (Ints.of_name name) (fun k -> Ints.parse k text) with
      | Some n -> Int n
      | None -> invalid_arg "Eval_types.value_param")
  | _ -> invalid_arg "Eval_types.value_param"

type numeric = Integer of Ints.kind | Floating of bool | Not_numeric

let numeric ty =
  match T.numeric_name ty with
  | None -> Not_numeric
  | Some name -> (
      match Ints.of_name name with
      | Some k -> Integer k
      | None -> Floating (name = "f32"))

(* The parameters of a type constructor, bound to arguments. *)
let arguments_of t item args =
  match Env.type_info t.env item with
  | Some info -> List.combine info.params args
  | None -> []

(* The types of the components of a value of a type, in order. *)
let component_types t ty v =
  match (T.resolve ty, v) with
  | Tuple ts, _ -> ts
  (* records.field-order: in the alphabetical order of their names. *)
  | Record fields, _ -> List.map snd fields
  | Con (_, [ elem ]), List xs -> List.init (Vec.length xs) (fun _ -> elem)
  (* generics.array-traits: an array's elements, which a list holds. *)
  | Con ({ home = "std.array"; name = "Array" }, [ elem; _ ]), List xs ->
      List.init (Vec.length xs) (fun _ -> elem)
  | Con (item, args), Variant (variant, _) -> (
      match Env.variant t.env variant with
      | Some (_, _, payload) ->
          List.map (T.subst (arguments_of t item args) []) payload
      | None -> [])
  | Con (item, args), Record _ -> (
      match Env.type_info t.env item with
      | Some { def = Record fields; _ } ->
          List.map
            (fun (_, ty) -> T.subst (arguments_of t item args) [] ty)
            fields
      | _ -> [])
  | _ -> []

(* The components of a value, with their types. *)
let components t ty v =
  let values =
    match v with
    | Tuple xs | Variant (_, xs) -> xs
    | List xs -> Vec.to_list xs
    | Record (_, fields) -> List.map snd fields
    | Int _ | Float _ | Bool _ | Str _ | Map _ | Fn _ | Iter _ | Window _
    | Deferred _ | Handler _ | Shared _ | Meta _ ->
        []
  in
  List.combine (component_types t ty v) values

(* views.functions-of-views: a view's value is the part it views, whose type is the
   viewed type. *)
let viewed ty =
  match T.resolve ty with
  | Con ({ home = "std.view"; name = "View" }, [ t ]) -> t
  | t -> t

let key_value_types ty =
  match T.resolve ty with
  | Con (_, [ k; v ]) -> (k, v)
  | _ -> invalid_arg "Eval_types.key_value_types"

let variant_index t item =
  match Env.variant t.env item with
  | Some (_, i, _) -> i
  | None -> invalid_arg "Eval_types.variant_index"

(* Literals *)

let digit c =
  match c with
  | '0' .. '9' -> Char.code c - Char.code '0'
  | 'a' .. 'f' -> Char.code c - Char.code 'a' + 10
  | 'A' .. 'F' -> Char.code c - Char.code 'A' + 10
  | _ -> invalid_arg "Eval_types.digit"

(* An integer literal of a float type, which holds its value exactly (numbers.integer-literals), so the digits of a radix literal accumulate without rounding. *)
let float_of_int_literal text =
  let radix =
    if String.length text < 2 then 10
    else
      match String.sub text 0 2 with
      | "0x" -> 16
      | "0o" -> 8
      | "0b" -> 2
      | _ -> 10
  in
  if radix = 10 then float_of_string text
  else
    String.fold_left
      (fun x c -> (x *. float_of_int radix) +. float_of_int (digit c))
      0.0
      (String.sub text 2 (String.length text - 2))

let int_literal ty text =
  match numeric ty with
  | Integer _ -> Int (Ints.of_literal text)
  | Floating _ -> Float (float_of_int_literal text)
  | Not_numeric -> invalid_arg "Eval_types.int_literal"

(* An integer pattern's literal, whose [-] is part of it (numbers.negative-literals). *)
let pattern_literal text =
  if String.starts_with ~prefix:"-" text then
    Int64.neg (Ints.of_literal (String.sub text 1 (String.length text - 1)))
  else Ints.of_literal text

(* A literal with its sign (numbers.negative-literals). A [-] that negates its operand
   gives the same value, since the literal fits its type. *)
let negative_literal ty text =
  match int_literal ty text with
  | Int x -> Int (Int64.neg x)
  | Float x -> Float (-.x)
  | _ -> invalid_arg "Eval_types.negative_literal"

let float_literal ty text =
  match numeric ty with
  | Floating true -> Float (Floats.f32_of_decimal text)
  | Floating false | Integer _ | Not_numeric -> Float (float_of_string text)
