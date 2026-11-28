(* The names, kinds and shapes of types that the export reads before it writes any type:
   what the model lacks raises [Outside], and [Model_types] includes all of it. *)

open Model_json

exception Outside of string

let outside fmt = Printf.ksprintf (fun s -> raise (Outside s)) fmt
let item_name (i : Hir.item) = i.home ^ "." ^ i.name

(* The names of a [when] written as another of its names, when their handles reach one
   value, whose place both stand for (shared.names-that-may-be-one-place). *)
let aliases : (int * Hir.var) list ref = ref []

let var_name (v : Hir.var) =
  let v = Option.value (List.assoc_opt v.id !aliases) ~default:v in
  v.name ^ "/" ^ string_of_int v.id

(* A type resolved. *)
let norm t = Types.resolve t

(* The native type [Array<T, n>] of std.array, which the calculus declares as a record named
   by its own text, of one field, [[]], the list of its elements (formal/Stilt/Arrays.lean,
   generics.arrays). *)
let array_item = { Hir.home = "std.array"; name = "Array" }

(* The field of an array's record that holds its elements, a name no field written has. *)
let array_field = "[]"

let is_array t =
  match norm t with Con (i, [ _; _ ]) -> i = array_item | _ -> false

(* A record the calculus declares as the program writes it: the program's own, and the
   library's but [Set], which the calculus has as a type of its own (std.sets). *)
let declared_record (i : Hir.item) =
  not (i.home = "std.prelude" && i.name = "Set")

let int_kind t =
  match norm t with
  | Con ({ home = "std.prelude"; name }, [])
    when List.mem name Types.integer_types ->
      Some name
  | _ -> None

let float_kind t =
  match norm t with
  | Con ({ home = "std.prelude"; name = ("f32" | "f64") as name }, []) ->
      Some name
  | _ -> None

let elem t =
  match norm t with
  | Con ({ home = "std.prelude"; name = "List" }, [ e ]) -> e
  | Con ({ home = "std.array"; name = "Array" }, [ e; _ ]) -> e
  | _ -> outside "an iteration over something other than a list"

(* Whether the calculus's row holds [io], and its error type: code that performs [io], or
   an effect, whose handlers' bodies may perform [io] wherever the performance is
   (handlers.handler-types). *)
let flat (r : Types.row) =
  let r = Types.row_contents r in
  (match r.tail with Row_params _ -> outside "a row parameter" | _ -> ());
  (r.io || r.effects <> [], r.raise)

let async_item = { Hir.home = "std.prelude"; name = "async" }
let mode : Ast.mode -> t = function Let -> Str "let" | Inout -> Str "inout"
let args_of t = match norm t with Types.Con (_, args) -> args | _ -> []

(* The part of a view type: [T] for [View<T>]. *)
let viewed t =
  match norm t with
  | Types.Con ({ home = "std.view"; name = "View" }, [ u ]) -> Some u
  | _ -> None
