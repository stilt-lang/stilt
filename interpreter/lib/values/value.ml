module Imap = Map.Make (Int)
module I64map = Map.Make (Int64)

module Vec = struct
  type 'a t = { length : int; items : 'a Imap.t }

  let empty = { length = 0; items = Imap.empty }
  let length v = v.length
  let get v i = Imap.find i v.items
  let set v i x = { v with items = Imap.add i x v.items }
  let push v x = { length = v.length + 1; items = Imap.add v.length x v.items }

  let pop v =
    if v.length = 0 then None
    else
      let i = v.length - 1 in
      Some ({ length = i; items = Imap.remove i v.items }, get v i)

  let of_list xs = List.fold_left push empty xs
  let to_list v = List.map snd (Imap.bindings v.items)

  let sub v start stop =
    of_list (List.filteri (fun i _ -> i >= start && i < stop) (to_list v))

  let insert v i x =
    let before, after =
      List.partition (fun (j, _) -> j < i) (Imap.bindings v.items)
    in
    of_list (List.map snd before @ (x :: List.map snd after))

  let remove v i = of_list (List.filteri (fun j _ -> j <> i) (to_list v))
end

type value =
  | Int of int64
  | Float of float
  | Bool of bool
  | Str of string
  | Tuple of value list
  | List of value Vec.t
  | Map of dict
  | Variant of Hir.item * value list
  | Record of Hir.item * (string * value) list
  | Fn of fn
  | Iter of iter
  | Window of window
  | Deferred of deferred
  | Handler of handler
  | Shared of shared
  | Meta of Macro_values.t
      (** A value that a macro reads or writes (macros.tokens-and-code). *)

and shared = { mutable held : value }
and handler = { heffect : Hir.item; control : bool; ops : (string * fn) list }
and deferred = { compute : fn; mutable result : value option }

and window = {
  locals : (int, value) Hashtbl.t;
  root : int;
  path : step list;
  start : int;
  stop : int;
}

and step =
  | At_field of string
  | At_elem of int
  | At_key of value * Types.ty * Ast.loc

and iter =
  | Elements of value list
  | Range of int64 * int64
  | Mapped of iter * fn
  | Filtered of iter * fn
  | Taken of iter * int64
  | Skipped of iter * int64
  | Taken_while of iter * fn
  | Skipped_while of iter * fn
  | Enumerated of iter * int64
  | Zipped of iter * iter
  | Chained of iter * iter

and dict = {
  entries : (value * value) Imap.t;
  stamps : int list I64map.t;
  next : int;
  default : value option;
}

and fn =
  | Closure of closure
  | Function of Tast.callee * Types.ty list
  | Constructor of Hir.item
  | Poly of Hir.var list * fn

and closure = {
  params : Tast.pattern list;
  body : Tast.expr;
  captured : value Imap.t;
  tenv : (Hir.var * Types.ty) list;
  home : string;
}

let unit = Tuple []
let some v = Variant (Types.prelude_item "Some", [ v ])
let none = Variant (Types.prelude_item "None", [])
let option = function Some v -> some v | None -> none

module Dict = struct
  type t = dict

  let empty default =
    { entries = Imap.empty; stamps = I64map.empty; next = 0; default }

  let length d = Imap.cardinal d.entries
  let entries d = List.map snd (Imap.bindings d.entries)

  let find d ~hash ~same =
    List.find_map
      (fun stamp ->
        let k, v = Imap.find stamp d.entries in
        if same k then Some (stamp, v) else None)
      (Option.value (I64map.find_opt hash d.stamps) ~default:[])

  let set d stamp v =
    let k, _ = Imap.find stamp d.entries in
    { d with entries = Imap.add stamp (k, v) d.entries }

  let add d ~hash k v =
    let stamps = Option.value (I64map.find_opt hash d.stamps) ~default:[] in
    {
      d with
      entries = Imap.add d.next (k, v) d.entries;
      stamps = I64map.add hash (stamps @ [ d.next ]) d.stamps;
      next = d.next + 1;
    }

  let remove d ~hash stamp =
    let stamps = List.filter (( <> ) stamp) (I64map.find hash d.stamps) in
    {
      d with
      entries = Imap.remove stamp d.entries;
      stamps =
        (if stamps = [] then I64map.remove hash d.stamps
         else I64map.add hash stamps d.stamps);
    }
end

(* patterns.constants: constants have no floats or functions inside, so their
   values compare by structure. *)
let rec same a b =
  match (a, b) with
  | Int x, Int y -> x = y
  | Bool x, Bool y -> x = y
  | Str x, Str y -> x = y
  | Tuple xs, Tuple ys ->
      List.length xs = List.length ys && List.for_all2 same xs ys
  | Variant (v, xs), Variant (w, ys) ->
      v = w && List.length xs = List.length ys && List.for_all2 same xs ys
  | List xs, List ys ->
      Vec.length xs = Vec.length ys
      && List.for_all2 same (Vec.to_list xs) (Vec.to_list ys)
  | Record (r, xs), Record (s, ys) ->
      r = s && List.for_all2 (fun (_, x) (_, y) -> same x y) xs ys
  | _ -> false
