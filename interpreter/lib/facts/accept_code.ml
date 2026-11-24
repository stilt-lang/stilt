(* The words of facts.acceptance-places and facts.known-signs that read code alone: places, what a test
   compares and the facts each test gives, the keys of facts.keys, the literals
   and constants of facts.terms, and the code that can't complete. *)

open Tast
module T = Types

type num = { neg : bool; mag : int64 }

let num_of_literal text = { neg = false; mag = Ints.of_literal text }
let negate n = if n.mag = 0L then n else { n with neg = not n.neg }

let compare_num a b =
  match (a.neg, b.neg) with
  | false, false -> Int64.unsigned_compare a.mag b.mag
  | true, true -> Int64.unsigned_compare b.mag a.mag
  | false, true -> 1
  | true, false -> -1

let zero = { neg = false; mag = 0L }
let sign n = compare_num n zero

type place = { root : int; fields : string list }
type term = Name of int | Num of num | Len of place | Other

type key =
  | Key_name of int
  | Key_int of num
  | Key_str of string
  | Key_bool of bool

type cmp = Lt | Le | Gt | Ge | Eq | Ne

type atom =
  | Cmp of term * cmp * term
  | Non_empty of place
  | Contains of place * key

type reader = { constant : expr -> num option; whens : (int, unit) Hashtbl.t }

let cmp_of : Ast.binary -> cmp option = function
  | Lt -> Some Lt
  | Le -> Some Le
  | Gt -> Some Gt
  | Ge -> Some Ge
  | Eq -> Some Eq
  | Ne -> Some Ne
  | _ -> None

let negated = function
  | Lt -> Ge
  | Le -> Gt
  | Gt -> Le
  | Ge -> Lt
  | Eq -> Ne
  | Ne -> Eq

let mirrored = function
  | Lt -> Gt
  | Le -> Ge
  | Gt -> Lt
  | Ge -> Le
  | (Eq | Ne) as op -> op

let compares atom a op b =
  match atom with
  | Cmp (x, o, y) ->
      (x = a && o = op && y = b) || (x = b && o = mirrored op && y = a)
  | _ -> false

let is_int ty =
  match T.numeric_name ty with
  | Some name -> List.mem name T.integer_types
  | None -> false

(* effects.panicking-operations: whether dividing [a] by [b] can panic, an integer division
   whose divisor isn't written as an integer literal other than zero. *)
let divides (a : expr) (b : expr) =
  is_int a.ty
  &&
  match b.desc with
  | Int text | Unary (Neg, { desc = Int text; _ }) ->
      Literal.int_canonical text = ""
  | _ -> true

let is_con name ty =
  match T.resolve ty with Con (i, _) -> i = T.prelude_item name | _ -> false

let is_map = is_con "Map"
let is_list = is_con "List"
let is_sequence ty = is_list ty || Option.is_some (Check_arrays.parts ty)

let rec unwrap (e : expr) =
  match e.desc with Comptime x | Instantiate (x, _) -> unwrap x | _ -> e

let is_when r (v : Hir.var) = Hashtbl.mem r.whens v.id

let rec place r (e : expr) =
  match e.desc with
  | Local v when not (is_when r v) -> Some { root = v.id; fields = [] }
  | Field (base, name) ->
      Option.map
        (fun p -> { p with fields = p.fields @ [ name ] })
        (place r base)
  | _ -> None

let binding r (e : expr) =
  match e.desc with Local v when not (is_when r v) -> Some v | _ -> None

let name r (e : expr) = if is_int e.ty then binding r e else None

let number r (e : expr) =
  if not (is_int e.ty) then None
  else
    match e.desc with
    | Int text -> Some (num_of_literal text)
    | Unary (Neg, { desc = Int text; _ }) -> Some (negate (num_of_literal text))
    | Constant _ | Member_constant _ -> r.constant e
    | _ -> None

let method_name : callee -> string option = function
  | Member (_, name) | Trait_method (_, name, _) -> Some name
  | _ -> None

let is_map_method name : callee -> bool = function
  | Member (owner, n) -> owner = T.prelude_item "Map" && n = name
  | _ -> false

let len_of r (e : expr) =
  match e.desc with
  | Call (c, _, [ a ], _) when method_name c = Some "len" -> place r a.value
  | _ -> None

let term r e =
  match (name r e, number r e, len_of r e) with
  | Some v, _, _ -> Name v.id
  | None, Some n, _ -> Num n
  | None, None, Some p -> Len p
  | None, None, None -> Other

let key r (e : expr) =
  match e.desc with
  | Local v when not (is_when r v) -> Some (Key_name v.id)
  | Int text -> Some (Key_int (num_of_literal text))
  | Str s -> Some (Key_str s)
  | Bool b -> Some (Key_bool b)
  | _ -> None

let contains r (e : expr) =
  match e.desc with
  | Call (c, _, [ m; k ], _) when is_map_method "contains" c -> (
      match (place r m.value, key r k.value) with
      | Some m, Some k -> Some (m, k)
      | _ -> None)
  | _ -> None

(* The facts a condition gives where it is true, or where it is false: each
   conjunct of its [&&] chain, and for its negation each disjunct's of its
   [||] chain, read through [!]. *)
let rec gives r (c : expr) positive =
  match c.desc with
  | Binary (And, a, b) when positive -> gives r a true @ gives r b true
  | Binary (Or, a, b) when not positive -> gives r a false @ gives r b false
  | Unary (Not, a) -> gives r a (not positive)
  | Binary (op, a, b) -> (
      match cmp_of op with
      | Some op ->
          let op = if positive then op else negated op in
          [ Cmp (term r a, op, term r b) ]
      | None -> [])
  | Call (callee, _, [ a ], _)
    when method_name callee = Some "is_empty" && not positive ->
      Option.fold ~none:[] ~some:(fun p -> [ Non_empty p ]) (place r a.value)
  | Call _ when positive ->
      Option.fold ~none:[]
        ~some:(fun (m, k) -> [ Contains (m, k) ])
        (contains r c)
  | Comptime x -> gives r x positive
  | _ -> []

(* The store of a key that a statement is, [m[k] = v] or [m.insert(k, v)]. *)
let stored r (s : stmt) =
  match s.stmt with
  | Assign (None, { desc = Index (m, k); _ }, _) when is_map m.ty -> (
      match (place r m, key r k) with
      | Some m, Some k -> Some (m, k)
      | _ -> None)
  | Expr { desc = Call (c, _, [ m; k; _ ], _); _ } when is_map_method "insert" c
    -> (
      match (place r m.value, key r k.value) with
      | Some m, Some k -> Some (m, k)
      | _ -> None)
  | _ -> None

(* The key that an [if !m.contains(k) { …; m[k] = v }] statement stores. *)
let stored_if_missing r (s : stmt) =
  match s.stmt with
  | Expr e -> (
      match (unwrap e).desc with
      | If ({ desc = Unary (Not, inner); _ }, then_, _) when then_ <> [] -> (
          match
            (contains r inner, stored r (List.nth then_ (List.length then_ - 1)))
          with
          | Some tested, Some store when tested = store -> Some tested
          | _ -> None)
      | _ -> None)
  | _ -> None

(* Whether code can't complete: each of its paths ends in [return], [break],
   [continue], [raise] or a call of type [Never]. *)
let rec ends_block (b : block) =
  match List.rev b with { stmt = Expr e; _ } :: _ -> ends e | _ -> false

and ends (e : expr) =
  match e.desc with
  | Return _ | Raise _ | Break | Continue -> true
  | Call _ | Call_value _ | Project _ -> is_con "Never" e.ty
  | Block b -> ends_block b
  | If (_, then_, Some alt) | If_let (_, _, then_, Some alt) ->
      ends_block then_ && ends alt
  | Match (_, arms) ->
      arms <> [] && List.for_all (fun (a : arm) -> ends a.body) arms
  | Comptime x -> ends x
  | _ -> false
