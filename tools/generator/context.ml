(* Where code is generated: the program so far, the scope of the code, the
   budget of the body it belongs to, and the types it can name. *)

open Code
open Ty

(* Programs *)

type fn_sig = {
  fname : string;
  params : (bool * t) list;  (** Whether each one is [inout], and its type. *)
  ret : t;
  raises : bool;  (** Whether its row is [raise<Fault>]. *)
  cost : int;  (** An estimate of the steps a call takes. *)
}

type program = {
  r : Pick.t;
  mutable decls : (string * decl) list;  (** In declaration order. *)
  mutable fns : fn_sig list;  (** The functions declared so far. *)
  mutable count : int;  (** The number in the last fresh name. *)
  fault : string;  (** The error type of every function that raises. *)
  fault_variants : (string * t list) list;  (** Its variants. *)
  panics : bool;  (** Whether its arithmetic may panic. *)
  capped : bool;  (** Whether its strings and lists are capped. *)
}

let fresh p prefix =
  p.count <- p.count + 1;
  prefix ^ string_of_int p.count

(* A string or a list that an operation makes grows with its operands, so that
   a fold's accumulator, or two variables that a loop assigns from each other,
   would double on each pass. Where a program is capped, each such operation's
   result is cut. The cut takes no random choice, so a seed's program is the
   same without it but for its values. *)
let longest_str = 120
let longest_list = 16
let cap_str p c = if p.capped then atom (call_text "cap" [ c.text ]) else c

let cap_list p c =
  if p.capped then method_on c "take" [ string_of_int longest_list ] else c

(* The function that cuts a string. Its body is too short for W0302 to compare
   it with another module's (docs.body-size). Every string is ASCII, so every
   offset is on a UTF-8 boundary. *)
let cap_decl =
  Printf.sprintf "fn cap(s: str) -> str { s.slice(0, s.len().min(%d)) }"
    longest_str

(* Whether [text] holds [word]. *)
let mentions word text =
  let n = String.length word in
  let rec from i =
    i + n <= String.length text && (String.sub text i n = word || from (i + 1))
  in
  from 0

let caps items =
  if List.exists (List.exists (fun (_, l) -> mentions "cap(" l)) items then
    [ line cap_decl ]
  else []

(* The error type of every function that raises, as its own module writes it. *)
let fault = "Fault"
let fault_variants = [ ("Bad", [ Int I64 ]); ("Odd", [ Str ]); ("Lost", []) ]
let fault_decl = "type Fault = | Bad(i64) | Odd(str) | Lost"

type var = { name : string; ty : t; mutable_ : bool }

(* Where code is being generated. *)
type scope = {
  vars : var list;  (** Latest first. *)
  frozen : string list;
      (** Variables that can't change here: those that an enclosing loop reads
          (modes.law), and loop counters. *)
  loop : bool;  (** Whether [break] and [continue] have a loop to act on. *)
  may_raise : bool;  (** Whether a raise of [Fault] may escape the code. *)
  io : bool;
  returns : t option;  (** What [return] returns, outside closures. *)
  weight : int;  (** How many times the code may run per call. *)
}

(* The body being generated, and how much of its budget it has used. *)
type body = { p : program; budget : int; mutable spent : int }

let affordable b sc cost = b.spent + (sc.weight * cost) <= b.budget
let spend b sc cost = b.spent <- b.spent + (sc.weight * cost)
let decl b name = List.assoc name b.p.decls
let typed vars ty = List.filter (fun v -> v.ty = ty) vars

let declare sc name ty ~mutable_ =
  { sc with vars = { name; ty; mutable_ } :: sc.vars }

let changeable sc =
  List.filter (fun v -> v.mutable_ && not (List.mem v.name sc.frozen)) sc.vars

let without names sc =
  { sc with vars = List.filter (fun v -> not (List.mem v.name names)) sc.vars }

(* The scope of a closure's body. It reads copies of the variables, which it
   can't change (expressions.capture), and [return], [break] and [continue] don't
   cross it. *)
let closure_scope sc params =
  {
    vars = params @ List.map (fun v -> { v with mutable_ = false }) sc.vars;
    frozen = sc.frozen;
    loop = false;
    may_raise = false;
    io = false;
    returns = None;
    weight = sc.weight * 4;
  }

(* What makes expressions, and the forms that make one out of others, which
   take it to make their operands. *)
type expr = body -> scope -> depth:int -> known:bool -> t -> code
type forms = (int * (unit -> code)) list

(* Types *)

let leaf_ty r =
  Pick.run r
    [
      (6, fun () -> Int (Pick.one r int_kinds));
      (2, fun () -> Float (Pick.one r float_kinds));
      (3, fun () -> Bool);
      (4, fun () -> Str);
    ]

let key_ty r =
  Pick.run r
    [
      (3, fun () -> Int (Pick.one r int_kinds));
      (2, fun () -> Str);
      (1, fun () -> Bool);
    ]

(* A type of at most [depth] levels. With [~maps:false], no map appears in
   it, since no map has a type that is known without an expected type. *)
let rec random_ty p ?(maps = true) depth =
  let r = p.r in
  let named =
    List.filter_map
      (fun (name, _) ->
        if maps || not (has_map p.decls (Named name)) then Some (Named name)
        else None)
      p.decls
  in
  if depth <= 0 then leaf_ty r
  else
    let inner () = random_ty p ~maps (depth - 1) in
    Pick.run r
      [
        (10, fun () -> leaf_ty r);
        (2, fun () -> List (inner ()));
        (2, fun () -> Option (inner ()));
        (1, fun () -> Tuple (Pick.times (Pick.between r 2 3) inner));
        ((if maps then 1 else 0), fun () -> Map (key_ty r, inner ()));
        ((if named = [] then 0 else 3), fun () -> Pick.one r named);
        (1, fun () -> Unit);
      ]
