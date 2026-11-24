(** The walk of a body's code in the order it is written, which records what the
    rules of acceptance read (facts.acceptance-places): the writes of each
    body's own code, the tests that guard each operation, the loops and the
    statement that hold it, and the [for] loops over ranges around it. Each
    closure literal's body is a body of its own, with a number. *)

open Tast

type write_kind = Assign of Ast.binary option | Inout | Insert | Yield

type write = {
  body : int;
  root : int;
  fields : string list;
  indexed : bool;
  kind : write_kind;
  value : expr option;
  place : expr;
  line : int;
}

val changes : write -> Accept_code.place -> bool
(** Whether a write may change the place [p]: a write to its root, at [p]'s
    fields or a prefix of them, not through an index. *)

val unstores : write -> Accept_code.place -> bool
(** Whether a write may take a key out of the place [p]: one that changes it and
    isn't an insertion at [p] itself. *)

type frame = { atoms : Accept_code.atom list; start : int; id : int }
type span = { mutable first : int; mutable last : int }

type range = {
  rbody : int;
  var : Hir.var;
  rstart : expr;
  rend : expr;
  inclusive : bool;
  rspan : int;
}

type op = Index of expr * expr | Division of expr | Self_call of arg list

type pending = {
  op : op;
  node : expr;
  pbody : int;
  log_at : int;
  frames : int list;
  loops : (int * int) list;
  stmt : int option;
  ranges : int list;
}

type looped = {
  loop : expr;
  lbody : int;
  cond : expr option;
  block : block;
  lspan : int;
}

type declared = Let_init of expr | Var_init of expr | Range_start of expr

type t = {
  log : write Dynarray.t;
  spans : span Dynarray.t;
  frames : frame Dynarray.t;
  ranges : range Dynarray.t;
  mutable pending : pending list;
  mutable looped : looped list;
  decls : (int, int * declared) Hashtbl.t;
  reader : Accept_code.reader;
}

type state = {
  w : t;
  env : Env.t;
  self : Implicit_names.key option;
  mutable active : int list;
  mutable loops_in : (int * int) list;
  mutable stmts : int list;
  mutable ranges_in : int list;
  mutable stores : expr list;
  mutable current : int;
  mutable bodies : int;
  mutable ids : int;
}

val in_span : t -> int -> int -> write list
(** The writes of [body] that the walk logged within [span]. *)

val between : t -> int -> pending -> write list
(** The writes between a frame and an operation: those since its test, those of
    the loops inside its code that hold the operation, and those of the
    statement that holds it. *)

val frame : t -> pending -> (Accept_code.atom -> bool) -> int option
(** The innermost frame guarding [p] that gives a fact [holds] accepts. *)

val first : write list -> (write -> bool) -> int option
(** The line of the first of the writes [f] accepts. *)

val id : state -> int
(** A new number, for a frame of guards. *)

val open_span : state -> int
(** Starts a span of the log, which [close_span] ends, and gives its number. *)

val close_span : state -> int -> unit
(** Ends the span [span] at the log's end. *)

val guard : state -> Accept_code.atom list -> int -> unit
(** Holds [atoms], the facts a test gives, for the code from [start] on, unless
    there are none. *)

val truncate : state -> int -> unit
(** Keeps only the first [depth] frames of guards that hold. *)

val pend : state -> op -> Tast.expr -> unit
(** Records the operation [op] at [node] for the rules to read once the walk
    ends, with the guards, loops, statement and ranges around it. *)

val write : state -> Tast.expr -> write_kind -> Tast.expr option -> unit
(** Logs a write to [place], of [kind], with [value] when it is an assignment's,
    if [place] has a root that the rules read. *)
