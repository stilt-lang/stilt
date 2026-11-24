(** The values of running programs.

    Every value is immutable, which gives the value semantics of
    values.value-semantics: a copy is the value itself, and a change builds a
    new value. *)

module Imap : Map.S with type key = int
module I64map : Map.S with type key = int64

(** Persistent vectors, for lists. *)
module Vec : sig
  type 'a t

  val empty : 'a t
  val length : 'a t -> int

  val get : 'a t -> int -> 'a
  (** @raise Not_found unless [0 <= i < length]. *)

  val set : 'a t -> int -> 'a -> 'a t
  val push : 'a t -> 'a -> 'a t
  val pop : 'a t -> ('a t * 'a) option

  val sub : 'a t -> int -> int -> 'a t
  (** [sub v start stop] holds the elements from [start] up to [stop]. *)

  val insert : 'a t -> int -> 'a -> 'a t
  val remove : 'a t -> int -> 'a t
  val of_list : 'a list -> 'a t
  val to_list : 'a t -> 'a list
end

type value =
  | Int of int64  (** As {!Ints} holds it, for the type the program gives it. *)
  | Float of float  (** As {!Floats} holds it. *)
  | Bool of bool
  | Str of string  (** UTF-8 bytes. *)
  | Tuple of value list  (** [()] included. *)
  | List of value Vec.t
  | Map of dict
  | Variant of Hir.item * value list
  | Record of Hir.item * (string * value) list
      (** Its fields, in the order the type declares them. *)
  | Fn of fn
  | Iter of iter
      (** An iterator, which runs nothing until a consumer reads it, and which
          every consumer reads from its first element (views.laziness). A view
          is no value of its own: it is the part of its source that it views,
          which nothing can change while the view lives
          (views.change-while-viewed). *)
  | Window of window
      (** A writable view (projections.writable-views): a window into the part
          of a list that a place of a frame holds, which a write through the
          view writes (projections.writable-views and
          projections.what-view-writes). *)
  | Deferred of deferred
      (** A [Lazy] of [std.lazy] (polymorphism.lazy-values), which every copy of
          it shares, so that its value is computed once, whichever copy asks.
          Its function performs no effect, so no program can tell this cell from
          an immutable value. *)
  | Handler of handler
      (** A handler (handlers.handler-types): its operations, closures of the
          code that wrote it. [async]'s, which [std.task] gives, has none, since
          every task runs to its end where it starts (tasks.sequential-run). *)
  | Shared of shared
      (** A [Shared<T>] of [std.sync] (shared.std-sync): a handle on one value,
          which every copy of the handle reaches, and which a [when] reads and
          writes (shared.when). *)
  | Meta of Macro_values.t
      (** A value that a macro reads or writes (macros.tokens-and-code). *)

and shared = { mutable held : value }

and handler = {
  heffect : Hir.item;
  control : bool;  (** Whether it takes control, written [-> R]. *)
  ops : (string * fn) list;
}

and deferred = {
  compute : fn;
  mutable result : value option;  (** Once computed. *)
}

and window = {
  locals : (int, value) Hashtbl.t;
  root : int;
  path : step list;
  start : int;
  stop : int;
}
(** The place of a frame that a window writes: its frame's locals, the variable,
    the steps to the list, and the part's offsets. *)

(** A step of a place (expressions.places): a field, a tuple's element, or an
    index into a container of the type, at the location of the index expression.
*)
and step =
  | At_field of string
  | At_elem of int
  | At_key of value * Types.ty * Ast.loc

(** Where an iterator's elements come from, and the adapters they pass through
    (views.making-iterator and views.adapters). *)
and iter =
  | Elements of value list
      (** The elements of a list or of a view of one, the entries of a map as
          pairs, or the characters or bytes of a view of a string. *)
  | Range of int64 * int64  (** From the first up to but excluding the last. *)
  | Mapped of iter * fn
  | Filtered of iter * fn
  | Taken of iter * int64
  | Skipped of iter * int64
  | Taken_while of iter * fn
  | Skipped_while of iter * fn
  | Enumerated of iter * int64
  | Zipped of iter * iter
  | Chained of iter * iter

and dict = private {
  entries : (value * value) Imap.t;
      (** Each entry by a stamp that orders entries by insertion. *)
  stamps : int list I64map.t;  (** The stamps of each key hash. *)
  next : int;
  default : value option;  (** [Map.with_default]'s (std.maps). *)
}

(** A function value. *)
and fn =
  | Closure of closure
  | Function of Tast.callee * Types.ty list
      (** A named function with its type arguments, which hold no type
          parameter. *)
  | Constructor of Hir.item  (** A variant that takes a payload. *)
  | Poly of Hir.var list * fn
      (** A value of a polymorphic function type: a function whose types hold
          these rigid types, which each use gives types
          (polymorphism.instantiation). *)

and closure = {
  params : Tast.pattern list;
  body : Tast.expr;
  captured : value Imap.t;
      (** The variables in scope where it was created, by [id], copied then
          (expressions.capture). *)
  tenv : (Hir.var * Types.ty) list;
      (** The type arguments of the code that created it. *)
  home : string;  (** The module whose source holds it. *)
}

val unit : value
val some : value -> value
val none : value
val option : value option -> value

(** Maps in insertion order. Keys are found by their hash, then by equality,
    which the evaluator provides, since both may run the program's impls. *)
module Dict : sig
  type t = dict

  val empty : value option -> t
  val length : t -> int

  val entries : t -> (value * value) list
  (** In insertion order. *)

  val find : t -> hash:int64 -> same:(value -> bool) -> (int * value) option
  (** The stamp and value of the first entry, in insertion order, whose key has
      the hash and satisfies [same]. *)

  val set : t -> int -> value -> t
  (** [set d stamp v] sets the value of the entry of [stamp], which keeps its
      key and its position. *)

  val add : t -> hash:int64 -> value -> value -> t
  (** A new entry, at the end. *)

  val remove : t -> hash:int64 -> int -> t
  (** Removes the entry of a stamp, whose key has the hash. *)
end

val same : value -> value -> bool
(** Whether two values of a constant pattern's type are structurally equal
    (patterns.floats). *)
