(** The types of a property's parameters as its generators see them
    (tests.generable-types and tests.minimal-values): the types they hold, each
    a node of a graph, with each type's depth, from which its minimal value and
    its nearest variants follow. *)

(** Why a type can't be generated (tests.generable-types). *)
type unfit =
  | Function  (** It holds a function type. *)
  | No_values of Types.ty  (** It holds this type, which has no values. *)
  | Key of Types.ty
      (** It holds a map whose key type, this one, doesn't implement both [Eq]
          and [Hash]. *)
  | Infinite  (** It holds infinitely many types. *)

type node =
  | Bool
  | Int of Ints.kind
  | Float of bool  (** Whether it is an [f32]. *)
  | Str
  | Unit
  | Tuple of int list
  | List of int
  | Map of int * int
  | Record of Hir.item * (string * int) list
      (** Its fields, in declaration order. *)
  | Variants of (Hir.item * int list) list
      (** Its variants, in declaration order, with their payloads. *)

type graph = {
  nodes : node array;
  tys : Types.ty array;  (** The type of each node. *)
  depths : int array;
      (** The depth of each node's type, [max_int] for a type with no values. *)
}

val build : Env.t -> Types.ty list -> (graph * int list, unfit) result
(** The graph of the types that the parameters' types hold, and the node of each
    parameter's type, or why one of them can't be generated: that they hold
    infinitely many types, else the first reason met in a walk of the types from
    the first parameter's. *)

val unfit : Env.t -> Types.ty -> unfit option
(** Why a parameter's type can't be generated, if it can't. A type with an error
    can: no diagnostic arises from it (errors.root-causes). *)

val nearest : graph -> (Hir.item * int list) list -> (Hir.item * int list) list
(** A variant type's nearest variants, in declaration order
    (tests.minimal-values). *)

val live : graph -> (Hir.item * int list) list -> (Hir.item * int list) list
(** A variant type's variants whose payload types all have values. *)
