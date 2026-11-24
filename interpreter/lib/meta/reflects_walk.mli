(** The walk of a type that a function that reflects is given
    (meta.types-without-shape): depth first in the order of meta.shapes, each
    type once, skipping a type with an impl of a guard and what it holds. *)

type need = { parts : bool; guards : Hir.item list; chain : string list }
(** What a function needs of a type it reflects on: a shape, and with [parts]
    one for each type its values hold, at any depth, but where a type has an
    impl of one of [guards]. [chain] names the functions that reflect, from the
    one instantiated to the one that names [T.shape()]. *)

type scope = {
  env : Env.t;
  bounds : Env.bounds;  (** The type parameters of the body, with bounds. *)
  origins : (int, Types.ty) Hashtbl.t;
      (** The rigid types of the polymorphic arguments of [fields.build], each
          with the type whose fields it stands for (meta.fields). *)
  met : Types.ty -> Hir.item -> (need * Types.ty) list;
      (** What the methods of the impl with which a type meets a guard need of
          the types it gives the impl's own type parameters, which are checked
          where the bound is met (meta.unseen-instantiations). *)
}

type failure = { missing : Types.ty; held : string list }
(** A type without a shape, with what holds it, outermost first. *)

val first :
  scope -> param:(Hir.var -> need -> unit) -> need -> Types.ty -> failure option
(** The first type of a walk that fails a need. [param] is told of each type
    parameter of the body that the walk meets, which the body then reflects on:
    one that a fresh type's or a rigid type's origin is, on its parts. *)

val holds : Env.t -> Types.ty -> Types.ty -> bool
(** [holds env ty missing] tells whether a value of type [ty] holds one of type
    [missing], at any depth. *)

val message : failure -> need -> string
(** E0350's message: the type, the types that hold it, and the chain. *)
