(** The types and signatures that declarations write, and when two of them are
    the same (traits.impl-signatures). *)

open Env_tables

val of_hir : ?self:Types.ty -> Hir.ty -> Types.ty

val of_hir_row : ?self:Types.ty -> Hir.row -> Types.row
(** The type that a written type stands for. [self] is what [Self] means in a
    trait, a type parameter. *)

val bounds_of : ?self:Types.ty -> Hir.type_param list -> bounds
(** The bounds of type parameters, with their arguments. A bound with an error
    is left out. *)

val synthetic : ?loc:Ast.loc -> string -> Hir.var
(** A new variable that no declaration has, at [loc] if it stands for something
    written there. *)

val signature :
  ?self:Types.ty -> ?self_ty:Types.ty -> outer:bounds -> Hir.fn_decl -> fn_sig
(** The signature of a function. [self] is what [Self] means, [self_ty] the
    receiver's type, and [outer] the generics of the impl that holds the
    function, which come first. Each non-escaping parameter has an implicit row
    variable of its own, which follows the written ones among the row
    parameters, joins the parameter's row, and joins the function's own row
    (effects.non-escaping-parameters). *)

val passing : fn_sig -> bool list
(** For each parameter of a signature, the receiver's first, whether it is
    non-escaping (effects.non-escaping-parameters). *)

val equal : Types.ty -> Types.ty -> bool
(** Whether two types are the same. The error type is the same as every type. *)

val equal_list : Types.ty list -> Types.ty list -> bool
(** Whether two lists of types are the same, in order. *)

val renaming : Types.forall -> Types.forall -> (Types.ty -> Types.ty) option
(** [renaming p q] renames [q]'s type parameters [p]'s, when the two declare as
    many with the same bounds in the same order, so that they are the same
    polymorphic function type if their bodies are then equal
    (polymorphism.instantiation). *)

val matches_trait :
  self_param:Hir.var ->
  self_ty:Types.ty ->
  fixed:(Hir.var * Types.ty) list ->
  fn_sig ->
  fn_sig ->
  own:int ->
  bool
(** [matches_trait ~self_param ~self_ty ~fixed expected actual ~own] tells
    whether [actual], the signature of a method of an impl with [own] type
    parameters, is the trait method's [expected], once [Self], the trait's
    [self_param], is the impl's type [self_ty], each trait parameter is the
    argument that [fixed] gives it (traits.trait-arguments), and the method's
    generics correspond in order (traits.impl-signatures). *)
