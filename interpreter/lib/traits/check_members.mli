(** Members of types and traits: the methods found for a receiver, and members
    named as [Type.m] or [Trait.m] (traits.methods and traits.qualified-calls;
    traits.functions-without-self and traits.trait-constants). *)

(** What a method's name finds on a type. *)
type found =
  | Inherent of Env.member
  | Via_trait of Hir.item * Env.trait_method * Env.trait_info
      (** A member of a trait, with what the trait is. *)
  | Ambiguous of Hir.item list  (** Methods of several traits. *)
  | Missing

val find_method : Check_state.state -> Types.ty -> string -> found
(** The method of a type with the given name: its inherent impls' first, then
    those of the visible traits it implements, or of the bounds of a type
    parameter, applied or not (traits.method-resolution;
    traits.constructor-parameters). *)

val head : Types.ty -> Hir.item option
(** The type constructor at the head of a type. *)

val left_out : Check_state.state -> Types.ty -> string -> bool
(** Whether a method that a type lacks is one that an error leaves out, whose
    uses have the error type (errors.error-type): a member of an impl with an
    error, or a method that a syntax error leaves without a signature, of a
    trait that the type implements or is bounded by. *)

val require_visible : Check_state.state -> Hir.name -> Env.member -> unit
(** Reports a private member used outside its module (program.visibility). *)

val ambiguous : Check_state.state -> Hir.name -> Hir.item list -> unit
(** Reports a method that several traits give a type (traits.ambiguous-methods).
*)

val trait_self : Env.trait_info -> Types.ty -> Types.ty
(** What a trait's [Self] is for a value of a type: the type, or for a
    constructor trait the constructor at its head (traits.constructor-traits).
*)

val instantiate_trait :
  Check_state.state ->
  Ast.loc ->
  use_at:Ast.loc ->
  Hir.item ->
  Env.trait_method ->
  Env.trait_info ->
  Types.ty ->
  Types.ty list * (Types.mode * Types.ty) list * Types.ty * Types.row
(** [instantiate_trait st loc ~use_at trait m info self] instantiates the member
    [m] of [trait] with [Self] as [self], and the trait's parameters as the impl
    or the bound of [self] gives them (traits.trait-arguments and
    traits.bound-arguments). *)

(** What naming a member finds. *)
type member_use =
  | Callable of
      Tast.callee
      * Types.ty list
      * (Types.mode * Types.ty) list
      * Types.ty
      * Types.row
      * bool
      (** A function, with its type arguments and instantiated signature, and
          whether it is a projection (projections.declaring-projection). *)
  | Trait_constant of Tast.expr
      (** A trait's constant, named on a type (traits.trait-constants). *)
  | Reflection of Tast.reflect * Types.ty
      (** [T.shape] or [T.name] of [std.meta], with the type it gives
          (meta.shape-and-name). *)

val member :
  Check_state.ctx -> Ast.loc -> Hir.owner -> Hir.name -> member_use option
(** A member of a type or a trait, named as [Type.m] or [Trait.m]
    (traits.associated-functions and traits.qualified-calls), or [None] after an
    error. A trait's function without [self] or constant named on its trait is
    E0330 (traits.functions-without-self and traits.trait-constants). *)

val projection_value : Check_state.state -> Ast.loc -> Tast.expr
(** Reports a projection named other than to call it, E0426
    (projections.not-a-value), and gives the error node. *)

val member_value :
  Check_state.ctx -> Ast.loc -> Hir.owner -> Hir.name -> Tast.expr
(** A member named as a value: a function, a type's constant
    (declarations.constant-declarations), or a trait's (traits.trait-constants).
*)
