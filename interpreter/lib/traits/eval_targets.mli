(** What a call runs: the body of a function or a method, native code, a
    structural impl, a closure, or a variant's constructor
    (traits.method-resolution and declarations.native-items). *)

val matching :
  Types.ty -> Types.ty -> (Hir.var * Types.ty) list -> (Hir.var * Types.ty) list
(** [matching pattern ty bound] binds the parameters in [pattern], such as an
    impl's type, to the parts of [ty] that they match, before [bound]. *)

val target : Eval_state.t -> Tast.callee -> Types.ty list -> Eval_state.target
(** What a call of a callee, with concrete type arguments, runs. A trait method
    runs the method of the impl for its type, the trait's default method, or the
    structural impl (traits.structural-calls). *)

val trait_constant :
  Eval_state.t -> Hir.item -> string -> Types.ty -> Value.value
(** [trait_constant t trait name ty] is the value of the constant [name] of
    [trait] for the concrete type [ty]: the impl's, or the trait's default with
    [ty] as its [Self] (traits.trait-constants). *)

val target_of_fn : Eval_state.t -> Value.fn -> Eval_state.target
(** What a call of a function value runs. A value of a polymorphic function type
    is called only once it is instantiated. *)

val generalize : Hir.var list -> Value.value -> Value.value
(** [generalize vars v] is the function value [v], whose types hold the rigid
    types [vars], as a value of a polymorphic function type
    (polymorphism.rigid-types). It passes no dictionaries of its own: each use
    gives the rigid types theirs . *)

val instantiate : Types.ty list -> Value.value -> Value.value
(** A value of a polymorphic function type at one use, whose rigid types take
    the concrete types [ts], in order, as a call of a generic function passes
    its type arguments (polymorphism.instantiation). *)
