(** Constants: their values, and the cycles among them
    (declarations.constant-expressions and declarations.constant-cycles). *)

val check_constant :
  ?bounds:Env.bounds ->
  ?self:Types.ty ->
  Env.t ->
  Hir.module_ ->
  Hir.const_decl ->
  Hir.expr ->
  Tast.expr Tast.definition * Check_state.constant list * Diagnostic.t list
(** [check_constant env m c value] checks the value [value] of the constant [c]
    against its type, and gives the constants it names and its errors. In the
    standard library, a hole marks a native constant
    (declarations.native-items). A trait's default value is checked with the
    trait's [bounds], and [self] as its [Self] (traits.impl-members). *)

val constant_cycles :
  ('a * Hir.module_ * Ast.loc * 'a list) list ->
  (Hir.module_ * Diagnostic.t) list
(** The constants that refer to each other in a cycle, each cycle reported once,
    at the name of its last constant (errors.primary-spans). The list holds
    every constant that has a value, by a key, with its module, the position of
    its name, and the keys of the constants its value names. *)
