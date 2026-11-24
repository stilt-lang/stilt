(** Bodies of functions, tests and doc examples, each checked on its own
    (declarations.function-declarations, declarations.tests and
    syntax.doc-examples). *)

val new_state :
  Env.t ->
  Hir.module_ ->
  bounds:Env.bounds ->
  self:Types.ty option ->
  Check_state.state
(** The state of checking a body of a module, with nothing found yet. *)

val outcome :
  Check_state.state -> at:Ast.loc -> (unit -> 'a) -> 'a Tast.definition
(** The elaboration of the body known by [at], or [Broken] if resolving or
    checking it found an error, so that the later phases skip it
    (errors.phases). *)

val check_fn :
  Env.t ->
  Hir.module_ ->
  bounds:Env.bounds ->
  self:Types.ty option ->
  Env.fn_sig ->
  Hir.fn_decl ->
  Hir.fn_body ->
  Tast.fn_def * Diagnostic.t list
(** A function's body, checked against its signature, and its errors. In the
    standard library, a hole body marks a native function
    (declarations.native-items); anywhere else it is a hole of the function's
    return type (declarations.typed-holes). *)

val foreign_fn : Hir.module_ -> Env.fn_sig -> Hir.fn_decl -> Tast.fn_def
(** A foreign function, which C gives (c.foreign-functions): [Native], as the
    interpreter calls it through {!Foreign}. *)

val check_test :
  Env.t ->
  Hir.module_ ->
  Ast.loc ->
  Hir.block ->
  Tast.block Tast.definition * Diagnostic.t list
(** A test's body, which may perform [io] and raise any error that can be shown
    (program.test-declarations). *)

val check_example :
  Env.t ->
  Hir.module_ ->
  Hir.expr ->
  Tast.expr Tast.definition * Diagnostic.t list
(** A doc example's claim, which must be [true], and which may perform [io] and
    raise any error that can be shown (program.doc-examples). *)
