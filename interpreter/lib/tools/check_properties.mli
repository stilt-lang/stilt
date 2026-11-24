(** Properties, the [/// prop:] lines of doc comments (tests.property-form,
    tests.generable-types and tests.property-io): a closure with typed
    parameters, whose types can be generated, and whose body is a [bool] that
    performs no [io] and may raise an error that can be shown. *)

val check_property :
  Env.t ->
  Hir.module_ ->
  Hir.expr ->
  Tast.expr Tast.definition * Diagnostic.t list
(** A property's closure, elaborated, and its errors. A property that isn't a
    closure with at least one parameter, each typed, is [Broken], with E0332 and
    no other error. *)
