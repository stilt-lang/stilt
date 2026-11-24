(** What the [use] declarations of a package's modules can name
    (packages.modules-of-dependencies, packages.imports and
    packages.manifests-with-errors). *)

val view :
  Program.packages ->
  Resolve_scopes.unit_ list ->
  Resolve_context.env ->
  int ->
  string ->
  Resolve_context.lookup
(** [view packages units env package written] is what a [use] of [written] in a
    module of the package [package] names, among [units], the program's modules,
    whose names [env] holds. *)
