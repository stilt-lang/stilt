(** What names and paths refer to: lookups in a module's scope
    (declarations.name-lookup), and walks through the namespaces of modules
    (program.visibility and program.namespaces). *)

open Resolve_context

(** What a name refers to. *)
type meaning =
  | Var_ref of Hir.var
  | Param_ref of Hir.var  (** A type parameter. *)
  | Self_ref of Hir.ty
  | Item_ref of Hir.item * entry
  | Namespace_ref of string
  | Broken_ref  (** Nothing: its uses have the error type. *)

val lookup : ctx -> namespace -> locals:bool -> string -> meaning option
(** What a name means where the context is, in one namespace, if anything.
    [locals] tells whether it can be a local binding. *)

val describe_meaning : meaning -> string
(** What a name refers to, as errors name it, such as "a variable". *)

val walk :
  ctx ->
  want:namespace ->
  noun:string ->
  ?misplaced:(Hir.name -> string -> unit) ->
  locals:bool ->
  Hir.name list ->
  meaning * Hir.name * Hir.name list
(** [walk ctx ~want ~noun ~locals path] resolves the names of [path] for as long
    as they name namespaces (program.namespaces), and returns what the first
    name that isn't a namespace means, that name, and the names after it. The
    last name is read in [want], and named [noun] in errors: [misplaced n what]
    reports the name [n] that is [what] instead, E0212 unless it is given.
    [locals] tells whether the first name can be a local binding. Naming an item
    of another module records a reference to that module, and needs the item to
    be visible (program.visibility). *)

val walk_to_end :
  ctx -> want:namespace -> noun:string -> Hir.name list -> meaning * Hir.name
(** The meaning of a path that must end at its last name, since only modules
    hold items in a path, and that name. No local binding is a path's first
    name. *)

val wrong_kind : ctx -> Hir.name -> meaning -> string -> unit
(** [wrong_kind ctx last m noun] reports that the name [last], which means [m],
    isn't [noun]. *)
