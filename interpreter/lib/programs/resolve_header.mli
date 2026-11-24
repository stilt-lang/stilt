(** Step 2 of name resolution: a module's header, which names the module and
    limits it (program.module-header and program.header-limits). *)

val check_header :
  Resolve_context.state -> Resolve_scopes.unit_ -> Hir.limit Hir.node list
(** The module's limits, after checking its header's path against its name. *)
