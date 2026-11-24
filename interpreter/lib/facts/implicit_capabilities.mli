(** The capabilities of natives, and how a message names where a function's
    capability comes from (facts.capability-natives and facts.without). *)

val native : Implicit_names.key -> Ast.capability option
(** The capability of a native function, by the table of
    facts.capability-natives. The caller checks that the key names a native. *)

val qualified : Implicit_names.key -> string
(** The item as a message names it: a function of a module of [std] other than
    the prelude with its module's last segment, as [clock.unix_ms]. *)

val named :
  through:(Implicit_names.key * Ast.loc) list ->
  Ast.capability ->
  Implicit_names.key ->
  string
(** [named ~through c k]: what an operation that names [k], which has [c], does,
    as in
    ["this uses `report`, which has the capability `clock` through `stamp` at
     line 4, then `clock.unix_ms` at line 3"]. [through] is the chain of items
    that pass [c] on, from what [k]'s body names first down to the native, each
    with where the one before it names it; it is empty when [k] is the native.
*)
