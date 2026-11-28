(** A program's traits, impls and functions as it writes them, as kinds read
    them, and the uses of its functions with constructor parameters, for the
    model's checks of kinds (formal/Stilt/Syntax/Kinds.lean). *)

val written :
  Env.t -> Hir.program -> Model_types.fn_instance list -> Model_json.t
(** The program's own modules' declarations, and the uses among the instances.
*)
