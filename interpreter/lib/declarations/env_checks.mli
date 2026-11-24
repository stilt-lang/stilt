(** The rules about declarations outside impls: records that contain themselves
    (declarations.recursive-types), the signature of [main] (program.main), and
    the bounds of [where] clauses on member types that a bound's argument fixes
    (traits.where). *)

open Env_tables

val check_record_cycles : diagnostics -> t -> Hir.program -> unit
(** Reports the records that contain themselves through records and tuples
    alone, which can't be constructed (declarations.recursive-types). Each group
    of records that hold one another is one error, at the last of them
    (errors.primary-spans). *)

val check_main : diagnostics -> t -> Hir.program -> unit
(** Reports the function [main] of the program's module [main], unless it has no
    generics and no parameters, returns [()], and performs at most [io] and
    [raise<E>] with [E: Show] (program.main). *)

val check_wheres : diagnostics -> t -> Hir.program -> unit
(** Reports each bound of a [where] clause on a member type that a bound's
    argument fixes, which the fixed type doesn't meet, E0318 at the member type
    (traits.where). *)
