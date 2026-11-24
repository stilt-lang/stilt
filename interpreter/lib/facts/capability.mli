(** The capabilities below [io] (facts.capabilities and
    facts.capability-natives), and the names of the limits of a [without] clause
    (program.header-limits; facts.spelling; facts.without). *)

val all : Ast.capability list
(** The seven capabilities, in the order of facts.capabilities. *)

val name : Ast.capability -> string
(** The capability as it is written after [without] and in [may]: ["fs"]. *)

val of_name : string -> Ast.capability option
(** The capability spelled so, if any. *)

val limit_name : Ast.limit -> string
(** The limit as it is written after [without]. *)

val native : home:string -> name:string -> Ast.capability option
(** [native ~home ~name] is the capability of the native function [name] of the
    module [home], by the table of facts.capability-natives. The caller checks
    that the function is a native: [std.fs]'s functions written in Stilt, such
    as [join], have none of their own. *)
