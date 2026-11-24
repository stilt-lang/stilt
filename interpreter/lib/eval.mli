(** The evaluator, which runs a program, its bodies with errors panicking where
    they are reached (program.bodies-with-errors). *)

val run : Env.t -> Hir.program -> Tast.program -> args:string list -> int option
(** Runs the function [main] of module [main] with the command-line arguments
    [args], and gives the exit status of program.exit-statuses, having written
    what the program writes, then the report of a raise that escapes [main], of
    a panic, or of running out of stack or memory. [None] if there is no [main].
*)

val caller :
  Env.t ->
  Hir.program ->
  Tast.program ->
  Hir.item ->
  Value.value array ->
  Ast.loc ->
  Value.value
(** [caller env hir program] calls a function of the program, a procedural
    macro, on the values of its arguments, as a call at a place
    (macros.running). What ends the call is the caller's to catch. *)

type verdict = {
  file : string;
  line : int;  (** Of a [test] keyword, or a [/// ex:] or [/// prop:] line. *)
  passed : bool;
  property : Eval_props.verdict option;
      (** A property's seed and cases, and its counterexample when it fails
          (tests.property-verdict). *)
}

val test :
  ?out:out_channel ->
  Env.t ->
  Hir.program ->
  Tast.program ->
  (verdict list, string) result
(** Runs every test, doc example and property, in order of position, and gives
    whether each passed (program.running-tests and program.test-results;
    program.test-order; tests.property-results). What they print goes to [out],
    stderr by default: it isn't part of their result, and [test --json] keeps
    stdout for its report (conformance.run-output). [Error reason] if they ran
    out of stack or memory, which ends them all. *)
