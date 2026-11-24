(** Running a property (tests.property-cases, tests.running-cases,
    tests.shrinking and tests.property-verdict): its cases, in order, until one
    fails, whose values are then shrunk. *)

(** How a run of the closure failed (tests.running-cases). *)
type failure =
  | False
  | Raise of string  (** The raised value, as its [Show] impl shows it. *)
  | Panic of string * string  (** The panic's kind and its detail. *)

type failed = {
  case : int;
  counterexample : string list;
      (** Each parameter's value, by its structure. *)
  failure : failure;
  shrinks : int;
}

type verdict = { seed : int64; cases : int; failed : failed option }
(** What [test --json] reports of a property (tests.property-verdict). *)

val run :
  Eval_state.t -> Eval_state.frame -> Tast.property -> Tast.expr -> verdict
(** Runs a property whose closure, elaborated, is the expression, in the frame
    of a body of its module. A stack overflow or running out of memory ends
    every test, so it isn't caught.

    @raise Eval_state.Fatal
    @raise Stack_overflow *)

val json : verdict -> string
(** The [property] object of tests.property-verdict. *)
