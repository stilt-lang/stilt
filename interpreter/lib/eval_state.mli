(** The evaluator's state: the tables of the program, the frame of each body
    being run, the exceptions through which control leaves a body, and the
    limits on stack and memory. *)

exception Return of Value.value
exception Break
exception Continue

exception Raised of Value.value
(** A raise, on its way to the innermost [try] that catches it
    (effects.innermost-catch). *)

exception
  Panicked of { kind : string; detail : string; file : string; loc : Ast.loc }
(** A panic, located in the program's files (program.panic-location). *)

exception Abandoned
(** The unwinding of the calls between a performance and the [with] whose
    handler ended it without resuming (handlers.resuming). They end as a raise
    ends them, writing back their [inout] arguments
    (handlers.call-that-handler-ends). *)

exception Exited of int
(** A call of [exit]. *)

exception Fatal of string
(** Running out of stack or memory (program.exit-statuses). *)

type frame = {
  locals : (int, Value.value) Hashtbl.t;  (** By variable id. *)
  mutable tenv : (Hir.var * Types.ty) list;
      (** The type arguments of the body, and the fresh types its arms and loops
          bind (meta.fresh-types). *)
  home : string;
  file : string;
  entry : (string * Ast.loc) option;
      (** For code of the standard library, the call from the program's files
          that led into it, where its panics are reported
          (program.panic-location). *)
}
(** A body being run. *)

(** What a call runs. *)
type target =
  | Body of Tast.fn_def * (Hir.var * Types.ty) list
  | Native_code of Tast.callee * Types.ty list
  | Structural of string * Types.ty
      (** A method of a prelude trait, for a type without a written impl
          (traits.structural-calls). *)
  | Closure_body of Value.closure
  | Variant_of of Hir.item

type t = {
  env : Env.t;
  modules : (string, Hir.module_) Hashtbl.t;
  functions : (Hir.item, Tast.fn_def) Hashtbl.t;
  members : (Hir.item * string, Tast.fn_def) Hashtbl.t;
  impl_methods : (Hir.item * Hir.item * string, Tast.fn_def) Hashtbl.t;
  default_methods : (Hir.item * string, Tast.fn_def) Hashtbl.t;
  constants : (Hir.item, Value.value Lazy.t) Hashtbl.t;
  member_constants : (Hir.item * string, Value.value Lazy.t) Hashtbl.t;
  impl_constants : (Hir.item * Hir.item * string, Value.value Lazy.t) Hashtbl.t;
  default_constants : (Hir.item * string, Tast.expr Tast.definition) Hashtbl.t;
      (** The default values of traits' constants, which each type that uses one
          evaluates with its [Self] (traits.trait-constants). *)
  args : string list;
  out : out_channel;  (** Where [print] writes. *)
  apply : t -> frame -> Ast.loc -> target -> Value.value array -> Value.value;
      (** {!Eval_exprs.apply}, through which the prelude traits and the native
          items run the program's code. *)
  eval : t -> frame -> Tast.expr -> Value.value;
      (** {!Eval_exprs.expr}, through which a trait's default constant is
          evaluated. *)
}
(** The program being run. *)

(** {1 Stack and memory} *)

val limit_resources : unit -> unit
(** Limits the stack to the depth a program may use: some 300,000 nested calls,
    far more than the 10,000 of program.recursion-depth. Together with the limit
    on the heap, it keeps the interpreter well within the 1 GiB that CI gives a
    test (conformance.environment), so that it reports running out itself
    (program.exit-statuses) rather than being killed. *)

val aliases : (int, int) Hashtbl.t
(** Inside the [when]s that run, each name's variable, by id, and the variable
    that holds its value: its own, or that of the first name of its [when] whose
    handle reaches the same value (shared.when). *)

val local_id : int -> int
(** The variable that holds the value of a variable, which is itself but for the
    names that {!aliases} gives another. *)

val temporary : unit -> int
(** A variable that no declaration has, such as the temporary that holds a
    yielded view (projections.yield), or the number of a projection's access. *)

val reserve : int -> unit
(** [reserve bytes] ends the program unless the heap can grow by [bytes].
    Operations that can build a value much larger than their operands ask first.

    @raise Fatal if it can't. *)

val check_memory : unit -> unit
(** Ends the program if its heap is full. Every call and every turn of a loop
    checks, and each allocates little, so the heap is measured at one in every
    256 of them.

    @raise Fatal if it is full. *)

(** {1 A macro's run (macros.running and macros.step-limits)} *)

exception Stopped of string
(** A run that stops before it finishes, with the reason (macros.step-limits).
*)

type run = {
  at : Ast.loc;
      (** The use's path, where the code that its quotes write is placed. *)
  home : string;  (** The macro's module. *)
  mark : string -> int;
      (** A number for the names that a quote of a module writes, which resolve
          among that module's items (macros.quote-hygiene). *)
  mutable steps : int;
  mutable frames : (string * Ast.loc) list;
      (** The module's own functions running, by their names' places, innermost
          first. *)
  mutable depth : int;
}
(** A macro's run, its steps and frames so far. *)

val running : run option ref
(** The run under way, if any. Outside one, a quote and [fresh] make code and
    names that no observable shows but a name's text (macros.outside-run). *)

val step : unit -> unit
(** Counts a step of the run under way: a call of a function, a method, a
    closure or a native, or a turn of a loop.

    @raise Stopped after 10,000,000. *)

val called : target -> unit
(** Counts the call of a target as a step of the run under way, when it is a
    function, a closure or a native.

    @raise Stopped after 10,000,000 steps. *)

val entering : home:string -> at:Ast.loc -> (unit -> 'a) -> 'a
(** [entering ~home ~at f] runs [f], the body of [home] whose name is at [at],
    as a frame of the run under way. What ends the run keeps the frames that
    were running.

    @raise Stopped deeper than 10,000 frames. *)

(** {1 Frames} *)

val frame :
  t ->
  home:string ->
  tenv:(Hir.var * Types.ty) list ->
  entry:(string * Ast.loc) option ->
  frame
(** A frame for a body of module [home], whose [entry] counts only for code of
    the standard library. *)

val enter :
  t ->
  frame ->
  Ast.loc ->
  home:string ->
  tenv:(Hir.var * Types.ty) list ->
  frame
(** [enter t caller loc ~home ~tenv] is the frame of a body of [home] that
    [caller] calls at [loc]. *)

val panic : frame -> Ast.loc -> string -> ('a, unit, string, 'b) format4 -> 'a
(** [panic fr loc kind fmt …] raises {!Panicked} with the kind and the formatted
    detail, at [loc] in the program's files, or at the call that led into the
    standard library. *)

val check_error : t -> home:string -> Ast.loc -> 'a
(** [check_error t ~home loc] raises the [check-error] panic of code with an
    error, located at [loc] in the file of module [home]
    (program.check-error-report). *)

val guard : frame -> Ast.loc -> (unit -> 'a) -> 'a
(** [guard fr loc f] runs [f], whose panics happen at [loc]. *)
