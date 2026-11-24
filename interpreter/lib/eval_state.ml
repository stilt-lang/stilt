(* The evaluator's state: the tables of the program, the frame of each body
   being run, the exceptions through which control leaves a body, and the
   limits on stack and memory. *)

open Tast
open Value
module T = Types

exception Return of value
exception Break
exception Continue

(* A raise, on its way to the innermost [try] that catches it (effects.innermost-catch). *)
exception Raised of value

(* A panic, located in the program's files (program.panic-location). *)
exception
  Panicked of { kind : string; detail : string; file : string; loc : Ast.loc }

(* The unwinding of the calls between a performance and the [with] whose
   handler ended it without resuming (handlers.resuming). They end as a raise
   ends them, writing back their [inout] arguments (handlers.call-that-handler-ends). *)
exception Abandoned

(* A call of [exit]. *)
exception Exited of int

(* Running out of stack or memory (program.exit-statuses). *)
exception Fatal of string

(* A body being run. *)
type frame = {
  locals : (int, value) Hashtbl.t;  (** By variable id. *)
  mutable tenv : (Hir.var * T.ty) list;
      (** The type arguments of the body, and the fresh types its arms and loops
          bind (meta.fresh-types). *)
  home : string;
  file : string;
  entry : (string * Ast.loc) option;
      (** For code of the standard library, the call from the program's files
          that led into it, where its panics are reported
          (program.panic-location). *)
}

(* What a call runs. *)
type target =
  | Body of fn_def * (Hir.var * T.ty) list
  | Native_code of callee * T.ty list
  | Structural of string * T.ty
      (** A method of a prelude trait, for a type without a written impl
          (traits.structural-calls). *)
  | Closure_body of closure
  | Variant_of of Hir.item

type t = {
  env : Env.t;
  modules : (string, Hir.module_) Hashtbl.t;
  functions : (Hir.item, fn_def) Hashtbl.t;
  members : (Hir.item * string, fn_def) Hashtbl.t;
  impl_methods : (Hir.item * Hir.item * string, fn_def) Hashtbl.t;
  default_methods : (Hir.item * string, fn_def) Hashtbl.t;
  constants : (Hir.item, value Lazy.t) Hashtbl.t;
  member_constants : (Hir.item * string, value Lazy.t) Hashtbl.t;
  impl_constants : (Hir.item * Hir.item * string, value Lazy.t) Hashtbl.t;
  default_constants : (Hir.item * string, Tast.expr Tast.definition) Hashtbl.t;
  args : string list;
  out : out_channel;  (** Where [print] writes. *)
  apply : t -> frame -> Ast.loc -> target -> value array -> value;
  eval : t -> frame -> Tast.expr -> value;
      (** {!Eval_exprs.apply}, through which the prelude traits and the native
          items run the program's code. *)
}

(* Stack and memory *)

(* The deepest stack and the largest heap a program may use. The stack holds
   some 300,000 nested calls, far more than the 10,000 of program.recursion-depth, and
   runs out before the heap does when recursion never ends. Together they keep
   the interpreter well within the 1 GiB that CI gives a test (conformance.environment), so that it reports running out itself (program.exit-statuses) rather than
   being killed. *)
let stack_limit = 64 * 1024 * 1024 / (Sys.word_size / 8)
let heap_limit = 512 * 1024 * 1024
let limit_resources () = Gc.set { (Gc.get ()) with stack_limit }
let heap_bytes () = (Gc.quick_stat ()).heap_words * (Sys.word_size / 8)

(* Ends the program unless the heap can grow by [bytes]. Operations that can
   build a value much larger than their operands ask first. A heap at its
   limit may hold mostly garbage, as checking a 100K-line project leaves over
   500 MB of which some 200 MB is live, so it is compacted before the program
   is said to run out. *)
let reserve bytes =
  if heap_bytes () + bytes > heap_limit then (
    Gc.compact ();
    if heap_bytes () + bytes > heap_limit then raise (Fatal "out of memory"))

(* Every call and every turn of a loop allocates little, so the heap is
   measured at one in every 256 of them. *)
let ticks = ref 0

let check_memory () =
  incr ticks;
  if !ticks land 255 = 0 then reserve 0

(* A macro's run (macros.running and macros.step-limits) *)

(* A run that stops before it finishes: too many steps or frames (macros.step-limits). *)
exception Stopped of string

(* The run of a macro on a use at [at], in the program of its module
   [home], whose quotes number the names they write with [mark]: its steps
   so far, and the places of the module's own functions running, innermost
   first. *)
type run = {
  at : Ast.loc;
  home : string;
  mark : string -> int;
  mutable steps : int;
  mutable frames : (string * Ast.loc) list;
  mutable depth : int;
}

let running : run option ref = ref None
let step_limit = 10_000_000
let frame_limit = 10_000

(* macros.step-limits: a call of a function, a method, a closure or a native, or a turn
   of a loop, is a step of the run. *)
let step () =
  match !running with
  | None -> ()
  | Some r ->
      r.steps <- r.steps + 1;
      if r.steps > step_limit then
        raise (Stopped "it took more than 10,000,000 steps")

(* macros.step-limits: a call of a function, a closure or a native is a step. *)
let called = function
  | Body _ | Closure_body _ | Native_code _ -> step ()
  | Structural _ | Variant_of _ -> ()

(* macros.step-limits: the body of [home] at [at] that a call runs, a frame of the run,
   which calls no deeper than 10,000 frames. What ends the run keeps the
   frames that were running, which its diagnostic names. *)
let entering ~home ~at f =
  match !running with
  | None -> f ()
  | Some r -> (
      let frames = r.frames and depth = r.depth in
      if depth >= frame_limit then
        raise (Stopped "it called deeper than 10,000 frames");
      r.depth <- depth + 1;
      if home = r.home then r.frames <- (home, at) :: frames;
      let restore () =
        r.depth <- depth;
        r.frames <- frames
      in
      match f () with
      | v ->
          restore ();
          v
      | exception ((Panicked _ | Stopped _ | Fatal _ | Stack_overflow) as e) ->
          raise e
      | exception e ->
          restore ();
          raise e)

(* Frames *)

let frame t ~home ~tenv ~entry =
  let m : Hir.module_ = Hashtbl.find t.modules home in
  {
    locals = Hashtbl.create 16;
    tenv;
    home;
    file = m.file;
    entry = (if m.std then entry else None);
  }

(* The frame of a body of [home] that [caller] calls at [loc]. *)
let enter t caller loc ~home ~tenv =
  check_memory ();
  let entry =
    match caller.entry with
    | Some _ -> caller.entry
    | None -> Some (caller.file, loc)
  in
  frame t ~home ~tenv ~entry

(* shared.when: inside a [when], each name is the binding of the first
   name whose handle reaches the same value, so that two names reaching one
   value are one place. [Hashtbl.add] shadows an entry and [remove] restores
   it, as nested runs of one [when] need. *)
let aliases : (int, int) Hashtbl.t = Hashtbl.create 8

let local_id id =
  if Hashtbl.length aliases = 0 then id
  else Option.value (Hashtbl.find_opt aliases id) ~default:id

(* A variable that no declaration has: the temporary of a statement, or the
   number of a projection's access (projections.yield and projections.raising-during-access). *)
let next_temporary = ref 0

let temporary () =
  decr next_temporary;
  !next_temporary

let panic fr loc kind fmt =
  Printf.ksprintf
    (fun detail ->
      let file, loc = Option.value fr.entry ~default:(fr.file, loc) in
      raise (Panicked { kind; detail; file; loc }))
    fmt

let check_error t ~home loc =
  let file = (Hashtbl.find t.modules home).Hir.file in
  let detail = "this code has an error, which `check` reports" in
  raise (Panicked { kind = "check-error"; detail; file; loc })

(* Runs [f], whose panics happen at [loc]. *)
let guard fr loc f =
  try f () with Fault.Panic (kind, detail) -> panic fr loc kind "%s" detail
