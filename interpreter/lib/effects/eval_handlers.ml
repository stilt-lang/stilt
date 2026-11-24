(* Handlers at run time (handlers.with and handlers.resuming), one-shot and deep, on the
   effects of OCaml 5. The handlers installed form a stack, innermost first,
   that a performance searches for its effect. A handler that resumes at
   once is called where the operation is performed; one that takes control
   captures the rest of its [with]'s block as a continuation, which it
   resumes at most once. *)

open Value
open Eval_state
open Eval_targets

(* A handler installed by a [with], with the stack outside it, where its
   operations run when it takes control, and the frame and the position of
   the [with]. *)
type installed = {
  id : int;
  handler : handler;
  outside : installed list;
  frame : frame;
  at : Ast.loc;
}

let stack : installed list ref = ref []
let next_id = ref 0

(* The [resume]s of the bodies of operations that take control, innermost
   first. A [resume] is in no closure literal (handlers.resuming), so it belongs to the
   innermost body that runs. *)
let resumes : (value -> value) list ref = ref []

(* A performance of an operation of the handler of this id, which takes
   control, on its arguments. *)
type _ Effect.t += Op : int * string * value array -> value Effect.t

let literal t fr ~expr (h : Tast.handler) =
  let op (name, e) =
    match expr t fr e with
    | Fn f -> (name, f)
    | _ -> invalid_arg "Eval_handlers.literal"
  in
  Handler { heffect = h.heffect; control = h.control; ops = List.map op h.ops }

let operation (h : handler) name =
  match List.assoc_opt name h.ops with
  | Some fn -> fn
  | None -> invalid_arg "Eval_handlers.operation"

(* handlers.resuming: the body of an operation that takes control, run with the
   handlers outside its [with]. [resume v] runs the rest of the block from
   the performance, with the handlers and the [resume]s it had there, and
   gives what the block ends with. A body that never resumes drops the
   block, whose value is the body's. *)
let take_control t entry name values
    (k : (value, value) Effect.Deep.continuation) =
  let site = !stack and site_resumes = !resumes in
  let resumed = ref false in
  let resume v =
    resumed := true;
    let mine = !resumes in
    stack := site;
    resumes := site_resumes;
    (* A rest that raises or jumps leaves the body through here, which never
       goes on: the handlers are the body's again, however the rest ends. *)
    Fun.protect
      ~finally:(fun () ->
        stack := entry.outside;
        resumes := mine)
      (fun () -> Effect.Deep.continue k v)
  in
  let drop () =
    if not !resumed then
      try ignore (Effect.Deep.discontinue k Abandoned) with Abandoned -> ()
  in
  stack := entry.outside;
  resumes := resume :: site_resumes;
  let fn = operation entry.handler name in
  match t.apply t entry.frame entry.at (target_of_fn t fn) values with
  | v ->
      drop ();
      v
  | exception e ->
      drop ();
      raise e

(* Runs the block of a [with] of a handler that takes control, whose
   operations' performances reach it as effects. *)
let controlled t entry run =
  Effect.Deep.match_with run ()
    {
      retc = Fun.id;
      exnc = raise;
      effc =
        (fun (type a) (eff : a Effect.t) ->
          match eff with
          | Op (id, name, values) when id = entry.id ->
              Some
                (fun (k : (a, value) Effect.Deep.continuation) ->
                  take_control t entry name values k)
          | _ -> None);
    }

(* handlers.with: runs [run] with the handler [hv] installed, and the stack as it
   was once it ends, however it ends. [async]'s handlers install nothing:
   every task runs to its end where it starts, which is the meaning of a
   program under each (tasks.sequential-run and tasks.same-output-under-every-handler). *)
let install t fr at hv run =
  match hv with
  | Handler h when h.heffect = Types.async_effect -> run ()
  | Handler handler ->
      incr next_id;
      let outside = !stack and saved = !resumes in
      let entry = { id = !next_id; handler; outside; frame = fr; at } in
      stack := entry :: outside;
      Fun.protect
        ~finally:(fun () ->
          stack := outside;
          resumes := saved)
        (fun () -> if handler.control then controlled t entry run else run ())
  | _ -> invalid_arg "Eval_handlers.install"

(* handlers.with: a performance calls the nearest handler of its effect. One that
   resumes at once is called here, with the stack that was outside its
   [with] while its body runs, so that its body performs every effect, its
   own included, on the handlers outside it (handlers.with and handlers.resuming); [call] calls its
   operation on the arguments. One that takes control is reached as an
   effect, with the arguments' values. *)
let perform ~call ~values eff name =
  match
    List.find_opt (fun (e : installed) -> e.handler.heffect = eff) !stack
  with
  | None -> invalid_arg ("Eval_handlers.perform: no handler of " ^ eff.Hir.name)
  | Some entry when not entry.handler.control ->
      let site = !stack in
      stack := entry.outside;
      Fun.protect
        ~finally:(fun () -> stack := site)
        (fun () -> call (operation entry.handler name))
  | Some entry -> Effect.perform (Op (entry.id, name, values ()))

(* handlers.resuming: [resume v] in the body of the operation that runs. *)
let resume v =
  match !resumes with r :: _ -> r v | [] -> invalid_arg "Eval_handlers.resume"
