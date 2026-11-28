(* Shared values, tasks, scopes and the parallel calls of std.par as the calculus writes
   them. A program's meaning is its sequential run (tasks.sequential-run), in which a
   shared value is a cell of the world, which every task reaches, and a handle names it;
   a [when] holds the cells it names, binds each name to its cell's value, runs its block
   and puts the values back however the block ends (shared.when). Tasks, scopes, lazy
   values and [std.par] are forms whose code is their run. *)

open Model_json
open Model_types
open Model_ops
open Model_forms

type callbacks = {
  expr : Tast.expr -> Model_json.t;
  block : Tast.block -> Model_json.t;
  place : Tast.expr -> Model_json.t;
}

(* The payload [T] of a [Shared<T>]. *)
let payload t =
  match norm t with
  | Types.Con (_, [ p ]) -> p
  | _ -> outside "a when on something that isn't shared"

(* [Shared.new(v)]: a new cell of the world holding [v], and its handle
   (shared.std-sync). *)
let shared_new cx (e : Tast.expr) v =
  on_world "sharedNew" [ ty cx (payload e.ty) ] [ v ]

(* A name of a [when]: the temporary that holds its handle, the binding that stands for
   its value's place, and its value's type. *)
type name = { handle : string; var : Hir.var; t : Types.ty }

(* The block of a [when] that holds [held], with each binding of [same] written as the
   one it shares a value with (shared.when). *)
let holding (cb : callbacks) cx (b : Tast.block) held same =
  let saved = !aliases in
  aliases := List.map (fun ((v : Hir.var), w) -> (v.id, w)) same @ saved;
  let block =
    Fun.protect ~finally:(fun () -> aliases := saved) (fun () -> cb.block b)
  in
  let names =
    List.map (fun n -> Arr [ Str (var_name n.var); ty cx n.t ]) held
  in
  tag "held" [ Arr names; Arr (List.map (fun n -> var_e n.handle) held); block ]

(* [when a, b { block }]: each handle evaluated, in order; then, for each way the handles of
   names of one type may be equal, the block holding one value for each set of names whose
   handles are, the others written as the first of them (shared.when and
   shared.names-that-may-be-one-place). *)
let when_ (cb : callbacks) cx (e : Tast.expr) pairs (b : Tast.block) =
  cx.when_met <- true;
  let name i ((h : Tast.expr), var) =
    let handle = temp (Printf.sprintf "when-handle-%d" i) e.loc in
    ({ handle; var; t = payload h.ty }, (h, cb.expr h))
  in
  let names = List.mapi name pairs in
  let same_type n h = to_string (ty cx n.t) = to_string (ty cx h.t) in
  let rec split held same = function
    | [] -> holding cb cx b (List.rev held) same
    | n :: rest ->
        let rec against = function
          | [] -> split (n :: held) same rest
          | h :: more ->
              let equal =
                op (Str "sameCell") [ var_e n.handle; var_e h.handle ]
              in
              let one = split held ((n.var, h.var) :: same) rest in
              tag "if" [ equal; ty cx e.ty; one; against more ]
        in
        against (List.filter (same_type n) (List.rev held))
  in
  let bind (n, ((h : Tast.expr), j)) rest =
    tag "letIn" [ Str n.handle; ty cx h.ty; j; rest ]
  in
  List.fold_right bind names (split [] [] (List.map fst names))

(* The result type and the row of a task's function, as the calculus writes them. *)
let task_fn cx (f : Tast.expr) =
  match norm f.ty with
  | Types.Fn ([], r, rw) -> (ty cx r, row cx rw)
  | _ -> outside "a task's function of a type the model lacks"

(* Declares the record of the library that a type of a form of tasks or lazy values is,
   which the calculus's form names though the program may write no binder of it. *)
let declares cx t = ignore (ty cx t)

(* The type argument of a [Task<T>], a [Scope<E>] or a [Lazy<T>]. *)
let arg_of t =
  match norm t with
  | Types.Con (_, [ a ]) -> a
  | _ -> outside "a task, scope or lazy value of a type the model lacks"

(* tasks.sequential-run: [spawn(f)], the form that binds [f] and runs it to its end, its
   value the task's handle (formal/Stilt/Typing/Tasks.lean).
   tasks.implicit-effects-and-capabilities: the call is one through the binding that holds
   [f], a site of [div] as the Reference makes the call one; a closure literal's body is
   still checked where it is written. *)
let spawned cx (e : Tast.expr) (f : Tast.expr) f_e =
  declares cx e.ty;
  let r, rw = task_fn cx f in
  tag "spawn" [ Str (temp "spawned" e.loc); rw; f_e; r ]

(* tasks.sequential-run and tasks.scope-failure: [t.await()] reads the value the task's
   handle holds; [s.spawn(f)] runs [f] as [spawn(f)] does, and its raise leaves as any
   raise. [Shared.new] makes a handle (shared.std-sync). *)
let member_call (cb : callbacks) cx (e : Tast.expr) (owner : Hir.item) name
    (args : Tast.arg list) =
  match (owner.home, owner.name, name, args) with
  | "std.sync", "Shared", "new", [ v ] -> shared_new cx e (cb.expr v.value)
  | "std.task", "Task", "await", [ t ] ->
      declares cx t.value.ty;
      tag "await" [ Str (temp "awaited" e.loc); ty cx e.ty; cb.expr t.value ]
  | "std.task", "Scope", "spawn", [ s; f ] ->
      declares cx e.ty;
      declares cx s.value.ty;
      let r, rw = task_fn cx f.value in
      let err = ty cx (arg_of s.value.ty) in
      tag "scopeSpawn"
        [
          Str (temp "receiver" e.loc);
          err;
          cb.expr s.value;
          Str (temp "spawned" e.loc);
          rw;
          cb.expr f.value;
          r;
        ]
  | _ -> outside "the function %s.%s" (item_name owner) name

(* polymorphism.lazy-values: [Lazy.new(f)] keeps [f], and [l.get()] calls it. *)
let lazy_call (cb : callbacks) cx (e : Tast.expr) name (args : Tast.arg list) =
  match (name, args) with
  | "new", [ f ] ->
      declares cx e.ty;
      tag "lazyNew" [ ty cx (arg_of e.ty); cb.expr f.value ]
  | "get", [ l ] ->
      declares cx l.value.ty;
      tag "lazyGet" [ Str (temp "lazy" e.loc); ty cx e.ty; cb.expr l.value ]
  | _ -> outside "the function std.lazy.Lazy.%s" name

(* Whether a type's functions are of std.sync or std.task. *)
let owns (owner : Hir.item) = owner.home = "std.sync" || owner.home = "std.task"

(* par.sequential-meaning: [par.map(xs, f)], the form that binds the list and [f], then calls
   [f] on the elements from the first to the last and gives the list of their values
   (formal/Stilt/Typing/Par.lean). *)
let par_map cx (e : Tast.expr) (xs : Tast.expr) xs_e f_e =
  tag "parMap"
    [
      Str (temp "par-list" e.loc);
      Str (temp "par-function" e.loc);
      Str (temp "par-values" e.loc);
      Str (temp "par-element" e.loc);
      ty cx (elem xs.ty);
      ty cx (elem e.ty);
      xs_e;
      f_e;
    ]

(* Whether a place is a variable followed by fields, whose evaluation reads nothing. *)
let rec plain (e : Tast.expr) =
  match e.desc with
  | Local _ -> true
  | Field (b, _) | Tuple_field (b, _) -> plain b
  | _ -> false

(* [par.each(inout xs, f)]: the form that binds [f], then calls it on each element of [xs] in
   place, from the first to the last (par.sequential-meaning and par.writes-in-place). *)
let par_each (cb : callbacks) cx (e : Tast.expr) (xs : Tast.expr)
    (f : Tast.expr) =
  if not (plain xs) then outside "a par.each over a place with an index";
  tag "parEach"
    [
      Str (temp "par-function" e.loc);
      Str (temp "par-index" e.loc);
      ty cx (elem xs.ty);
      cb.place xs;
      cb.expr f;
    ]

(* [par.both(f, g)]: the form that binds [f] and [g], calls [f], then [g], and gives the pair of
   their values (par.sequential-meaning). *)
let par_both cx (e : Tast.expr) (f : Tast.expr) (g : Tast.expr) f_e g_e =
  tag "parBoth"
    [
      Str (temp "par-first" e.loc);
      Str (temp "par-second" e.loc);
      ty cx (fn_result f.ty);
      ty cx (fn_result g.ty);
      f_e;
      g_e;
    ]

(* [par.fold(xs, empty, f)]: the form that binds its arguments in order, gives [empty] for an
   empty list, and otherwise calls the function of par.fold-tree, which the program declares
   once, as the model writes it ([FnDecl.foldTree]). *)
let par_fold cx (e : Tast.expr) xs_e empty_e f_e =
  let key = "std.par.fold" in
  if not (List.mem_assoc key cx.helpers) then
    cx.helpers <- (key, Str "foldTree") :: cx.helpers;
  tag "parFold"
    [
      Str (temp "fold-list" e.loc);
      Str (temp "fold-empty" e.loc);
      Str (temp "fold-function" e.loc);
      ty cx e.ty;
      xs_e;
      empty_e;
      f_e;
    ]

(* A call of a function of std.task or std.par by its name. *)
let std_call (cb : callbacks) cx (e : Tast.expr) (i : Hir.item)
    (args : Tast.arg list) =
  let v (a : Tast.arg) = cb.expr a.value in
  match (i.home, i.name, args) with
  | "std.task", "spawn", [ f ] -> spawned cx e f.value (v f)
  | "std.task", ("threads" | "sequential"), [] -> unit_e
  | "std.task", "scope", [ f ] -> (
      (* tasks.scopes: [f] called with a new scope. *)
      match norm f.value.ty with
      | Types.Fn ([ (_, s) ], _, _) ->
          declares cx s;
          tag "scope" [ ty cx (arg_of s); v f; ty cx e.ty ]
      | _ -> outside "a scope's function of a type the model lacks")
  | "std.par", "map", [ xs; f ] -> par_map cx e xs.value (v xs) (v f)
  | "std.par", "each", [ xs; f ] -> par_each cb cx e xs.value f.value
  | "std.par", "both", [ f; g ] -> par_both cx e f.value g.value (v f) (v g)
  | "std.par", "fold", [ xs; d; f ] -> par_fold cx e (v xs) (v d) (v f)
  | _ -> outside "the function %s" (item_name i)
