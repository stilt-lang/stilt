(* The natives of [std.par] (par.std-par), [std.sync] (shared.std-sync) and the
   scopes of [std.task] (tasks.scopes and tasks.scope-failure). A program means its
   sequential run (tasks.sequential-run; parallel-like-sequential), which is what each runs here. *)

open Value
open Eval_state
open Eval_targets

let call t fr loc f args = t.apply t fr loc (target_of_fn t f) args

let elements = function
  | List xs -> Vec.to_list xs
  | _ -> invalid_arg "Eval_parallel.elements"

(* par.fold-tree: a list of [n] elements combines its first [n / 2]
   elements folded with the rest folded, so that the tree depends on [n]
   alone; one element is itself. *)
let rec tree combine = function
  | [] -> invalid_arg "Eval_parallel.tree"
  | [ x ] -> x
  | xs ->
      let n = List.length xs / 2 in
      let left = tree combine (List.filteri (fun i _ -> i < n) xs) in
      let right = tree combine (List.filteri (fun i _ -> i >= n) xs) in
      combine left right

(* par.sequential-meaning and par.panics: [map] and [each] call [f] on the elements from the
   first to the last, and [both] calls [f], then [g], so that the panic
   reported is the first in that order. [each] writes each element in place
   (par.writes-in-place). *)
let par_native t fr loc name args =
  match (name, args) with
  | "map", [| xs; Fn f |] ->
      List
        (Vec.of_list
           (List.map (fun x -> call t fr loc f [| x |]) (elements xs)))
  | "each", [| xs; Fn f |] ->
      let write x =
        let cell = [| x |] in
        ignore (call t fr loc f cell);
        cell.(0)
      in
      args.(0) <- List (Vec.of_list (List.map write (elements xs)));
      unit
  | "both", [| Fn f; Fn g |] ->
      let a = call t fr loc f [||] in
      Tuple [ a; call t fr loc g [||] ]
  | "fold", [| xs; empty; Fn f |] -> (
      match elements xs with
      | [] -> empty
      | xs -> tree (fun a b -> call t fr loc f [| a; b |]) xs)
  | _ -> invalid_arg ("Eval_parallel.par_native: " ^ name)

(* shared.std-sync: [Shared.new] makes a value of its own, which every copy
   of the handle reaches. *)
let sync_native name args =
  match (name, args) with
  | "new", [| v |] -> Shared { held = v }
  | _ -> invalid_arg ("Eval_parallel.sync_native: " ^ name)

let scope_item = { Hir.home = "std.task"; name = "Scope" }
let task_item = { Hir.home = "std.task"; name = "Task" }

(* tasks.scopes and tasks.scope-failure: in the sequential run, [s.spawn] runs its task to
   its end, so a task that raises raises at [s.spawn], and the tasks after
   it never start; the scope ends once its function does, when every task
   of it has ended. *)
let scope_native t fr loc name args =
  match (name, args) with
  | "scope", [| Fn f |] -> call t fr loc f [| Variant (scope_item, []) |]
  | "spawn", [| _; Fn f |] -> Variant (task_item, [ call t fr loc f [||] ])
  | _ -> invalid_arg ("Eval_parallel.scope_native: " ^ name)
