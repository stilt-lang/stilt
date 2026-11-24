(* [when] at run time (shared.when-order). The reference interpreter runs one task at a
   time, each to its end where it starts (tasks.sequential-run), so a [when] holds
   its values by running its block: no other block runs meanwhile. *)

open Value
open Eval_state

(* The values that the [when]s whose blocks haven't ended hold. *)
let held : shared list ref = ref []

(* How many [Lazy] values are being computed, one inside another's
   computation (polymorphism.lazy-values). *)
let computing = ref 0

let computing_lazy f =
  incr computing;
  Fun.protect ~finally:(fun () -> decr computing) f

(* shared.when-on-value-already-held: a [when] on a value that one of them holds panics, before
   it holds anything; polymorphism.lazy-waits-for-nothing: so does one that runs while a [Lazy]
   computes its value, which waits for nothing. *)
let check_free fr loc cells =
  if !computing > 0 then
    panic fr loc "deadlock"
      "this `when` runs while a `Lazy` computes its value, which waits for \
       nothing"
  else if List.exists (fun cell -> List.exists (( == ) cell) !held) cells then
    panic fr loc "deadlock"
      "this `when` waits for a value that a `when` around it holds"

(* shared.when-on-value-already-held: each name's variable holds its value for the block, but a name
   whose handle reaches the value of an earlier name is that name's place.
   Once the block ends, however it ends, each value holds what its variable
   holds then. *)
let run t fr loc ~expr names run_block =
  let handle (h, (v : Hir.var)) =
    match expr t fr h with
    | Shared cell -> (cell, v)
    | _ -> invalid_arg "Eval_when.run"
  in
  let handles = List.map handle names in
  check_free fr loc (List.map fst handles);
  let outside = !held in
  held := List.map fst handles @ outside;
  let roots =
    List.fold_left
      (fun roots (cell, (v : Hir.var)) ->
        match List.find_opt (fun (c, _) -> c == cell) roots with
        | Some (_, (root : Hir.var)) ->
            Hashtbl.add aliases v.id root.id;
            roots
        | None ->
            Hashtbl.add aliases v.id v.id;
            Hashtbl.replace fr.locals v.id cell.held;
            (cell, v) :: roots)
      [] handles
  in
  let release () =
    List.iter
      (fun (cell, (v : Hir.var)) ->
        Option.iter (fun x -> cell.held <- x) (Hashtbl.find_opt fr.locals v.id))
      roots;
    List.iter (fun (_, (v : Hir.var)) -> Hashtbl.remove aliases v.id) handles;
    held := outside
  in
  Fun.protect ~finally:release run_block

(* expressions.capture: a closure literal captures copies of the variables in
   scope, the names of the [when]s around it among them. *)
let captured fr =
  let captured = Hashtbl.fold Imap.add fr.locals Imap.empty in
  Hashtbl.fold
    (fun id root captured ->
      match Hashtbl.find_opt fr.locals root with
      | Some x when not (Imap.mem id captured) -> Imap.add id x captured
      | _ -> captured)
    aliases captured
