(* The demands on the thread axes of modes (modes.fixed-values, modes.contended-values and modes.demands and
   14): a value put in a [Shared<T>], and a task's function, must be
   [portable] (shared.tasks-and-modes), and a closure that [std.par] runs
   must be [calm] and [portable] (par.what-runs-in-parallel). A value is fixed when its
   type holds a view, and contended when it holds a [Shared<T>]; a closure
   literal is either when a binding it captures is. *)

open Tast
module T = Types
module V = Views_types
module S = Views_sources

type demand =
  | Portable  (** E0432 (shared.tasks-and-modes). *)
  | Calm_portable  (** E0431 (par.what-runs-in-parallel). *)

let shared_item = { Hir.home = "std.sync"; name = "Shared" }

let demands : callee -> (int * demand) list = function
  | Member ({ home = "std.sync"; name = "Shared" }, "new") -> [ (0, Portable) ]
  | Function { home = "std.task"; name = "spawn" } -> [ (0, Portable) ]
  (* The receiver is the first argument. *)
  | Member ({ home = "std.task"; name = "Scope" }, "spawn") -> [ (1, Portable) ]
  | Function { home = "std.par"; name = "map" | "each" } ->
      [ (1, Calm_portable) ]
  | Function { home = "std.par"; name = "both" } ->
      [ (0, Calm_portable); (1, Calm_portable) ]
  | Function { home = "std.par"; name = "fold" } -> [ (2, Calm_portable) ]
  | _ -> []

let demanded callee i = List.mem_assoc i (demands callee)

(* Whether a type holds a type that [p] accepts, at any depth. *)
let rec holds p ty =
  let ty = T.resolve ty in
  p ty
  ||
  match ty with
  | Con (_, ts) | Tuple ts | App (_, ts) -> List.exists (holds p) ts
  | Record fields -> List.exists (fun (_, t) -> holds p t) fields
  | Spread (_, t) -> holds p t
  | Fn (ps, r, _) -> List.exists (fun (_, t) -> holds p t) ps || holds p r
  | Forall f -> holds p f.body
  | Handler _ | Param _ | Var _ | Value _ | Error -> false

(* modes.fixed-values, and views.fixed *)
let fixed_type =
  holds (function Con (item, _) -> V.is_view_con item | _ -> false)

(* modes.contended-values *)
let contended_type =
  holds (function Con (item, _) -> item = shared_item | _ -> false)

(* The closure literals that [let] binds to a name, by the name's id. *)
let closures block =
  let found = Hashtbl.create 8 in
  Walk.iter_block
    ~stmt:(fun s ->
      match s.stmt with
      | Let { pattern = { pat = P_bind v; _ }; value; _ } -> (
          match value.desc with
          | Closure _ -> Hashtbl.replace found v.id value
          | _ -> ())
      | _ -> ())
    ignore block;
  found

(* The uses, in a closure literal's body, of the bindings it captures:
   those that aren't bound inside it, in the order they are written. *)
let captures (body : expr) =
  let bound = S.bound_in body in
  let found = ref [] in
  Walk.iter
    (fun (e : expr) ->
      match e.desc with
      | Local v when not (List.mem v.id bound) -> found := (v, e) :: !found
      | _ -> ())
    body;
  List.rev !found

type ctx = {
  sources : S.t;
  closures : (int, expr) Hashtbl.t;
  report : Code.t -> Ast.loc -> string -> unit;
}

(* The closure literal that an argument is, or that the binding it names
   holds. *)
let literal ctx (a : expr) =
  match a.desc with
  | Closure (_, _, body) -> Some body
  | Local v -> (
      match Hashtbl.find_opt ctx.closures v.id with
      | Some { desc = Closure (_, _, body); _ } -> Some body
      | _ -> None)
  | _ -> None

(* A captured binding that is fixed: of a type that holds a view, or a
   closure that captures one (views.fixed). *)
let fixed ctx ((_ : Hir.var), (use : expr)) =
  fixed_type use.ty || S.carries ctx.sources use

let check_portable ctx (a : expr) =
  match literal ctx a with
  | Some body -> (
      match List.find_opt (fixed ctx) (captures body) with
      | Some (v, use) ->
          ctx.report Code.e0432 use.loc
            (Printf.sprintf
               "this task's function captures `%s`, a view, which can't reach \
                another task"
               v.name)
      | None -> ())
  | None ->
      if fixed_type a.ty || S.carries ctx.sources a then
        ctx.report Code.e0432 a.loc
          "this value holds a view, which can't be put in a `Shared<T>`"

let check_calm_portable ctx (a : expr) =
  let reached =
    match literal ctx a with
    | Some body ->
        List.find_map
          (fun ((v : Hir.var), (use : expr)) ->
            if contended_type use.ty then Some (v.name, "contended")
            else if fixed ctx (v, use) then Some (v.name, "fixed: a view")
            else None)
          (captures body)
    | None -> None
  in
  Option.iter
    (fun (name, why) ->
      ctx.report Code.e0431 a.loc
        (Printf.sprintf
           "this closure can't run in parallel: it reaches `%s`, which is %s"
           name why))
    reached

let errors _env ~file block =
  let found = ref [] in
  let report code loc message =
    found := Diagnostic.at ~file code loc message :: !found
  in
  let ctx = { sources = S.collect block; closures = closures block; report } in
  Walk.iter_block
    (fun (e : expr) ->
      match e.desc with
      | Call (callee, _, args, _) ->
          List.iter
            (fun (i, demand) ->
              Option.iter
                (fun (a : arg) ->
                  match demand with
                  | Portable -> check_portable ctx a.value
                  | Calm_portable -> check_calm_portable ctx a.value)
                (List.nth_opt args i))
            (demands callee)
      | _ -> ())
    block;
  List.rev !found
