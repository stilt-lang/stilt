(* meta.reflects and meta.types-without-shape: the functions that reflect, and the types they are
   given. Which function reflects on which of its type parameters is an
   inferred fact, a least fixed point over the calls that bodies make; then
   each body's calls and names of such functions are checked (E0350). *)

open Tast
module T = Types
module K = Implicit_names
module R = Reflects_items
module W = Reflects_walk

type need = W.need

(* For each item, by key, what it needs of each of its type parameters, by
   id, in the order found. *)
type t = (K.key, (int * need list) list) Hashtbl.t

let needs (facts : t) key (v : Hir.var) =
  Option.value ~default:[]
    (Option.bind (Hashtbl.find_opt facts key) (List.assoc_opt v.id))

let same (a : need) (b : need) =
  a.parts = b.parts && List.sort compare a.guards = List.sort compare b.guards

(* Adds [need] to what [key] needs of [v], and tells whether it was new. *)
let add (facts : t) key (v : Hir.var) need =
  let known = needs facts key v in
  if List.exists (same need) known then false
  else
    let others =
      List.remove_assoc v.id
        (Option.value ~default:[] (Hashtbl.find_opt facts key))
    in
    Hashtbl.replace facts key ((v.id, known @ [ need ]) :: others);
    true

(* The traits that the body's bound tests name on each type parameter, which
   guard what it reflects on (meta.reflects). *)
let guards block =
  let found = ref [] in
  Walk.iter_block
    (fun (e : expr) ->
      match e.desc with
      | Reflect (Implements (ty, bounds)) -> (
          match T.resolve ty with
          | Param v ->
              found :=
                List.map (fun (b : T.bound) -> (v.id, b.trait)) bounds @ !found
          | _ -> ())
      | _ -> ())
    block;
  fun (v : Hir.var) ->
    List.sort_uniq compare
      (List.filter_map
         (fun (id, trait) -> if id = v.id then Some trait else None)
         !found)

(* What a body is: its item, its type parameters with their bounds, those
   that its callers can't see, and its code. *)
type body = {
  key : K.key option;
  bounds : Env.bounds;
  unseen : Hir.var list;
  code : block;
}

(* A use of an item that may reflect, met in a body: [T.shape()] on a type,
   or a call or a name of a function with the types it gives. *)
type site =
  | Names_shape of T.ty * Ast.loc
  | Gives of K.key * (Hir.var * T.ty) list * Ast.loc * expr list

(* A call or a name of [callee], and the impls whose bounds the types it
   gives meet, whose own type parameters are checked there (meta.unseen-instantiations). *)
let gives env site callee targs loc args =
  Option.iter
    (fun (key, sub) ->
      site (Gives (key, sub, loc, args));
      List.iter
        (fun ((v : Hir.var), bounds) ->
          match List.find_opt (fun ((w : Hir.var), _) -> w.id = v.id) sub with
          | Some (_, t) ->
              List.iter
                (fun (k, s) -> site (Gives (k, s, loc, args)))
                (R.met env bounds t)
          | None -> ())
        (fst (R.params env key)))
    (R.target env callee targs)

let sites env block =
  let found = ref [] in
  let origins = Hashtbl.create 8 in
  let site e = found := e :: !found in
  Walk.iter_block
    (fun (e : expr) ->
      match e.desc with
      | Reflect (Shape_of ty) -> site (Names_shape (ty, e.loc))
      | Call (callee, targs, args, _) | Project (callee, targs, args, _) ->
          (* meta.building: the polymorphic argument of [fields.build] stands for
             each field of the type. *)
          (match (callee, targs, args) with
          | Member (owner, "build"), [ of_ ], [ _; { value; _ } ]
            when owner = Meta.item "Fields" -> (
              match value.desc with
              | Generalize (vars, _) ->
                  List.iter
                    (fun (v : Hir.var) -> Hashtbl.replace origins v.id of_)
                    vars
              | _ -> ())
          | _ -> ());
          gives env site callee targs e.loc
            (List.map (fun (a : arg) -> a.value) args)
      | Callee (callee, targs) -> gives env site callee targs e.loc []
      | _ -> ())
    block;
  (List.rev !found, origins)

(* A body's checks, with what it reflects on: [param] is told of each type
   parameter of the body met where a site's type is walked, and [fail] of
   the first type of a site that fails a need, each site once. *)
let visit facts env body ~param ~fail =
  let sites, origins = sites env body.code in
  let guards_of = guards body.code in
  let met ty trait =
    List.concat_map
      (fun (key, sub) ->
        List.concat_map
          (fun ((v : Hir.var), t) ->
            List.map (fun n -> (n, t)) (needs facts key v))
          sub)
      (R.met env [ { Env.trait; args = [] } ] ty)
  in
  let sc = { W.env; bounds = body.bounds; origins; met } in
  let check loc args need ty =
    match W.first sc ~param:(param loc) need ty with
    | Some f ->
        fail loc args f need;
        true
    | None -> false
  in
  List.iter
    (function
      | Names_shape (ty, loc) ->
          let guards =
            match T.resolve ty with Param v -> guards_of v | _ -> []
          in
          ignore (check loc [] { W.parts = false; guards; chain = [] } ty)
      | Gives (key, sub, loc, args) ->
          ignore
            (List.exists
               (fun ((v : Hir.var), t) ->
                 List.exists (fun n -> check loc args n t) (needs facts key v))
               sub))
    sites

(* The bounds of a body: those of its item's signature, or, for a method of an
   impl whose trait fails to resolve, which no table holds, its own type
   parameters, which its callers see as any function's (errors.error-type). *)
let signed (bounds : Env.bounds) (own : Hir.var list) =
  if bounds = [] then List.map (fun v -> (v, [])) own else bounds

let hidden body (p : Hir.var) =
  List.exists (fun (v : Hir.var) -> v.id = p.id) body.unseen

(* The bodies of the program's items. *)
let bodies env (program : program) =
  let body key (f : fn_def) =
    match f.body with
    | Code code ->
        let bounds, unseen = R.params env key in
        let bounds = signed bounds f.type_params in
        Some { key = Some key; bounds; unseen; code }
    | Native | Broken -> None
  in
  List.filter_map Fun.id
    (List.map (fun (i, f) -> body (K.Function i) f) program.functions
    @ List.map (fun ((o, n), f) -> body (K.Member (o, n)) f) program.members
    @ List.map
        (fun ((tr, o, n), f) -> body (K.Impl_method (tr, o, n)) f)
        program.impl_methods
    @ List.map
        (fun ((tr, n), f) -> body (K.Default_method (tr, n)) f)
        program.default_methods)

(* meta.reflects: the least fixed point. A body reflects on each of its type
   parameters that a site's walk meets, with the guards and the chain of
   the need it met, but for those its callers can't see, which are errors
   where they are met (meta.unseen-instantiations). *)
let infer env program : t =
  let facts = Hashtbl.create 64 in
  let all = bodies env program in
  let rec fix () =
    let grew = ref false in
    List.iter
      (fun body ->
        let param _ p (n : need) =
          match body.key with
          | Some key when not (hidden body p) ->
              if add facts key p { n with chain = R.name key :: n.chain } then
                grew := true
          | _ -> ()
        in
        visit facts env body ~param ~fail:(fun _ _ _ _ -> ()))
      all;
    if !grew then fix ()
  in
  fix ();
  facts

(* meta.types-without-shape and meta.unseen-instantiations: E0350 at the first argument whose type holds the type that
   fails, or at the call or the name, and at a site that reflects on a type
   parameter that the body's callers can't see. *)
let errors facts env ~file ~key ~own block =
  let bounds, unseen =
    match key with Some key -> R.params env key | None -> ([], [])
  in
  let bounds = signed bounds own in
  let body = { key; bounds; unseen; code = block } in
  let found = ref [] in
  let report loc message =
    if
      not
        (List.exists
           (fun (d : Diagnostic.t) -> d.line = loc.Ast.line && d.col = loc.col)
           !found)
    then found := Diagnostic.at ~file Code.e0350 loc message :: !found
  in
  let param loc p (_ : need) =
    if hidden body p then
      report loc
        (Printf.sprintf
           "this reflects on `%s`, which callers that reach this function \
            through a bound never give, so nothing checks that it has a shape"
           p.name)
  in
  let fail loc args (f : W.failure) need =
    let at =
      match
        List.find_opt (fun (a : expr) -> W.holds env a.ty f.missing) args
      with
      | Some a -> a.loc
      | None -> loc
    in
    report at (W.message f need)
  in
  visit facts env body ~param ~fail;
  List.rev !found
