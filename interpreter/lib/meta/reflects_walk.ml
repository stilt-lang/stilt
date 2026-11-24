(* meta.types-without-shape: the walk of a type that a function that reflects is given,
   depth first in the order of meta.shapes, each type once, skipping a type with
   an impl of a guard and what it holds. *)

module T = Types
module S = Meta_shapes

(* What a function needs of the type it reflects on: a shape, and with
   [parts] one for each type its values hold, at any depth, but where a type
   has an impl of one of [guards]. [chain] names the functions that reflect,
   from the one instantiated to the one that names [T.shape()]. *)
type need = { parts : bool; guards : Hir.item list; chain : string list }

(* Where a walk is: the body's bounds, its type parameters, and the rigid
   types of the polymorphic arguments of [fields.build], each with the type
   whose fields it stands for (meta.fields). [met] gives what the methods of the
   impl with which a type meets a guard need of the types it gives the
   impl's own type parameters, which are checked there (meta.unseen-instantiations). *)
type scope = {
  env : Env.t;
  bounds : Env.bounds;
  origins : (int, T.ty) Hashtbl.t;
  met : T.ty -> Hir.item -> (need * T.ty) list;
}

(* A type without a shape, with the types that hold it, outermost first. *)
type failure = { missing : T.ty; held : string list }

let show = S.describe

let guard sc (need : need) ty =
  List.find_opt
    (fun trait -> Env.implements sc.env sc.bounds ty trait = Env.Yes)
    need.guards

let own sc (p : Hir.var) =
  List.exists (fun ((v : Hir.var), _) -> v.id = p.id) sc.bounds

(* The type whose shape a fresh type, or a rigid type of [build]'s
   argument, is part of. *)
let origin sc (p : Hir.var) =
  match Meta.origin p with
  | Some o -> Some o
  | None -> Hashtbl.find_opt sc.origins p.id

(* Each part of a type, with how a message names what holds it. *)
let parts ty (case : S.case) =
  let t = show ty in
  match case with
  | Leaf _ -> []
  | Holds (_, ts) -> List.map (fun p -> (p, "`" ^ t ^ "`")) ts
  | Fields (_, fields) ->
      List.map
        (fun (n, p) -> (p, Printf.sprintf "the field `%s` of `%s`" n t))
        fields
  | Cases variants ->
      List.concat_map
        (fun ((v : Hir.item), ps) ->
          List.map
            (fun p -> (p, Printf.sprintf "the variant `%s` of `%s`" v.name t))
            ps)
        variants

(* The first type that fails [need], walking [ty]. [param] is told of each
   type parameter of the body met, which the body then reflects on. *)
let rec walk sc ~param (need : need) seen held ty =
  let ty = T.resolve ty in
  match guard sc need ty with
  | Some trait ->
      List.find_map
        (fun (n, t) -> walk sc ~param n seen held t)
        (sc.met ty trait)
  | None -> (
      match ty with
      | Param p when own sc p ->
          param p need;
          None
      | Param p -> (
          match origin sc p with
          | Some o -> walk sc ~param { need with parts = true } seen held o
          | None -> Some { missing = ty; held })
      (* A type left unknown, by an earlier error or one that nothing
         solved, which E0312 reports, fails nothing here, since only root
         causes are reported (errors.root-causes). *)
      | Var _ | Error -> None
      | _ -> (
          match S.case_of sc.env ty with
          | None -> Some { missing = ty; held }
          | Some _
            when (not need.parts) || List.exists (Env_signatures.equal ty) !seen
            ->
              None
          | Some case ->
              seen := ty :: !seen;
              List.find_map
                (fun (p, by) -> walk sc ~param need seen (held @ [ by ]) p)
                (parts ty case)))

let first sc ~param need ty = walk sc ~param need (ref []) [] ty

(* Whether a value of type [ty] holds a value of type [missing]. *)
let holds env ty missing =
  let seen = ref [] in
  let rec go ty =
    let ty = T.resolve ty in
    Env_signatures.equal ty missing
    || (not (List.exists (Env_signatures.equal ty) !seen))
       &&
       (seen := ty :: !seen;
        let args =
          match ty with
          | Con (_, ts) | Tuple ts | App (_, ts) -> ts
          | Record fields -> List.map snd fields
          | Fn (ps, r, _) -> r :: List.map snd ps
          | _ -> []
        in
        let inside =
          match S.case_of env ty with Some case -> S.parts case | None -> []
        in
        List.exists go (args @ inside))
  in
  go ty

(* The chain without a function named twice in a row, as recursion gives. *)
let rec squeeze = function
  | a :: (b :: _ as rest) when a = b -> squeeze rest
  | a :: rest -> a :: squeeze rest
  | [] -> []

let message (f : failure) (need : need) =
  let held =
    match List.rev f.held with
    | [] -> ""
    | inner :: outer ->
        Printf.sprintf ", which %s holds%s" inner
          (String.concat ""
             (List.map (fun o -> Printf.sprintf ", in %s" o) outer))
  in
  let chain =
    match squeeze need.chain with
    | [] -> "`T.shape()` reads its shape"
    | [ one ] -> Printf.sprintf "`%s` reflects on it" one
    | first :: rest ->
        Printf.sprintf
          "`%s` reflects on it, through %s, which names `T.shape()`" first
          (String.concat ", then " (List.map (fun n -> "`" ^ n ^ "`") rest))
  in
  Printf.sprintf "`%s` has no shape%s, but %s" (show f.missing) held chain
