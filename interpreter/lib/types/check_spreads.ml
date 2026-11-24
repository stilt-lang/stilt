(* Spread expressions, which map over the tuples of a pack (variadics.spread-expressions and variadics.pack-tuples). *)

module T = Types
module A = Tast
open Check_state
open Check_expect

let is_spread (e : Hir.expr) = match e.desc with Spread _ -> true | _ -> false

(* The packs of the pack tuples a spread names, each once. *)
let packs_of (named : (Hir.var * T.ty) list) =
  List.fold_left
    (fun packs (_, p) ->
      if List.exists (fun q -> T.same_pack p q) packs then packs
      else packs @ [ p ])
    [] (List.rev named)

(* variadics.spread-expressions and variadics.spread-checks: [..e], whose pack tuples, named in [e], stand for their elements
   there. It names at least one, all of one pack, and stands inside no other
   spread (E0343). *)
let spread ctx loc (e : Hir.expr) : A.expr =
  let st = ctx.st in
  match st.spreading with
  | Some _ ->
      error st Code.e0343 loc "a spread can't stand inside another spread";
      ignore (abandon ctx e);
      error_node loc
  | None -> (
      let sp =
        { named = []; mixed_at = None; closures = 0; names_broken = false }
      in
      st.spreading <- Some sp;
      let body =
        Fun.protect
          ~finally:(fun () -> st.spreading <- None)
          (fun () -> infer ctx None e)
      in
      match packs_of sp.named with
      | [ pack ] ->
          let tuples = List.rev_map fst sp.named in
          node (Spread { pack; tuples; body }) (T.Spread (pack, body.ty)) loc
      (* A tuple or a name whose type is an error was reported where it was
         written (errors.error-type), even when the operation on it was given
         up. *)
      | [] when sp.names_broken -> error_node loc
      | [] ->
          error st Code.e0343 loc
            "this spread names no tuple of a pack, so nothing says how many \
             values it stands for";
          error_node loc
      | _ ->
          error st Code.e0343
            (Option.value sp.mixed_at ~default:loc)
            "this spread names tuples of two packs, which may differ in \
             length; a spread maps tuples of one pack";
          error_node loc)

(* A local of type [ty] named where a spread is being checked. *)
let names_local st ty =
  match st.spreading with
  | Some sp when T.mentions_error ty -> sp.names_broken <- true
  | _ -> ()

(* A pack tuple named where a spread is being checked: its element, or E0343
   inside a closure there, which could run for any element. *)
let named_in_spread st loc (v : Hir.var) pack element =
  match st.spreading with
  | None -> None
  | Some sp ->
      if not (List.mem_assoc v sp.named) then (
        (match List.rev sp.named with
        | (_, first) :: _
          when sp.mixed_at = None && not (T.same_pack first pack) ->
            sp.mixed_at <- Some loc
        | _ -> ());
        sp.named <- (v, pack) :: sp.named);
      if sp.closures > 0 then (
        error st Code.e0343 loc
          "`%s` is a tuple of a pack, which a closure inside a spread can't \
           name: the closure could run for any of its elements"
          v.name;
        Some (error_node loc))
      else Some (node (Local v) element loc)

(* Checks a closure's body inside a spread as inside a closure. *)
let in_closure st f =
  match st.spreading with
  | None -> f ()
  | Some sp ->
      sp.closures <- sp.closures + 1;
      Fun.protect ~finally:(fun () -> sp.closures <- sp.closures - 1) f

(* variadics.spread-expressions: a tuple with spreads among its elements, the type of each spread
   the spread of its pack over the type of its body. *)
let spread_tuple ctx loc (es : Hir.expr list) =
  let items =
    List.map
      (fun (e : Hir.expr) ->
        match e.desc with
        | Spread inner -> spread ctx e.loc inner
        | _ -> infer ctx None e)
      es
  in
  (* errors.error-type: a spread that gave the error type says nothing of how many
     elements the tuple has, so the tuple has the error type. *)
  let broken (e : Hir.expr) (i : A.expr) =
    match (e.desc, T.resolve i.ty) with Spread _, T.Error -> true | _ -> false
  in
  if List.exists2 broken es items then error_node loc
  else
    node (Tuple items) (T.Tuple (List.map (fun (i : A.expr) -> i.ty) items)) loc

(* variadics.spread-expressions: a list with spreads among its elements, whose type names no pack,
   so that every element has it (E0311). *)
let spread_list ctx expected loc (es : Hir.expr list) =
  let st = ctx.st in
  let elem =
    match Option.map T.resolve expected with
    | Some (Con (item, [ t ])) when item = T.prelude_item "List" -> t
    | _ -> fresh st loc
  in
  let item (e : Hir.expr) =
    match e.desc with
    | Spread inner -> (
        let s = spread ctx e.loc inner in
        match s.desc with
        | Spread { pack; body; _ } when Packs.mentions_pack pack body.ty ->
            error st Code.e0311 e.loc
              "each value of this spread has the type `%s`, which differs from \
               one element of the pack to the next, so they can't make a list"
              (show body.ty);
            s
        | Spread { body; _ } ->
            expect st e.loc ~expected:elem body.ty;
            s
        (* A spread that was given up has the error type, which its elements
           take too (errors.error-type). *)
        | _ ->
            expect st e.loc ~expected:elem s.ty;
            s)
    | _ -> check ctx elem e
  in
  node (List (List.map item es)) (T.list elem) loc

(* variadics.pack-inference and variadics.spread-expressions: the arguments of a call where the callee's parameters or
   the arguments hold a spread: the arguments' types, a spread's that of its
   pack over its body, are the parameters'. *)
let spread_arguments ctx loc params (args : Hir.arg list) : A.arg list =
  let st = ctx.st in
  let values =
    List.map
      (fun (a : Hir.arg) ->
        match a.value.desc with
        | Spread inner -> spread ctx a.value.loc inner
        | _ -> infer ctx None a.value)
      args
  in
  let given = T.Tuple (List.map (fun (v : A.expr) -> v.ty) values) in
  let wanted = T.Tuple (List.map snd params) in
  if not (Check_unify.unify given wanted) then
    error st Code.e0311 loc "this call's arguments are `%s`, but it takes `%s`"
      (show given) (show wanted);
  List.map (fun value -> { A.mode = by_value; value }) values
