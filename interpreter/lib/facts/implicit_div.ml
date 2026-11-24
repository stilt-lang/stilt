(* The sites of possible non-termination, [div] (facts.div and facts.descending-self-calls). *)

open Tast
module N = Implicit_names

type context = {
  env : Env.t;
  self : N.key option;
  group : N.key list;
  params : (Ast.mode * Hir.var) list;
  through : Hir.var list;
  proofs : Accept.t option;
}

let mem_var (v : Hir.var) = List.exists (fun (w : Hir.var) -> w.id = v.id)

(* The parameter whose part a place or a binding holds, and how many steps
   from the parameter it is, if it holds one. A step is a field, a tuple
   element or a variant's payload, never an index, a call or a function
   value. *)
let rec source cx parts (e : expr) =
  match e.desc with
  | Local v
    when List.exists
           (fun ((m : Ast.mode), (p : Hir.var)) -> m = Let && p.id = v.id)
           cx.params ->
      Some (v.id, 0)
  | Local v -> Option.map (fun p -> (p, 1)) (List.assoc_opt v.id !parts)
  | Field (base, _) | Tuple_field (base, _) ->
      Option.map (fun (p, d) -> (p, d + 1)) (source cx parts base)
  | _ -> None

(* The bindings of a pattern, with the steps each is from the value matched.
   A list's elements are reached through an index, which isn't a step. *)
let rec bound depth (p : pattern) =
  match p.pat with
  | P_bind v -> [ (v, depth) ]
  | P_variant (_, ps) | P_tuple ps -> List.concat_map (bound (depth + 1)) ps
  | P_record fields ->
      List.concat_map (fun (_, q) -> bound (depth + 1) q) fields
  | P_or ps -> List.concat_map (bound depth) ps
  | P_list _ | P_wild | P_int _ | P_str _ | P_bool _ | P_const _ | P_error -> []

(* facts.descending-self-calls: the bindings that hold a strict part of a [let] parameter, bound
   by a [let], a [match] or an [if let], each with the parameter's id. *)
let strict_parts cx block =
  let parts = ref [] in
  let matched (scrutinee : expr) patterns =
    match source cx parts scrutinee with
    | Some (p, d) ->
        List.iter
          (fun pattern ->
            List.iter
              (fun ((v : Hir.var), k) ->
                if d + k >= 1 then parts := (v.id, p) :: !parts)
              (bound 0 pattern))
          patterns
    | None -> ()
  in
  Walk.iter_block
    ~stmt:(fun s ->
      match s.stmt with Let b -> matched b.value [ b.pattern ] | _ -> ())
    (fun e ->
      match e.desc with
      | Match (scrutinee, arms) ->
          matched scrutinee (List.map (fun (a : arm) -> a.pattern) arms)
      | If_let (p, scrutinee, _, _) -> matched scrutinee [ p ]
      | _ -> ())
    block;
  parts

(* facts.descending-self-calls: whether every self-call passes, in the position of one [let]
   parameter, a strict part of it. *)
let descends cx block self_calls =
  let parts = strict_parts cx block in
  List.exists
    (fun (i, (mode, (p : Hir.var))) ->
      (mode : Ast.mode) = Let
      && List.for_all
           (fun (args : arg list) ->
             match List.nth_opt args i with
             | Some a -> (
                 match source cx parts a.value with
                 | Some (q, d) -> q = p.id && d >= 1
                 | None -> false)
             | None -> false)
           self_calls)
    (List.mapi (fun i p -> (i, p)) cx.params)

let is_self cx c = cx.self <> None && N.callee_key cx.env c = cx.self

(* facts.div: a call through a function value, held by a field, a local binding,
   a parameter marked [escaping] or any other value, such as a call's result.
   A call through a parameter that isn't escaping adds nothing, since its
   effects are counted where the argument is written, and so does a call of a
   closure literal where it is written, whose body is the caller's. *)
let rec through_value cx (f : expr) =
  let ends = "which may never end" in
  match f.desc with
  (* polymorphism.effects-and-escaping: a polymorphic value is called as itself. *)
  | Instantiate (f, _) -> through_value cx f
  | Local v when mem_var v cx.through -> None
  | Closure _ -> None
  | Local v when List.exists (fun (_, p) -> (p : Hir.var).id = v.id) cx.params
    ->
      Some
        (Printf.sprintf
           "this calls the function value of the escaping parameter `%s`, %s"
           v.name ends)
  | Local v ->
      Some
        (Printf.sprintf "this calls the function value that `%s` holds, %s"
           v.name ends)
  | Field (_, name) ->
      Some
        (Printf.sprintf "this calls the function value of the field `%s`, %s"
           name ends)
  | _ -> Some ("this calls a stored function value, " ^ ends)

(* facts.div: a call of a function of the caller's own recursive group, or a use
   of one as a value, except a self-call that descends (facts.descending-self-calls). *)
let in_group cx ~descending c targs ~call =
  let names = N.callee_names cx.env c targs in
  match List.find_opt (fun k -> List.mem k cx.group) names with
  | None -> None
  | Some k when not call ->
      Some
        (Printf.sprintf
           "this names `%s` as a value, which its own recursive group may call \
            without end"
           (N.show_key k))
  | Some _ when is_self cx c && descending -> None
  | Some k when is_self cx c ->
      Some
        (Printf.sprintf
           "this call of `%s` recurses without passing a part of a parameter, \
            so it may never end"
           (N.show_key k))
  | Some k ->
      Some
        (Printf.sprintf
           "this call of `%s` may recurse back here through its group, which \
            may never end"
           (N.show_key k))

let sites cx block =
  let self_calls = ref [] in
  Walk.iter_block
    (fun e ->
      match e.desc with
      | Call (c, _, args, _) when is_self cx c ->
          self_calls := args :: !self_calls
      | _ -> ())
    block;
  (* facts.shrinking-recursion: every self-call shrinks, or every one descends by facts.descending-self-calls. *)
  let structural = descends cx block !self_calls in
  let descending =
    cx.group <> []
    && (structural || Option.fold ~none:false ~some:Accept.shrinks cx.proofs)
  in
  (* facts.closest-rule: what shrinking recursion needs, which each self-call
     that may not end names. *)
  let shrink =
    if structural then None else Option.bind cx.proofs Accept.recursion_note
  in
  let found = ref [] in
  let add ?note e =
    Option.iter (fun why -> found := (e, why, note) :: !found)
  in
  Walk.iter_block
    (fun e ->
      match e.desc with
      | While _ | Loop _ -> (
          (* facts.counting-loops and facts.closest-rule *)
          let why =
            match e.desc with
            | Loop _ -> "this `loop` may never end"
            | _ -> "this `while` loop may never end"
          in
          match Option.map (fun p -> Accept.loop p e) cx.proofs with
          | Some (Proved _) -> ()
          | Some (Unproved "") | None -> add e (Some why)
          | Some (Unproved note) -> add ~note e (Some why))
      | Call_value (f, _) -> add e (through_value cx f)
      (* handlers.implicit-effects-and-capabilities: a performance calls its handler's operation, a
         stored function value. *)
      | Call (Operation (eff, name), _, _, _) ->
          add e
            (Some
               (Printf.sprintf
                  "this performs `%s.%s`, whose handler may never end" eff.name
                  name))
      | Call (c, targs, _, _) ->
          let note = if is_self cx c then shrink else None in
          add ?note e (in_group cx ~descending c targs ~call:true)
      | Callee (c, targs) -> add e (in_group cx ~descending c targs ~call:false)
      | _ -> ())
    block;
  List.rev !found
