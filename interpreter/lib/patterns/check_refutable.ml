(* Whether patterns can fail to match (patterns.irrefutable-positions), and the variants that
   names written without a module name in them (patterns.variants-by-type). *)

module T = Types
open Check_state

(* patterns.variants-by-type: the variant [name] of the type [ty], when [ty] is known by
   its outermost constructor to be a variant type with a variant [name]. *)
let matched_variant st ty name : Hir.item option =
  match T.resolve ty with
  | Con (owner, _) -> (
      match Env.type_info st.env owner with
      | Some { def = Variants variants; _ } when List.mem_assoc name variants ->
          Some { home = owner.home; name }
      | _ -> None)
  | _ -> None

(* The arguments of [ty] as a value of the type constructor [owner], or the
   error type for each when [ty] isn't known to be one. *)
let arguments ty (owner : Hir.item) params =
  match T.resolve ty with
  | Con (o, args) when o = owner && List.length args = List.length params ->
      args
  | _ -> List.map (fun _ -> T.Error) params

(* The types of [ps], the parts of a pattern of type [ty] whose types are
   [declared] in terms of [params] of [owner], when [ty] is given. *)
let parts ty owner params declared ps =
  match ty with
  | Some t when List.length declared = List.length ps ->
      let sub = T.subst (List.combine params (arguments t owner params)) [] in
      List.map (fun d -> Some (sub d)) declared
  | _ -> List.map (fun _ -> None) ps

(* generics.array-patterns: the array that a list pattern matches, given the type it
   is matched against, or the [Option] of it before a let-else's [else],
   which a pattern that can't fail reads as [let p = (e else x)] (patterns.let-else). *)
let matched_array ty =
  match Option.map T.resolve ty with
  | Some (Con (o, [ t ])) when o = T.prelude_item "Option" ->
      Check_arrays.parts t
  | Some t -> Check_arrays.parts t
  | None -> None

(* Whether a list pattern matches an array, given its type or as checking
   found it. One that doesn't fit the array's size is an error of its own,
   E0311, which makes it no refutable pattern. *)
let array_fit st ty (p : Hir.pattern) =
  Option.is_some (matched_array ty) || Hashtbl.mem st.arrays p.loc

(* patterns.irrefutable-positions: a pattern is irrefutable when its form alone guarantees a
   match, given how many variants the types it names have. A name written
   without a module names what checking the pattern found it to name, or,
   before the pattern is checked, what it names as matched against [ty] where
   that is given (patterns.pattern-forms), as for a let-else (patterns.let-else). *)
let rec irrefutable st ?ty (p : Hir.pattern) =
  match p.desc with
  | P_wild | P_bind _ | P_error -> true
  | P_tuple ps ->
      let items =
        match Option.map T.resolve ty with
        | Some (Tuple ts) when List.length ts = List.length ps ->
            List.map Option.some ts
        | _ -> List.map (fun _ -> None) ps
      in
      List.for_all2 (fun q ty -> irrefutable st ?ty q) ps items
  | P_record (hty, fields, _) ->
      let declared = record_parts st ty hty in
      List.for_all
        (fun (f : Hir.field_pattern) ->
          irrefutable st ?ty:(List.assoc_opt f.field.desc declared) f.pattern)
        fields
  (* records.anonymous-patterns *)
  | P_fields (fields, _) ->
      let declared =
        Option.value ~default:[]
          (Option.bind ty (fun t -> Env.record_fields st.env t))
      in
      List.for_all
        (fun (f : Hir.field_pattern) ->
          irrefutable st ?ty:(List.assoc_opt f.field.desc declared) f.pattern)
        fields
  | P_variant (item, ps) -> variant_irrefutable st ty item ps
  | P_bare (n, ps, fallback) -> (
      match Hashtbl.find_opt st.bare p.loc with
      | Some (Named_variant item) -> variant_irrefutable st None item ps
      | Some Named_const -> false
      | Some Named_error -> true
      | None -> (
          match
            (Option.bind ty (fun t -> matched_variant st t n.desc), fallback)
          with
          | Some item, _ | None, Scope_variant item ->
              variant_irrefutable st ty item ps
          | None, Scope_const _ -> false
          | None, (Scope_error | Scope_failure _) -> true))
  | P_list ([], (Rest | Rest_bind _)) -> true
  (* generics.array-patterns: a list pattern that fits an array's size, given its
     type or as checking found it, can't fail when its elements can't. *)
  | P_list (ps, _) when array_fit st ty p ->
      let elem = Option.map fst (matched_array ty) in
      List.for_all (irrefutable st ?ty:elem) ps
  | P_or alternatives -> List.exists (irrefutable st ?ty) alternatives
  | P_int _ | P_str _ | P_bool _ | P_const _ | P_assoc_const _ | P_list _ ->
      false

and variant_irrefutable st ty item ps =
  match Env.variant st.env item with
  | Some (owner, _, payload) -> (
      match Env.type_info st.env owner with
      | Some { def = Variants [ _ ]; params; _ } ->
          let types = parts ty owner params payload ps in
          List.for_all2 (fun q ty -> irrefutable st ?ty q) ps types
      | _ -> false)
  | None -> true

(* The types of the fields of the record type [hty] that a pattern of type
   [ty] names, when [ty] is given. *)
and record_parts st ty (hty : Hir.ty) =
  match (ty, hty.desc) with
  | Some t, Ty_con (item, _) -> (
      match Env.type_info st.env item with
      | Some { params; def = Record fields; _ } ->
          let sub =
            T.subst (List.combine params (arguments t item params)) []
          in
          List.map (fun (f, ft) -> (f, sub ft)) fields
      | _ -> [])
  | _ -> []

(* Once the pattern is checked. *)
let require_irrefutable st (p : Hir.pattern) =
  if not (irrefutable st p) then
    error st Code.e0321 p.loc
      "this pattern can fail to match, which isn't allowed here"
