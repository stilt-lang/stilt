(* The rules about declarations outside impls: records that contain
   themselves (declarations.recursive-types), the signature of [main] (program.main), and
   the bounds of [where] clauses on member types that a bound's argument fixes
   (traits.where). *)

module T = Types
open Env_tables
open Env_signatures
open Env_implements

(* What a value of a record type can hold through record fields and tuple
   elements alone (declarations.recursive-types). *)
type held = Holds_record of Hir.item | Holds_param of int

(* The records of [program], each with its module and the position of its
   name. Of two declarations with the same name, only the first is the type
   that names refer to. *)
let records_of (program : Hir.program) =
  List.concat_map
    (fun (m : Hir.module_) ->
      let seen = ref [] in
      List.filter_map
        (fun (decl : Hir.decl Hir.node) ->
          match decl.desc.kind with
          | Type t when List.mem t.name.desc !seen -> None
          | Type t -> (
              seen := t.name.desc :: !seen;
              match t.def with
              | Record _ ->
                  let item = { Hir.home = m.name; name = t.name.desc } in
                  Some (item, m, t.name.loc)
              | Variants _ | Native -> None)
          | Fn _ | Const _ | Trait _ | Test _ | Effect _ -> None)
        m.decls)
    program

let record_info env item =
  match type_info env item with
  | Some ({ def = Record fields; _ } as info) -> Some (info.params, fields)
  | _ -> None

(* What a value of type [t] holds, where [holds] tells what each record
   holds. *)
let rec held env holds t =
  match T.resolve t with
  | T.Tuple ts -> List.concat_map (held env holds) ts
  | Param p -> [ Holds_param p.id ]
  | Con (item, args) -> (
      match (record_info env item, Imap.find_opt item holds) with
      | Some (params, _), Some inside when List.length params = List.length args
        ->
          let bound =
            List.combine (List.map (fun (v : Hir.var) -> v.id) params) args
          in
          Holds_record item
          :: List.concat_map
               (function
                 | Holds_record r -> [ Holds_record r ]
                 | Holds_param id ->
                     Option.fold ~none:[] ~some:(held env holds)
                       (List.assoc_opt id bound))
               inside
      | _ -> [])
  | Record fields -> List.concat_map (fun (_, t) -> held env holds t) fields
  | Fn _ | Forall _ | App _ | Spread _ | Handler _ | Var _ | Value _ | Error ->
      []

(* What each of the [records] holds, as a least fixed point, with the type
   parameters a record holds standing for the types they are instantiated
   with. *)
let holds_of env records =
  let step holds =
    Imap.mapi
      (fun item _ ->
        match record_info env item with
        | Some (_, fields) ->
            List.sort_uniq compare
              (List.concat_map (fun (_, t) -> held env holds t) fields)
        | None -> [])
      holds
  in
  let rec fix holds =
    let next = step holds in
    if Imap.equal ( = ) next holds then holds else fix next
  in
  fix
    (List.fold_left
       (fun acc (item, _, _) -> Imap.add item [] acc)
       Imap.empty records)

(* The [records] in groups that hold one another. *)
let rec groups holds_record = function
  | [] -> []
  | ((item, _, _) as r) :: rest ->
      let group, others =
        List.partition
          (fun (other, _, _) ->
            holds_record item other && holds_record other item)
          rest
      in
      (r :: group) :: groups holds_record others

(* declarations.recursive-types: a record that contains itself through records and tuples
   alone can't be constructed. Each group of records that hold one another
   is one error, at the last of them (errors.primary-spans). *)
let check_record_cycles d env (program : Hir.program) =
  let records = records_of program in
  let holds = holds_of env records in
  let holds_record a b = List.mem (Holds_record b) (Imap.find a holds) in
  let cyclic =
    List.filter (fun (item, _, _) -> holds_record item item) records
  in
  List.iter
    (fun group ->
      let position (_, (m : Hir.module_), (loc : Ast.loc)) =
        (m.file, loc.line, loc.col)
      in
      let _, m, loc =
        List.fold_left
          (fun a b -> if compare (position b) (position a) > 0 then b else a)
          (List.hd group) group
      in
      report d m Code.e0309 loc
        "this record contains itself, so no value of it can be built")
    (groups holds_record cyclic)

(* program.missing-main *)
let check_main d env (program : Hir.program) =
  List.iter
    (fun (m : Hir.module_) ->
      if m.name = "main" && not m.std then
        List.iter
          (fun (decl : Hir.decl Hir.node) ->
            match decl.desc.kind with
            | Fn ({ name = { desc = "main"; loc }; _ } as f) ->
                (* handlers.no-effect-reaches-main: no user-defined effect reaches [main], whose
                   row may hold [async]. *)
                List.iter
                  (fun (e : Hir.effect_inst) ->
                    if e.eff <> T.async_effect then
                      report d m Code.e0512 e.at
                        "`main` handles `%s` with `with`, so its row can't \
                         hold it"
                        e.eff.name)
                  f.row.effects;
                let s = signature ~outer:[] f in
                let shows =
                  match s.row.raise with
                  | None -> true
                  | Some e -> implements env [] e (T.prelude_item "Show") <> No
                in
                if
                  f.generics <> [] || f.params <> []
                  || (not (equal s.ret T.unit))
                  || s.row.tail <> Closed || not shows
                then
                  report d m Code.e0310 loc
                    "`main` must take no parameters, return `()` and perform \
                     at most `io` and `raise<E>` with `E: Show`"
            | _ -> ())
          m.decls)
    program

(* traits.where: a [where] bound on a member type that a bound's argument
   fixes is met by the fixed type, under the declaration's [bounds]. One on a
   type parameter of an impl block is assumed instead. *)
let check_where d env m bounds wheres =
  List.iter
    (fun ((t : Hir.ty), (b : Hir.bound), loc) ->
      match (of_hir t, b.trait) with
      | T.Param _, _ | _, Trait_error -> ()
      | ty, Trait_ref trait ->
          let args = List.map of_hir b.args in
          let same =
            match trait_args env bounds ty trait with
            | Some actual when List.length actual = List.length args ->
                equal_list actual args
            | Some _ | None -> true
          in
          if implements env bounds ty trait = No || not same then
            report d m Code.e0318 loc
              "`%s` doesn't implement `%s`, which this `where` clause asks of \
               it"
              (Types_show.to_string ty) trait.name)
    wheres

(* The bounds that a function's body assumes: its own, its impl block's, and
   those of its [where] clause on the block's member types. *)
let fn_bounds ~outer (f : Hir.fn_decl) =
  let s = signature ~outer f in
  s.type_params
  @ List.filter_map
      (fun (t, b) -> match t with T.Param v -> Some (v, [ b ]) | _ -> None)
      s.assumed

let check_wheres d env (program : Hir.program) =
  let fn m outer (decl : Hir.decl Hir.node) =
    match decl.desc.kind with
    | Fn f -> check_where d env m (fn_bounds ~outer f) f.where_bounds
    | Const _ | Type _ | Trait _ | Test _ | Effect _ -> ()
  in
  List.iter
    (fun (m : Hir.module_) ->
      List.iter (fn m []) m.decls;
      List.iter
        (fun (i : Hir.impl_decl Hir.node) ->
          let outer = bounds_of i.desc.generics in
          check_where d env m outer i.desc.where_bounds;
          List.iter (fn m outer) i.desc.members)
        m.impls)
    program
