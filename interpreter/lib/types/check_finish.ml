(* The end of a body: the rules whose answer needs every type of the body,
   decided once inference is done. *)

module T = Types
open Check_state
open Check_unify
open Check_patterns
open Check_operators

(* expressions.unused-values and expressions.if *)
let unit_sites st =
  List.iter
    (fun (ty, site, loc) ->
      let valued =
        match T.resolve ty with
        | Tuple [] | Error | Var _ -> false
        (* tasks.std-task, Required tests: a task that is never awaited, whose
           handle a statement drops, still runs. *)
        | Con ({ home = "std.task"; name = "Task" }, _) -> false
        | t -> t <> T.never
      in
      match site with
      | Statement when valued ->
          error st Code.e0322 loc
            "this value of type `%s` is unused; write `let _ = …` to discard it"
            (show ty)
      | If_without_else _ when valued ->
          error st Code.e0323 loc
            "an `if` without `else` can't have a value of type `%s`" (show ty)
      | If_without_else if_ty ->
          if not (unify if_ty T.unit) then
            error st Code.e0311 loc "expected `%s`, found `()`" (show if_ty)
      | Statement -> ())
    (List.rev st.units)

(* numbers.integer-literals, numbers.float-literals and numbers.negative-literals *)
let literal_ranges st =
  List.iter
    (fun l ->
      match T.numeric_name l.lty with
      | Some name ->
          let fits =
            if l.float then Literal.float_fits l.text name
            else if List.mem name T.float_types then
              Literal.int_exact_in l.text name
            else Literal.int_fits l.text ~negative:l.negative name
          in
          if not fits then
            error st Code.e0320 l.lloc "%s%s doesn't fit in `%s`"
              (if l.negative then "-" else "")
              l.text name
      | None -> ())
    (List.rev st.literals)

(* A type as a message shows it, with the type parameters it holds: two
   rigid types of one name are two types (polymorphism.rigid-types). *)
let shown ty =
  (show ty, List.map (fun (v : Hir.var) -> v.id) (T.type_params (T.zonk ty)))

(* variadics.packs: a pack's bound holds for each of its elements, and is
   reported at each element that lacks it. *)
let rec elements ((ty, trait, loc, bounds) as obligation) =
  match T.resolve ty with
  | Spread (pack, body) -> (
      match T.resolve pack with
      | Tuple es ->
          List.concat_map
            (fun e -> elements (T.element pack body e, trait, loc, bounds))
            es
      | _ -> [ obligation ])
  | _ -> [ obligation ]

(* traits.unsatisfied-bounds *)
(* traits.bound-reported-once: each type and trait once per body, at its first use in
   source order, and the traits missing at one use in one diagnostic. *)
let missing_impls st =
  let position (_, _, (loc : Ast.loc)) = (loc.line, loc.col) in
  let firsts =
    List.filter
      (fun (ty, trait, _, bounds) -> Env.implements st.env bounds ty trait = No)
      (List.concat_map elements (List.rev st.obligations))
    |> List.map (fun (ty, (trait : Hir.item), loc, _) ->
        (shown ty, trait.name, loc))
    |> List.stable_sort (fun a b -> compare (position a) (position b))
    |> List.fold_left
         (fun firsts ((ty, trait, _) as use) ->
           if List.exists (fun (t, tr, _) -> t = ty && tr = trait) firsts then
             firsts
           else firsts @ [ use ])
         []
  in
  let rec report = function
    | [] -> ()
    | ((ty, _, loc) as first) :: _ as uses ->
        let here, rest =
          List.partition
            (fun ((t, _, _) as use) -> t = ty && position use = position first)
            uses
        in
        let traits = List.map (fun (_, trait, _) -> "`" ^ trait ^ "`") here in
        error st Code.e0318 loc "`%s` doesn't implement %s" (fst ty)
          (String.concat " or " traits);
        report rest
  in
  report firsts

(* std.width-fill-and-alignment, std.precision, std.integer-kinds, std.scientific-notation, std.format-special-values and std.invalid-specs: which types a format spec applies to. *)
let format_specs st =
  (* std.invalid-specs *)
  List.iter
    (fun (ty, spec, loc) ->
      let { precision; kind; _ } : Format_spec.t =
        Option.get (Format_spec.parse spec)
      in
      let precision = Option.is_some precision in
      let integer = Option.is_some (integer_name ty) in
      let floating = Option.is_some (T.numeric_name ty) && not integer in
      let ok =
        match T.resolve ty with
        | Error | Var _ -> true
        | _ -> (
            match kind with
            | Some ('x' | 'X' | 'o' | 'b') -> integer && not precision
            | Some 'e' -> floating
            | _ -> (not precision) || floating)
      in
      if not ok then
        error st Code.e0325 loc "the format spec `%s` doesn't apply to `%s`"
          spec (show ty))
    (List.rev st.specs)

(* Types that inference didn't decide, when nothing else is wrong: each at
   the first expression, in source order, whose type holds it, and once per
   expression (types.undecided-types and types.undecided-type-location). Variables that inference made one take the
   earliest origin of any of them. *)
let unknown_types st =
  if st.errors = [] && not st.broken then (
    let first = Hashtbl.create 16 in
    let earlier (a : Ast.loc) (b : Ast.loc) =
      if compare (a.line, a.col) (b.line, b.col) <= 0 then a else b
    in
    List.iter
      (fun v ->
        match (T.origin v, T.unsolved v) with
        | Some own, Some info
          when (not info.tainted) && not (List.mem info.id st.unknown) ->
            Hashtbl.replace first info.id
              (match Hashtbl.find_opt first info.id with
              | Some origin -> earlier origin own
              | None -> own)
        | _ -> ())
      st.vars;
    Hashtbl.fold (fun _ origin origins -> origin :: origins) first []
    |> List.sort_uniq (fun (a : Ast.loc) b ->
        compare (a.line, a.col) (b.line, b.col))
    |> List.iter (fun origin ->
        error st Code.e0312 origin
          "the type of this expression can't be inferred; add an annotation"))

(* Decides the rules that wait for every type of the body. *)
let finish st =
  (* effects.catch: a [catch] whose operand raises nothing catches
     [Never]. *)
  List.iter
    (fun t -> if Option.is_some (T.unsolved t) then T.solve t T.never)
    st.catch_errors;
  (* numbers.literal-defaults *)
  List.iter
    (fun l ->
      match T.unsolved l.lty with
      | Some { kind = Int_literal; _ } -> T.solve l.lty T.i64
      | Some { kind = Float_literal; _ } -> T.solve l.lty T.f64
      | _ -> ())
    (List.rev st.literals);
  (* traits.bound-arguments: the arguments of the bounds whose types are known only
     now. *)
  improve st;
  unit_sites st;
  literal_ranges st;
  (* c.element-types and c.lending-buffer *)
  Check_foreign.fit st;
  (* patterns.floats *)
  List.iter
    (fun (ty, loc) ->
      if holds_float st.env ty then
        error st Code.e0328 loc "a float can't be matched by a pattern")
    (List.rev st.int_patterns);
  (* numbers.no-implicit-conversions, and expressions.no-string-plus: the operators whose operand
     type was open where they were checked. *)
  List.iter
    (fun (ty, rule, loc) ->
      if supports ty rule = Some false then unsupported st ty rule loc)
    (List.rev st.operators);
  (* numbers.shift-amounts: the shift amounts whose type was open. *)
  List.iter
    (fun (ty, loc) ->
      if supports ty Integer = Some false then not_an_amount st ty loc)
    (List.rev st.amounts);
  missing_impls st;
  format_specs st;
  (* macros.splices *)
  Check_quotes.fit st;
  unknown_types st
