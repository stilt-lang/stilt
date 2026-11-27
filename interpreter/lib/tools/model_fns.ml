open Model_types

let target_name = function
  | Function i -> item_name i
  | Member (owner, name) -> item_name owner ^ "." ^ name
  | Impl (trait, owner, name) | Default (trait, owner, name) ->
      item_name trait ^ " for " ^ item_name owner ^ "." ^ name

(* The trait method that a default is the body of. *)
let trait_method cx trait name =
  Option.bind (Env.trait_info cx.env trait) (fun (info : Env.trait_info) ->
      List.find_opt
        (fun (m : Env.trait_method) -> m.method_name = name && m.has_default)
        info.methods
      |> Option.map (fun m -> (info, m)))

let signature cx target =
  let found =
    match target with
    | Function i when List.mem_assoc i cx.projections ->
        let s, _, _ = List.assoc i cx.projections in
        Some s
    | Function i -> Env.function_sig cx.env i
    | Member (owner, name) ->
        List.find_opt
          (fun (m : Env.member) -> m.name = name)
          (Env.inherent_members cx.env owner)
        |> Option.map (fun (m : Env.member) -> m.signature)
    | Impl (trait, owner, name) -> (
        match Env.trait_impl cx.env ~trait owner with
        | Some impl ->
            List.find_opt (fun (m : Env.member) -> m.name = name) impl.members
            |> Option.map (fun (m : Env.member) -> m.signature)
        | None -> None)
    | Default (trait, _, name) ->
        Option.map
          (fun (_, (m : Env.trait_method)) -> m.method_sig)
          (trait_method cx trait name)
  in
  match found with
  | Some s -> s
  | None -> outside "the function %s" (target_name target)

let code cx target =
  let found =
    match target with
    | Function i when List.mem_assoc i cx.projections ->
        let _, d, _ = List.assoc i cx.projections in
        Some d
    | Function i -> List.assoc_opt i cx.program.functions
    | Member (owner, name) -> List.assoc_opt (owner, name) cx.program.members
    | Impl (trait, owner, name) ->
        List.assoc_opt (trait, owner, name) cx.program.impl_methods
    | Default (trait, _, name) ->
        List.assoc_opt (trait, name) cx.program.default_methods
  in
  match found with Some ({ body = Code b; _ } as d) -> Some (d, b) | _ -> None

(* The row variable of a parameter's row, a row parameter alone, takes what the
   argument's row holds beyond what the declared row names
   (effects.non-escaping-parameters). *)
let row_in acc (rw : Types.row) rw' =
  match (rw, Types.row_contents rw') with
  | { effects; tail = Row_params [ p ]; io; raise }, actual
    when not (List.mem_assoc p.var acc) ->
      let named (e, args) =
        List.exists
          (fun (e', args') ->
            e = e' && List.map norm args = List.map norm args')
          effects
      in
      let rest =
        {
          actual with
          io = actual.io && not io;
          raise = (if raise = None then actual.raise else None);
          effects = List.filter (fun e -> not (named e)) actual.effects;
        }
      in
      (p.var, rest) :: acc
  | _ -> acc

(* The rows a function's arguments give its row parameters: a parameter of a
   function type, or of a handler type, whose row is a row parameter alone takes
   the row of its argument's type (effects.non-escaping-parameters and
   handlers.handler-types). *)
let rec rows_in acc (declared : Types.ty) (actual : Types.ty) =
  let pairs acc ds xs =
    if List.length ds = List.length xs then List.fold_left2 rows_in acc ds xs
    else acc
  in
  match (declared, norm actual) with
  | Fn (ps, r, rw), Fn (ps', r', rw') ->
      pairs (row_in acc rw rw') (r :: List.map snd ps) (r' :: List.map snd ps')
  | Handler h, Handler h' -> row_in acc h.hrow h'.hrow
  | Con (_, ds), Con (_, xs) | Tuple ds, Tuple xs -> pairs acc ds xs
  | _ -> acc

(* How deeply a type nests. *)
let rec depth (t : Types.ty) =
  let deepest ts = List.fold_left (fun d t -> max d (depth t)) 0 ts in
  match norm t with
  | Con (_, ts) | Tuple ts -> 1 + deepest ts
  | Fn (ps, r, _) -> 1 + deepest (r :: List.map snd ps)
  | _ -> 1

(* A call at a type nested deeper than this is declined: a function may call
   itself at ever deeper types (polymorphism.recursion), whose instances never
   end. *)
let deepest_instance = 12

(* The types a type written in terms of type parameters gives them at [actual]. *)
let rec matched acc (written : Types.ty) (actual : Types.ty) =
  let pairs acc ws xs =
    if List.length ws = List.length xs then List.fold_left2 matched acc ws xs
    else acc
  in
  match (norm written, norm actual) with
  | Param v, t when not (List.mem_assoc v acc) -> (v, t) :: acc
  | Con (_, ws), Con (_, xs) | Tuple ws, Tuple xs -> pairs acc ws xs
  | _ -> acc

(* The type a call of a trait's function is at: the [Self] it is named on, or its
   receiver's type. *)
let self_type ?self args =
  match (self, args) with
  | Some t, _ -> Some t
  | None, t :: _ -> Some t
  | None, [] -> None

(* The arguments of a generic impl that a call of one of its functions takes from the type
   [self] it is called at, which the impl's type matches, and those that the member types
   of the impl's bounds imply (traits.implementing-trait and traits.member-types): its
   generics come first among the function's type parameters. *)
let impl_args cx target ?self targs args (s : Env.fn_sig) =
  match target with
  | Impl (trait, owner, _) -> (
      match (Env.trait_impl cx.env ~trait owner, self_type ?self args) with
      | Some ({ generics = _ :: _ as generics; _ } as impl), Some self
        when List.length generics + List.length targs
             = List.length s.type_params ->
          let found =
            match norm self with
            | Con (_, a) -> Env.impl_subst cx.env [] impl a
            | self -> matched [] impl.self_ty self
          in
          let arg (v, _) =
            match List.assoc_opt v found with
            | Some t -> t
            | None ->
                outside
                  "a generic impl whose receiver doesn't give its arguments"
          in
          List.map arg generics
      | Some { generics = _ :: _; _ }, None ->
          outside "a generic impl's method without a receiver"
      | _ -> [])
  | _ -> []

(* What a default's [Self] is: the type it is called at, the type whose impl leaves the
   function out, and what the trait's parameters are, the arguments that impl gives them
   (traits.impl-members and traits.trait-arguments). *)
let self_of cx target ?self args =
  match target with
  | Default (trait, _, name) -> (
      match (trait_method cx trait name, self_type ?self args) with
      | Some (info, _), Some self ->
          let targs =
            Option.value ~default:[] (Env.trait_args cx.env [] self trait)
          in
          if List.length targs <> List.length info.params then
            outside "the default of a trait with parameters";
          (info.self_param, self) :: List.combine info.params targs
      | _ -> outside "the default of a function without self")
  | _ -> []

let instance ?self cx target targs args =
  let s = signature cx target in
  let targs = impl_args cx target ?self targs args s @ targs in
  if List.length s.type_params <> List.length targs then
    outside "a generic call of %s" (target_name target);
  if List.exists (fun t -> depth t > deepest_instance) targs then
    outside "a function called at ever deeper types";
  let self = self_of cx target ?self args in
  let types_of =
    self @ List.map2 (fun (v, _) t -> (v, t)) s.type_params targs
  in
  let declared = List.map snd s.params in
  let rows_of =
    if List.length declared = List.length args then
      List.fold_left2 rows_in [] declared args
    else []
  in
  if not (List.for_all (fun v -> List.mem_assoc v rows_of) s.row_params) then
    outside "a row parameter of %s that no argument gives" (target_name target);
  let fkey =
    match (List.map snd self @ targs, rows_of) with
    | [], [] -> target_name target
    | targs, _ ->
        let types = List.map (type_arg cx) targs in
        let rows =
          List.map (fun (_, r) -> Model_json.to_string (row cx r)) rows_of
        in
        target_name target ^ "<" ^ String.concat ", " (types @ rows) ^ ">"
  in
  let inst = { fkey; target; types_of; rows_of } in
  if not (List.exists (fun i -> i.fkey = fkey) cx.fns) then
    cx.fns <- inst :: cx.fns;
  inst

let instantiated inst t = Types.subst inst.types_of inst.rows_of t
let instantiated_row inst r = Types.subst_row inst.types_of inst.rows_of r

(* The implicit row variables of a row, in order. *)
let implicits (r : Types.row) =
  match r.tail with
  | Row_params ps -> List.filter (fun (p : Types.row_param) -> p.implicit) ps
  | _ -> []

(* The checker gives a body implicit row variables of its own for its
   non-escaping parameters (effects.non-escaping-parameters): each is the one
   that its parameter's type holds where the body reads it, and stands for the
   signature's, so it takes that one's row. *)
let body_rows inst (d : Tast.fn_def) (s : Env.fn_sig) b =
  let found = ref inst.rows_of in
  let param = List.combine (List.map snd d.params) (List.map snd s.params) in
  let read (e : Tast.expr) =
    match e.desc with
    | Local v -> (
        match (List.assoc_opt v param, norm e.ty) with
        | Some (Fn (_, _, declared)), Fn (_, _, own) ->
            let pairs = implicits declared and owns = implicits own in
            if List.length pairs = List.length owns then
              List.iter2
                (fun (p : Types.row_param) (o : Types.row_param) ->
                  match List.assoc_opt p.var inst.rows_of with
                  | Some r when not (List.mem_assoc o.var !found) ->
                      found := (o.var, r) :: !found
                  | _ -> ())
                pairs owns
        | _ -> ())
    | _ -> ()
  in
  Walk.iter_block read b;
  !found

(* A spec with a width and no alignment aligns a splice right only when its type
   where it is written is a numeric type, and left when it is a type parameter
   that a number instantiates (std.width-fill-and-alignment): so before the
   instance's types replace the parameters, such a splice's spec says left. *)
let written_alignment (e : Tast.expr) spec =
  let numeric = int_kind e.ty <> None || float_kind e.ty <> None in
  match Format_spec.parse spec with
  | Some { align = None; width; _ } when width > 0 && not numeric -> "<" ^ spec
  | _ -> spec

let is_param t = match Types.resolve t with Types.Param _ -> true | _ -> false

(* traits.floats: [<] in generic code goes through [compare], whose order on floats is the
   total one, unlike [<] on floats: so before the instance's types replace the parameters,
   an ordering of a type parameter's values tests the [Ordering] of [Ord.compare]. *)
let generic_order (e : Tast.expr) =
  let prelude name = { Hir.home = "std.prelude"; name } in
  match e.desc with
  | Binary (((Lt | Le | Gt | Ge) as b), x, y) when is_param x.ty ->
      let ordering = Types.Con (prelude "Ordering", []) in
      let args =
        [ { Tast.mode = Let; value = x }; { mode = Let; value = y } ]
      in
      let compare = Tast.Trait_method (prelude "Ord", "compare", x.ty) in
      let called =
        {
          e with
          desc = Call (compare, [], args, Types.empty_row);
          ty = ordering;
        }
      in
      let test, ctor =
        match b with
        | Lt -> (Ast.Eq, "Less")
        | Gt -> (Eq, "Greater")
        | Le -> (Ne, "Greater")
        | _ -> (Ne, "Less")
      in
      let case =
        { e with desc = Construct (prelude ctor, [], []); ty = ordering }
      in
      { e with desc = Binary (test, called, case) }
  | _ -> e

(* generics.value-parameters-in-body: a value parameter read in a body is the value its
   instance gives it, a literal of the parameter's type. *)
let value_param inst (e : Tast.expr) =
  match e.desc with
  | Value_param v -> (
      match List.assoc_opt v inst.types_of with
      | Some (Types.Value (("true" | "false") as b)) ->
          { e with desc = Bool (b = "true") }
      | Some (Types.Value text) -> { e with desc = Int text }
      | _ -> e)
  | _ -> e

let body inst d s b =
  let rows = body_rows inst d s b in
  let at = { inst with rows_of = rows } in
  Check_zonk.map_block ~spec:written_alignment
    ~node:(fun e -> generic_order (value_param inst e))
    ~ty:(instantiated at) ~row:(instantiated_row at) b

(* A function declared at the top level as a value, at its type arguments: its
   instance. A value gives no row parameter a row, so a function with one stays
   outside. *)
let value cx i targs =
  let s = signature cx (Function i) in
  if s.row_params <> [] then outside "a function with row parameters as a value";
  let inst = instance cx (Function i) targs [] in
  Model_json.(tag "fnRef" [ Str inst.fkey; Arr []; Arr [] ])
