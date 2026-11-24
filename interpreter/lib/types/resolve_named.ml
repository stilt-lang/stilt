(* Named types: a path with its arguments, applied to what the path names
   (declarations.type-arguments; traits.member-types, traits.constructor-traits and traits.constructor-parameters; variadics.packs, variadics.type-spreads and variadics.pack-inference; generics.value-arguments). *)

open Hir
open Resolve_context
open Resolve_paths

(* program.private-in-signatures: a private item can't appear in a signature that other
   modules see. *)
let check_public = Resolve_rows.check_public

let as_type m loc =
  match m with
  | Param_ref v -> Some { desc = Ty_param v; loc }
  | Self_ref t -> Some t
  | Item_ref (item, { kind = Type_item; _ }) ->
      Some { desc = Ty_con (item, []); loc }
  | Item_ref _ | Var_ref _ | Namespace_ref _ | Broken_ref -> None

let plural n = if n = 1 then "" else "s"

(* declarations.type-arguments *)
let arity_error ctx loc path arity given =
  errorf ctx Code.e0300 loc "`%s` takes %d type argument%s, not %d"
    (dotted_path path) arity (plural arity) given;
  Ty_error

(* traits.constructor-parameters and traits.constructor-traits: a constructor of [arity] arguments, given
   [given]. *)
let kind_error ctx loc what arity given =
  errorf ctx Code.e0337 loc
    "%s is a type constructor of %d argument%s, so it is written with %d, not \
     %d"
    what arity (plural arity) arity given;
  Ty_error

(* variadics.type-spreads: a pack is written only inside a spread, which collects the
   packs it names. *)
let pack_use ctx loc (v : var) =
  match ctx.spread with
  | Some named ->
      named := v :: !named;
      Ty_param v
  | None ->
      errorf ctx Code.e0343 loc
        "`%s` is a pack, which is written spread, as `..%s`" v.name v.name;
      Ty_error

(* variadics.packs and variadics.pack-inference: the arguments of a type whose last parameter is a
   pack, those after the others a tuple of the pack's elements. *)
let packed_args loc arity args =
  let firsts = List.filteri (fun i _ -> i < arity - 1) args in
  let rest = List.filteri (fun i _ -> i >= arity - 1) args in
  firsts @ [ { desc = Ty_tuple rest; loc } ]

(* What a path that names [m] stands for, applied to [args]. *)
let applied ctx loc path (last : name) m args =
  let given = List.length args in
  match m with
  | Param_ref v when List.mem v.id ctx.packs ->
      if given = 0 then pack_use ctx loc v else arity_error ctx loc path 0 given
  (* variadics.packs: after E0344, a misplaced pack is a plain type parameter,
     and a spread of it is just its body. *)
  | Param_ref v when List.mem v.id ctx.misplaced && given = 0 ->
      Option.iter (fun named -> named := v :: !named) ctx.spread;
      Ty_param v
  | Param_ref v -> (
      match List.assoc_opt v.id ctx.kinds with
      | Some k when k = given -> Ty_app (v, args)
      | Some k -> kind_error ctx loc ("`" ^ v.name ^ "`") k given
      | None when given = 0 -> Ty_param v
      | None -> arity_error ctx loc path 0 given)
  | Self_ref { desc = Ty_self; _ } when ctx.ctor > 0 ->
      if given = ctx.ctor then Ty_self_app args
      else kind_error ctx loc "`Self`" ctx.ctor given
  | Self_ref { desc = Ty_con (item, []); _ } when ctx.ctor > 0 ->
      if given = ctx.ctor then Ty_con (item, args)
      else kind_error ctx loc "`Self`" ctx.ctor given
  | Self_ref t when given = 0 -> t.desc
  | Self_ref _ -> arity_error ctx loc path 0 given
  | Item_ref (item, ({ kind = Type_item; pack = true; _ } as e))
    when given >= e.arity - 1 ->
      check_public ctx loc item e;
      Ty_con (item, packed_args loc e.arity args)
  | Item_ref (item, ({ kind = Type_item; _ } as e)) ->
      check_public ctx loc item e;
      if given = e.arity then Ty_con (item, args)
      else arity_error ctx loc path e.arity given
  | m ->
      wrong_kind ctx last m "a type";
      Ty_error

(* traits.member-types: the member type [C.member], where [C] is the type
   parameter [v]: the argument that the one bound of [v] whose trait has the
   parameter [member] gives it. *)
let member_type ctx loc (v : var) (member : name) =
  advanced ctx;
  let found =
    List.filter_map
      (fun ((trait : item), params) ->
        Option.map
          (fun (t : ty) -> (trait, t))
          (List.assoc_opt member.desc params))
      (Option.value ~default:[] (List.assoc_opt v.id ctx.members))
  in
  match found with
  | [] ->
      errorf ctx Code.e0334 loc "no bound of `%s` has a trait parameter `%s`"
        v.name member.desc;
      Ty_error
  | [ (_, t) ] -> t.desc
  | (a, _) :: (b, _) :: _ ->
      errorf ctx Code.e0335 loc
        "`%s.%s` could be the `%s` of `%s` or of `%s`; name it with a generic \
         of the function, as in `%s: %s<T>`"
        v.name member.desc member.desc a.name b.name v.name a.name;
      Ty_error

(* A path written as a type, whose arguments [resolve_args] resolves once its
   head is known: a type, or a member type (traits.member-types). *)
let named ctx ?misplaced loc (path : name list) resolve_args =
  let walked =
    walk ctx ~want:Types ~noun:"a type" ?misplaced ~locals:false path
  in
  let args = resolve_args walked in
  match walked with
  | Broken_ref, _, _ -> Ty_error
  | m, last, [] -> applied ctx loc path last m args
  | Param_ref v, _, [ member ] when args = [] -> member_type ctx loc v member
  | m, last, [ member ] when args = [] && Option.is_some (as_type m last.loc) ->
      advanced ctx;
      errorf ctx Code.e0334 loc
        "`%s` isn't a type parameter, so it has no member type `%s`" last.desc
        member.desc;
      Ty_error
  | m, (last : name), _ :: _ ->
      errorf ctx Code.e0212 last.loc "`%s` is %s, not a module" last.desc
        (describe_meaning m);
      Ty_error
