(* Fields: places, reads of fields, through an [Option] too (types.fields-through-option), and
   record literals. *)

module T = Types
module A = Tast
open Check_state
open Check_expect
open Check_types

(* expressions.places: a variable, or a field or element of a place. *)
let rec is_place (e : Hir.expr) =
  match e.desc with
  | Local _ -> true
  | Field (base, _) | Index (base, _) -> is_place base
  | _ -> false

(* Whether [e] may be a place once checked: a place, or a call that may be
   a projection's (projections.call-is-place), which only its callee decides. *)
let rec may_be_place (e : Hir.expr) =
  match e.desc with
  | Local _ | Call _ -> true
  | Field (base, _) | Index (base, _) -> may_be_place base
  | _ -> false

(* projections.call-is-place: a projection's call is a place, and so is a field, an
   element or an index of one. *)
let rec rooted_in_projection (e : A.expr) =
  match e.desc with
  | Project _ -> true
  (* An expression with an error may be anything (errors.error-type). *)
  | Error -> true
  | Field (base, _) | Tuple_field (base, _) | Index (base, _) ->
      rooted_in_projection base
  | _ -> false

(* expressions.places and projections.call-is-place: whether the checked form [checked] of
   [e] is a place. *)
let checked_place (e : Hir.expr) (checked : A.expr) =
  is_place e || rooted_in_projection checked

(* types.option-field-not-place: whether the checked form of a place reads a field through
   an [Option], which makes it a copy rather than a place. Such a read is
   checked as a [match]. *)
let rec through_option (e : A.expr) =
  match e.desc with
  | Match _ -> true
  | Field (base, _) | Tuple_field (base, _) | Index (base, _) ->
      through_option base
  | _ -> false

(* records.record-bounds and records.bound-fields: a declared record's fields, an anonymous
   record's, and those of a type parameter's record bound. *)
let record_fields st ty = Env.record_fields st.env ty

(* A field of [b], whose type [ty] is known and isn't an [Option]: an
   element of a tuple, or a field of a record. *)
let read_direct st loc (b : A.expr) (ty : T.ty) (field : Hir.name) =
  let missing () =
    let hint =
      match ty with
      | Con (item, _) when item = T.prelude_item "Result" ->
          "; convert a `Result` with `.ok()` first"
      | _ -> ""
    in
    (match ty with
    (* shared.std-sync: a [Shared<T>] has no field; its value is reached in a
       [when]. *)
    | Con ({ home = "std.sync"; name = "Shared" }, _) ->
        error st Code.e0313 field.loc
          "`%s` has no field `%s`: its value is reached only inside a `when` \
           that names it"
          (show ty) field.desc
    | _ ->
        error st Code.e0313 field.loc "`%s` has no field `%s`%s" (show ty)
          field.desc hint);
    error_node loc
  in
  match int_of_string_opt field.desc with
  (* variadics.pack-tuples *)
  | Some _ when Packs.has_spread ty ->
      error st Code.e0342 loc
        "`%s` has as many elements as its pack, which this body doesn't know, \
         so its elements aren't read by position; map over it with a spread, \
         as `(..e)`"
        (show ty);
      error_node loc
  | Some i -> (
      match ty with
      | Tuple ts when i < List.length ts ->
          node (Tuple_field (b, i)) (List.nth ts i) loc
      | _ -> missing ())
  | None -> (
      match Option.bind (record_fields st ty) (List.assoc_opt field.desc) with
      | Some t -> node (Field (b, field.desc)) t loc
      | None -> missing ())

(* The field [field] of [b], whose type [ty] is known. types.fields-through-option: on an
   [Option], the read goes through it, as
   [match b { Some(x) => x.field, None => None }], where the value of
   [x.field] is wrapped in [Some] unless it is an [Option] already. *)
let rec read_field st loc (b : A.expr) (ty : T.ty) (field : Hir.name) =
  match ty with
  | Con (item, [ t ]) when item = T.prelude_item "Option" -> (
      match known st b.loc t with
      | None -> error_node loc
      | Some inner_ty -> read_through st loc b ty t inner_ty field)
  | _ -> read_direct st loc b ty field

(* A read through [b], an [Option] of type [ty] whose values have type [t],
   which is known to be [inner_ty]. *)
and read_through st loc (b : A.expr) ty t inner_ty (field : Hir.name) =
  let x = Env.synthetic "x" in
  let inner = read_field st loc (node (Local x) t b.loc) inner_ty field in
  let arm variant payload body : A.arm =
    {
      pattern =
        {
          pat = P_variant (T.prelude_item variant, payload);
          pty = ty;
          ploc = b.loc;
        };
      guard = None;
      because = false;
      body;
    }
  in
  let through value u =
    let none =
      node (Construct (T.prelude_item "None", [ u ], [])) (T.option u) loc
    in
    node
      (Match
         ( b,
           [
             arm "Some" [ { pat = P_bind x; pty = t; ploc = b.loc } ] value;
             arm "None" [] none;
           ] ))
      (T.option u) loc
  in
  (* types.option-field-known: whether the read adds a level of [Option]
     depends on the field's type, which must be known here. *)
  match known st loc inner.ty with
  | None -> error_node loc
  | Some Error -> inner
  | Some (Con (item, [ u ])) when item = T.prelude_item "Option" ->
      through inner u
  | Some u ->
      through
        (node
           (Construct (T.prelude_item "Some", [ u ], [ inner ]))
           (T.option u) loc)
        u

let field_access ctx loc base (field : Hir.name) =
  let b = infer ctx None base in
  match known ctx.st base.loc b.ty with
  | None -> error_node loc
  | Some ty -> read_field ctx.st loc b ty field

let struct_literal ctx loc (hty : Hir.ty) (fields : Hir.field_init list) =
  let st = ctx.st in
  let ty = named_type st hty in
  match (T.resolve ty, record_fields st ty) with
  | Error, _ ->
      List.iter
        (fun (f : Hir.field_init) -> ignore (abandon ctx f.value))
        fields;
      error_node loc
  | Con (item, args), Some declared ->
      let seen = ref [] in
      let values =
        List.map
          (fun (f : Hir.field_init) ->
            match List.assoc_opt f.field.desc declared with
            | Some t ->
                if List.mem f.field.desc !seen then
                  error st Code.e0316 f.field.loc
                    "the field `%s` is given twice" f.field.desc;
                seen := f.field.desc :: !seen;
                (f.field.desc, check ctx t f.value)
            | None ->
                error st Code.e0313 f.field.loc "`%s` has no field `%s`"
                  item.name f.field.desc;
                (f.field.desc, abandon ctx f.value))
          fields
      in
      (match
         List.filter (fun (name, _) -> not (List.mem name !seen)) declared
       with
      | [] -> ()
      | missing ->
          error st Code.e0316 hty.loc "this literal lacks the field%s %s"
            (if List.length missing = 1 then "" else "s")
            (String.concat ", "
               (List.map (fun (n, _) -> "`" ^ n ^ "`") missing)));
      node (Record (item, args, values)) ty loc
  | t, _ ->
      error st Code.e0311 hty.loc "`%s` is not a record type" (show t);
      List.iter
        (fun (f : Hir.field_init) -> ignore (abandon ctx f.value))
        fields;
      error_node loc
