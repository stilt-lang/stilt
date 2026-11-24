(* Anonymous record literals, and updates of records (records.anonymous-literals and records.update). *)

module T = Types
module A = Tast
open Check_state
open Check_expect
open Check_types

(* records.anonymous-literals: [{ f: e, g }], whose fields are evaluated in the order they are
   written, each named once (E0316). Its type is the anonymous record type of
   its fields, never a declared record's, and an expected anonymous record
   type gives each field it names its type. *)
let anonymous_literal ctx expected loc (fields : Hir.field_init list) =
  let st = ctx.st in
  let expected_fields =
    match Option.map T.resolve expected with Some (Record fs) -> fs | _ -> []
  in
  let values =
    List.fold_left
      (fun values (f : Hir.field_init) ->
        if List.mem_assoc f.field.desc values then (
          error st Code.e0316 f.field.loc "the field `%s` is given twice"
            f.field.desc;
          ignore (abandon ctx f.value);
          values)
        else
          let want = List.assoc_opt f.field.desc expected_fields in
          let v = infer_checked ctx want f.value in
          values @ [ (f.field.desc, (v, Option.value want ~default:v.ty)) ])
      [] fields
  in
  node
    (Record (T.anonymous, [], List.map (fun (n, (v, _)) -> (n, v)) values))
    (T.record (List.map (fun (n, (_, t)) -> (n, t)) values))
    loc

(* records.update-fields: the fields an update writes, each one of the type's [declared]
   fields (E0313), at most once (E0316), with its type (E0311). *)
let written ctx ty declared (fields : Hir.field_init list) =
  let st = ctx.st in
  List.fold_left
    (fun values (f : Hir.field_init) ->
      let name = f.field.desc in
      match List.assoc_opt name declared with
      | None ->
          error st Code.e0313 f.field.loc
            "`%s` has no field `%s`, and an update never adds one" (show ty)
            name;
          ignore (abandon ctx f.value);
          values
      | Some _ when List.mem_assoc name values ->
          error st Code.e0316 f.field.loc "the field `%s` is given twice" name;
          ignore (abandon ctx f.value);
          values
      | Some t -> values @ [ (name, check ctx t f.value) ])
    [] fields

(* records.update: a record of [base]'s type [ty], with the fields written in place
   of its own. The base is evaluated first, then the fields. *)
let update ctx loc ty (base : A.expr) fields =
  let st = ctx.st in
  match Env.record_fields st.env ty with
  | Some declared -> node (Update (base, written ctx ty declared fields)) ty loc
  | None ->
      if T.resolve ty <> Error then
        error st Code.e0311 base.loc
          "`%s` isn't a record, so an update can't copy its fields" (show ty);
      List.iter
        (fun (f : Hir.field_init) -> ignore (abandon ctx f.value))
        fields;
      error_node loc

(* [Name { ..base, f: e }], whose base has the declared record's type. *)
let named_update ctx loc (hty : Hir.ty) base fields =
  let ty = named_type ctx.st hty in
  let b = check ctx ty base in
  update ctx loc ty b fields

(* [{ ..base, f: e }], whose base is an anonymous record or a type parameter
   with a record bound; a declared record's update names it. *)
let anonymous_update ctx loc (base : Hir.expr) fields =
  let st = ctx.st in
  let b = infer ctx None base in
  match known st base.loc b.ty with
  | Some (Con (item, _) as t) when Option.is_some (Env.record_fields st.env t)
    ->
      error st Code.e0311 base.loc
        "`%s` is a declared record, so its update names it, as `%s { ..base, … \
         }`"
        (show t) item.name;
      List.iter
        (fun (f : Hir.field_init) -> ignore (abandon ctx f.value))
        fields;
      error_node loc
  | Some t -> update ctx loc t b fields
  | None ->
      List.iter
        (fun (f : Hir.field_init) -> ignore (abandon ctx f.value))
        fields;
      error_node loc
