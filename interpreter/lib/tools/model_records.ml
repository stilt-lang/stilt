open Model_json
open Model_types
open Model_forms

(* [{ ..base, f: x }]: [base] evaluated first, then the fields written, in
   order, then the record of [base]'s type with those fields and [base]'s
   others (records.update). *)
let update ~expr cx (e : Tast.expr) (base : Tast.expr) written =
  let declared_fields =
    match norm e.ty with
    | Con (i, _) when declared_record i -> (
        match Env.type_info cx.env i with
        | Some { Env.def = Env.Record fields; _ } -> List.map fst fields
        | _ -> outside "an update of a record the model lacks")
    | Record fields -> List.map fst fields
    | _ -> outside "an update of a record the model lacks"
  in
  let b = temp "update" e.loc in
  let named =
    List.mapi
      (fun k (f, x) -> (f, Printf.sprintf "%s/%d" b k, (x : Tast.expr)))
      written
  in
  let field f =
    match List.find_opt (fun (g, _, _) -> g = f) named with
    | Some (_, n, _) -> Arr [ Str f; var_e n ]
    | None -> Arr [ Str f; tag "field" [ var_e b; Str f ] ]
  in
  let built =
    tag "record"
      ((Str (record_name cx e.ty) :: with_args (record_args cx e.ty))
      @ [ Arr (List.map field declared_fields) ])
  in
  let body =
    List.fold_right
      (fun (_, n, (x : Tast.expr)) acc ->
        tag "letIn" [ Str n; ty cx x.ty; expr x; acc ])
      named built
  in
  tag "letIn" [ Str b; ty cx base.ty; expr base; body ]
