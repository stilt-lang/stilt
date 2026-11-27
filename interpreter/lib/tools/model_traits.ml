open Model_json
open Model_types
open Model_ops
open Model_forms

(* The calculus has [Set] as a type of its own (std.sets), shown and compared by its own
   operations, so the prelude's impls for it, which read its record's field, don't run. *)
let written cx trait name t : target option =
  match norm t with
  | Con (owner, _)
    when declared_record owner
         && Model_fns.code cx (Impl (trait, owner, name)) <> None ->
      Some (Impl (trait, owner, name))
  | _ -> None

let call_values cx target types values result =
  let inst = Model_fns.instance cx target [] types in
  let f = tag "fnRef" [ Str inst.fkey; Arr []; Arr [] ] in
  call_e cx f (List.map (fun v -> tag "value" [ v ]) values) result

(* Whether a type holds a string, which a structural [Show] writes quoted when it is
   nested and bare when it isn't (std.show-output). *)
let rec holds_str cx t =
  match norm t with
  | Types.Con ({ home = "std.prelude"; name = "str" }, []) -> true
  | Con ({ home = "std.prelude"; name }, [])
    when List.mem name Types.integer_types
         || List.mem name [ "f32"; "f64"; "bool"; "Never" ] ->
      false
  | Tuple ts -> List.exists (holds_str cx) ts
  | Con (i, args) when not (List.mem i [ list_item; option_item ]) -> (
      match Env.type_info cx.env i with
      | Some { Env.def = Env.Record fields; _ } ->
          List.exists
            (fun (_, f) ->
              holds_str cx
                (instantiated cx
                   { key = ""; item = i; args; generic = false }
                   f))
            fields
      | Some { Env.def = Env.Variants ctors; _ } ->
          List.exists
            (fun (_, ts) ->
              List.exists
                (fun f ->
                  holds_str cx
                    (instantiated cx
                       { key = ""; item = i; args; generic = false }
                       f))
                ts)
            ctors
      | _ -> true)
  | Con (_, args) -> List.exists (holds_str cx) args
  | _ -> true
