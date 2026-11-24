(* The message of E0608 (packages.ungranted-effects; facts.ungranted-capabilities; c.granting-unsafe). *)

type fact =
  | Has of Ast.capability
  | Bare
  | Unsafe_code  (** An [unsafe] block (c.granting-unsafe). *)

(* facts.ungranted-capabilities *)
let narrowest facts =
  let effects =
    if List.mem Bare facts then [ "io" ]
    else
      List.filter_map
        (function
          | Has c -> Some (Capability.name c) | Bare | Unsafe_code -> None)
        facts
  in
  let granted =
    effects @ if List.mem Unsafe_code facts then [ "unsafe" ] else []
  in
  Printf.sprintf "may = [%s]"
    (String.concat ", " (List.map (Printf.sprintf "%S") granted))

let ungranted dep ~facts fact path
    ((callee : Implicit_names.key), (at : Ast.loc)) =
  let what =
    match fact with
    | Has c ->
        Printf.sprintf
          "`%s` has the capability `%s`, which this manifest doesn't grant it"
          dep (Capability.name c)
    | Bare ->
        Printf.sprintf
          "`%s` performs `io` without a capability, which only `io` grants, \
           and this manifest doesn't grant it"
          dep
    | Unsafe_code ->
        Printf.sprintf
          "`%s` holds an `unsafe` block, which may run C code and which only \
           `unsafe` grants, and this manifest doesn't grant it"
          dep
  in
  let where =
    match fact with
    | Unsafe_code -> Printf.sprintf "`%s` has one at line %d" path at.line
    | Has _ | Bare ->
        Printf.sprintf "`%s` uses `%s` at line %d" path
          (Implicit_capabilities.qualified callee)
          at.line
  in
  Printf.sprintf "%s: %s. The narrowest grant is `%s`" what where
    (narrowest facts)
