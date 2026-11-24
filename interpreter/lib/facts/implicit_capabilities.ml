(* The capabilities of natives (facts.capability-natives), and the messages of E0204
   under a capability's limit (facts.without). *)

open Implicit_names

let native = function
  | Function item -> Capability.native ~home:item.home ~name:item.name
  (* tasks.implicit-effects-and-capabilities *)
  | Member ({ home = "std.task"; name = "Scope" }, "spawn") -> Some Ast.Spawn
  | Member _ | Impl_method _ | Default_method _ | Built_in _ -> None

let qualified = function
  | Function { home; name }
    when String.starts_with ~prefix:"std." home && home <> "std.prelude" ->
      let segments = String.split_on_char '.' home in
      List.nth segments (List.length segments - 1) ^ "." ^ name
  | key -> show_key key

let named ~through c k =
  let cap = Capability.name c in
  match through with
  | [] ->
      Printf.sprintf "this uses `%s`, a native with the capability `%s`"
        (qualified k) cap
  | _ ->
      Printf.sprintf "this uses `%s`, which has the capability `%s` through %s"
        (qualified k) cap
        (String.concat ", then "
           (List.map
              (fun (n, (at : Ast.loc)) ->
                Printf.sprintf "`%s` at line %d" (qualified n) at.line)
              through))
