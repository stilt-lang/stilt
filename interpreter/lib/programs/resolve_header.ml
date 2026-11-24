(* Step 2 of name resolution: a module's header, which names the module and
   limits it (program.module-header and program.header-limits). *)

open Resolve_context
open Resolve_scopes

let check_header st (u : unit_) =
  let file = u.source.file in
  match u.tree.header with
  | None -> []
  | Some { desc = { path; withouts }; _ } ->
      if u.valid && dotted_path path <> u.local then
        report st ~file Code.e0201 (List.hd path).loc
          "this file is module `%s`, but its header says `%s`" u.local
          (dotted_path path);
      Resolve_limits.of_header st ~file withouts
