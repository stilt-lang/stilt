(* The uses of procedural macros (macros.procedural-uses). *)

open Hir
open Resolve_context

type found = Proc of item * Procs.state | Missing | Not_proc

(* macros.meta-use: a procedural macro is named only through [meta use], and only
   its procedural macros are named so. *)
let find ctx (path : Ast.path) =
  match path with
  | [ (alias : name); (n : name) ] -> (
      match Smap.find_opt alias.desc ctx.scope.metas with
      | None -> Not_proc
      | Some ns -> (
          let entry =
            Option.bind (Smap.find_opt ns ctx.env.scopes) (fun scope ->
                Smap.find_opt n.desc scope.values)
          in
          match entry with
          | Some (Item ({ kind = Proc_item; _ } as e)) ->
              if not e.pub then (
                errorf ctx Code.e0213 n.loc "`%s.%s` is private to module `%s`"
                  ns n.desc ns;
                Missing)
              else
                let find package path =
                  match ctx.env.view package path with
                  | Found ns -> Some ns
                  | _ -> None
                in
                let state = ctx.env.st.host.state ~find ns n.desc in
                Proc ({ home = ns; name = n.desc }, state)
          | _ when Smap.mem alias.desc ctx.scope.values -> Not_proc
          | _ ->
              unknown_name ctx
                ~name:(alias.desc ^ "." ^ n.desc)
                n.loc "module `%s` has no procedural macro `%s`" ns n.desc;
              Missing))
  | _ -> Not_proc

(* Whether [path] names a procedural macro through [meta use], as [find]
   reads it, reporting nothing. *)
let names_proc ctx (path : Ast.path) =
  match path with
  | [ (alias : name); (n : name) ] -> (
      match Smap.find_opt alias.desc ctx.scope.metas with
      | None -> false
      | Some ns -> (
          match
            Option.bind (Smap.find_opt ns ctx.env.scopes) (fun scope ->
                Smap.find_opt n.desc scope.values)
          with
          | Some (Item { kind = Proc_item; _ }) -> true
          | _ -> false))
  | _ -> false

(* macros.named-files: a file that a use names, read by the compiler, or E0229 at the
   literal. *)
let read ctx (l : Procs.literal) =
  match ctx.env.st.host.read ~file:ctx.scope.file l.text with
  | Ok contents -> Some (Procs.File_arg (l, contents))
  | Error why ->
      errorf ctx Code.e0229 (Macro_tokens.loc l.token) "%s" why;
      None

let arg ctx : Macro_parts.given -> Procs.arg option = function
  | Code (c, tokens) -> Some (Code_arg (c, tokens))
  | Literal (l, false) -> Some (Text_arg l)
  | Literal (l, true) -> read ctx l
  | Tokens (trees, close) -> Some (Tokens_arg (trees, close))

(* macros.running, macros.raised-errors and macros.step-limits: the run of the macro on the use's parts, whose quotes
   are numbered so that the names they write resolve where they are
   written. *)
let run ctx loc (item : item) (signature : Procs.signature) groups =
  let st = ctx.env.st in
  match Macro_parts.args ~file:ctx.scope.file signature.inputs groups with
  | Error (at, why) ->
      errorf ctx Code.e0227 at "%s, for `%s!`" why item.name;
      None
  | Ok given -> (
      let args = List.map (arg ctx) given in
      if List.exists Option.is_none args then None
      else
        let mark home =
          let id = st.next_id in
          st.next_id <- id + 1;
          Hashtbl.replace st.expansions id home;
          id
        in
        let use : Procs.use =
          {
            home = item.home;
            name = item.name;
            file = ctx.scope.file;
            at = loc;
            args = List.filter_map Fun.id args;
            mark;
          }
        in
        match st.host.run use with
        | Expanded tokens -> Some tokens
        | Raised (at, message) ->
            errorf ctx Code.e0225 at "%s" message;
            None
        | Stopped reason ->
            errorf ctx Code.e0226 loc "`%s!` didn't finish: %s" item.name reason;
            None)
