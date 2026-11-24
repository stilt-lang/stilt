(* The uses of macros, expanded as names are resolved (macros.expansion). *)

open Hir
open Resolve_context
open Resolve_paths

(* macros.nested-expansions: how deep expansions nest. *)
let depth_limit = 128

exception Too_deep of string list

(* macros.expansion-size: how many tokens the expansions of a use the user
   wrote hold in all, and the tokens of those of the use being resolved. *)
let size_limit = 100_000

exception Too_large of string * string

let spent = ref 0

(* macros.expansion-size: counts an expansion of the macro [name], which ends
   the use the user wrote once its expansions hold too many tokens. *)
let spend st name tokens =
  spent := !spent + List.length tokens;
  if !spent > size_limit then
    let outer =
      match List.rev st.chain with outer :: _ -> outer | [] -> name
    in
    raise (Too_large (outer, name))

(* macros.uses: a macro's name is resolved as a function's is. *)
let find ctx (path : Ast.path) =
  match walk ctx ~want:Values ~noun:"a macro" ~locals:false path with
  | Item_ref (item, { kind = Macro_item; _ }), _, [] ->
      Option.map (fun m -> (item, m)) (Hashtbl.find_opt ctx.env.st.macros item)
  | Broken_ref, _, _ -> None
  | m, last, [] ->
      wrong_kind ctx last m "a macro";
      None
  | m, (last : name), _ :: _ ->
      errorf ctx Code.e0212 last.loc "`%s` is %s, not a module" last.desc
        (describe_meaning m);
      None

(* A path as the user wrote it, without the marks of an expansion. *)
let written (path : Ast.path) =
  String.concat "." (List.map (fun (n : name) -> Macro_marks.base n.desc) path)

let form_name : Macro_expand.form -> string = function
  | Expr -> "an expression"
  | Pattern -> "a pattern"
  | Type -> "a type"

let fits (m : macro) : Macro_expand.form -> bool = function
  | Expr -> m.expr
  | Pattern -> m.pattern
  | Type -> false

(* macros.uses *)
let placed ctx (path : Ast.path) (m : macro) form =
  let fits = fits m form in
  (if not fits then
     let makes =
       if m.expr then "expressions"
       else if m.pattern then "patterns"
       else "neither expressions nor patterns"
     in
     errorf ctx Code.e0223 (List.hd path).loc
       "`%s!` stands where %s does, but its templates are %s" (written path)
       (form_name form) makes);
  fits

(* macros.matching: the first arm that matches the use, or E0222 at the furthest
   token that any arm reached. *)
let matched ctx (path : Ast.path) (m : macro) groups =
  let tokens = Array.of_list (Macro_tokens.flatten groups) in
  match Macro_match.first m.decl.arms tokens with
  | Ok found -> Some found
  | Error ((t : Lexer.token), expected) ->
      errorf ctx Code.e0222
        { line = t.line; col = t.col }
        "no arm of `%s!` matches this use: at %s, an arm expects %s"
        (written path)
        (Macro_tokens.describe t.token)
        expected;
      None

(* macros.nested-expansions: a use inside 128 nested expansions, of pattern macros and
   procedural macros alike (macros.nested-expansions), is too deep. *)
let deepen st =
  if List.length st.chain >= depth_limit then raise (Too_deep st.chain)

(* The expansion [tokens] of the macro [name], parsed and resolved in its
   place, inside the chain of expansions. *)
let in_place ctx name tokens parse resolve =
  let st = ctx.env.st in
  spend st name tokens;
  let ctx = { ctx with expanding = true; quoting = None } in
  match parse ctx tokens with
  | Stdlib.Error d ->
      Option.iter (fun d -> st.diagnostics <- d :: st.diagnostics) d;
      None
  | Ok tree ->
      st.chain <- name :: st.chain;
      Fun.protect
        ~finally:(fun () -> st.chain <- List.tl st.chain)
        (fun () -> Some (resolve ctx tree))

(* macros.hygiene and macros.nested-expansions: the expansion, numbered so that the names its template
   writes resolve where the macro is declared. *)
let expanded ctx loc (item : item) (m : macro) (arm : Ast.macro_arm) env parse
    resolve =
  let st = ctx.env.st in
  deepen st;
  let id = st.next_id in
  st.next_id <- id + 1;
  Hashtbl.replace st.expansions id m.home;
  let tokens = Macro_expand.substitute ~id ~at:loc arm.template env in
  in_place ctx item.name tokens parse resolve

let pattern_macro ctx loc path groups form parse resolve =
  match find ctx path with
  | Some (item, m) when m.usable && not ctx.env.st.declaring -> (
      if not (placed ctx path m form) then None
      else
        match matched ctx path m groups with
        | Some (arm, env) -> expanded ctx loc item m arm env parse resolve
        | None -> None)
  | Some _ | None -> None

let code_form : Hir.code -> Macro_expand.form = function
  | Code_expr | Code_field -> Expr
  | Code_pattern -> Pattern
  | Code_type -> Type

(* macros.procedural-uses and macros.running: a procedural macro's use, which stands where
   its result's form may (E0223), and expands unless its module has an error
   or the use is in a quote being resolved where it is written. *)
let proc_macro ctx loc (path : Ast.path) (item : item) state groups form parse
    resolve =
  match (state : Procs.state) with
  | Unusable -> None
  | Usable _ when ctx.env.st.declaring -> None
  | Usable signature when code_form signature.result <> form ->
      errorf ctx Code.e0223 (List.hd path).loc
        "`%s!` stands where %s does, but it gives %s" (written path)
        (form_name form)
        (form_name (code_form signature.result));
      None
  | Usable signature -> (
      deepen ctx.env.st;
      match Resolve_procs.run ctx loc item signature groups with
      | Some tokens -> in_place ctx item.name tokens parse resolve
      | None -> None)

let expand ctx loc path groups form parse resolve =
  let st = ctx.env.st in
  let outermost = st.chain = [] in
  if outermost then spent := 0;
  try
    match Resolve_procs.find ctx path with
    | Proc (item, state) ->
        proc_macro ctx loc path item state groups form parse resolve
    | Missing -> None
    | Not_proc -> pattern_macro ctx loc path groups form parse resolve
  with
  | Too_deep chain when outermost ->
      errorf ctx Code.e0224 loc
        "this use expands inside %d nested expansions, which is too deep: %s"
        depth_limit
        (String.concat " in "
           (List.map
              (fun name -> "`" ^ name ^ "!`")
              (List.filteri (fun i _ -> i < 3) chain))
        ^ " …");
      None
  | Too_large (outer, name) when outermost ->
      if outer = name then
        errorf ctx Code.e0231 loc
          "the expansion of `%s!` holds more than 100,000 tokens" name
      else
        errorf ctx Code.e0231 loc
          "the expansions of `%s!` hold more than 100,000 tokens once `%s!` \
           expands in them"
          outer name;
      None

(* macros.splices: a splice in a quote, whose expression is the macro's code,
   recorded where it stands; [none] stands for it in the quote's tree. *)
let splice ctx place (s : Ast.expr) none =
  match ctx.quoting with
  | Some q ->
      q.splice place s;
      none
  | None -> invalid_arg "Resolve_macros.splice"
