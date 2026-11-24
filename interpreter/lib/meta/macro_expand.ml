(* A macro's templates as tokens (macros.checked-templates, macros.expansion and macros.hygiene). Tokens are
   gathered latest first. *)

open Ast
open Macro_match

type form = Expr | Pattern | Type

let at = Macro_tokens.at
let token = Macro_tokens.token

(* macros.hygiene: an identifier the template writes is marked with its expansion,
   but for a member, after a [.], which no scope resolves. *)
let marked id loc a (out : Lexer.token list) =
  let after_dot =
    match out with { token = DOT; _ } :: _ -> true | _ -> false
  in
  let t : Token.t =
    match a with
    | A_lower s when not after_dot -> LIDENT (Macro_marks.mark id s)
    | A_upper s when not after_dot -> UIDENT (Macro_marks.mark id s)
    | a -> token a
  in
  Macro_tokens.at loc t :: out

let separator loc : string option -> Lexer.token list = function
  | Some "," -> [ at loc COMMA ]
  | Some _ -> [ at loc SEP ]
  | None -> []

(* The fragments of a repetition that repeat there, and the number of its
   rounds, which they share (macros.templates). *)
let rounds env ts =
  let repeated =
    List.filter_map
      (fun name ->
        match List.assoc_opt name env with
        | Some (Many bs) -> Some (name, bs)
        | _ -> None)
      (Macro_check.names ts)
  in
  let count = match repeated with (_, bs) :: _ -> List.length bs | [] -> 0 in
  (repeated, count)

let rec expand_items ~id ~loc env ts out =
  List.fold_left (fun out t -> expand_item ~id ~loc env t out) out ts

and expand_item ~id ~loc env (t : tree) out =
  match t.desc with
  | Token a -> marked id loc a out
  | Group (d, ts, _) ->
      let out =
        expand_items ~id ~loc env ts (at loc (Macro_tokens.opener d) :: out)
      in
      at loc (Macro_tokens.closer d) :: out
  | Fragment (n, _) -> (
      (* macros.expansion: an expression or a pattern stays one form. *)
      match List.assoc_opt n.desc env with
      | Some (One (("expr" | "pattern"), tokens)) ->
          at loc RPAREN :: List.rev_append tokens (at loc LPAREN :: out)
      | Some (One (_, tokens)) -> List.rev_append tokens out
      | Some (Many _) | None -> invalid_arg "Macro_expand.substitute")
  | Repeat (ts, sep, _) ->
      let repeated, count = rounds env ts in
      let round out k =
        let out = if k > 0 then separator loc sep @ out else out in
        let env =
          List.map (fun (name, bs) -> (name, List.nth bs k)) repeated @ env
        in
        expand_items ~id ~loc env ts out
      in
      List.fold_left round out (List.init count Fun.id)

let substitute ~id ~at:loc template env =
  List.rev (expand_items ~id ~loc env template [])

(* macros.checked-templates: what stands for a fragment while its template is checked. *)
let placeholder form kind name : Token.t list =
  match (kind, form) with
  | "expr", Pattern | "pattern", Expr -> [ DOLLAR ]
  | "pattern", Pattern -> [ UNDERSCORE ]
  | "block", _ -> [ LBRACE; RBRACE ]
  | ("Name" | "type"), _ -> [ UIDENT (Macro_marks.hole name) ]
  | _ -> [ LIDENT (Macro_marks.hole name) ]

let rec hole_items form kinds ts out =
  List.fold_left (fun out t -> hole_item form kinds t out) out ts

and hole_item form kinds (t : tree) out =
  match t.desc with
  | Token a -> at t.loc (token a) :: out
  | Group (d, ts, close) ->
      let out =
        hole_items form kinds ts (at t.loc (Macro_tokens.opener d) :: out)
      in
      at close (Macro_tokens.closer d) :: out
  | Fragment (n, _) ->
      let kind = Option.value (List.assoc_opt n.desc kinds) ~default:"expr" in
      List.rev_append (List.map (at t.loc) (placeholder form kind n.desc)) out
  | Repeat (ts, _, _) -> hole_items form kinds ts out

let holes form kinds template = List.rev (hole_items form kinds template [])

let parse_expr ~file ~at:loc tokens =
  Parse_run.run ~macros:true ~file Parser.Incremental.example
    (tokens @ [ at loc EOF ])

let parse_pattern ~file ~at:loc tokens =
  Parse_run.run ~macros:true ~file Parser.Incremental.pattern_example
    (tokens @ [ at loc EOF ])

let parse_type ~file ~at:loc tokens =
  Parse_run.run ~macros:true ~file Parser.Incremental.type_example
    (tokens @ [ at loc EOF ])
