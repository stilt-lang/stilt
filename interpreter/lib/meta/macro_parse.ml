(* The parsers that a cursor calls (macros.cursor): the longest run of
   tokens that is a whole expression, pattern or type of the language's own
   grammar, read with no terminator at its top level (macros.part-forms), and stops
   before a [,], a [;] or the end. *)

module M = Macro_values

let parses (form : Hir.code) (tokens : Lexer.token list) =
  let at =
    match List.rev tokens with
    | t :: _ -> Macro_tokens.loc t
    | [] -> { Ast.line = 1; col = 1 }
  in
  let ok = function Ok _ -> Ok () | Error d -> Error d in
  match form with
  | Code_expr | Code_field -> ok (Macro_expand.parse_expr ~file:"" ~at tokens)
  | Code_pattern -> ok (Macro_expand.parse_pattern ~file:"" ~at tokens)
  | Code_type -> ok (Macro_expand.parse_type ~file:"" ~at tokens)

let form_name : Hir.code -> string = function
  | Code_expr | Code_field -> "an expression"
  | Code_pattern -> "a pattern"
  | Code_type -> "a type"

let shown (t : M.token) =
  match t.kind with
  | Word x | Number x | Punct x -> "`" ^ x ^ "`"
  | String_lit _ -> "a string"
  | Interpolated -> "an interpolated string"
  | Group (Paren, _, _) -> "`(`"
  | Group (Bracket, _, _) -> "`[`"
  | Group (Brace, _, _) -> "`{`"

let sub items at k = Array.to_list (Array.sub items at k)

(* Whether the run of [k] tokens from [at] stops before a [,], a [;] or the
   end: no newline ends it, since no terminator is inserted at the top level
   of the tokens (macros.part-forms). *)
let stops (items : M.token array) at k =
  at + k = Array.length items
  || match items.(at + k).kind with Punct ("," | ";") -> true | _ -> false

let code form items at k : M.code =
  let run = sub items at k in
  let first = List.hd run and last = items.(at + k - 1) in
  {
    tokens = Macro_lexed.code run;
    at = { first.span with stop = last.span.stop };
    form;
  }

(* Where a run that parses as no form fails: the token where the parser
   stops, or what ends the run. *)
let failure form (items : M.token array) at (close : M.span) =
  let n = Array.length items in
  let rec first_stop k =
    if k >= n - at || stops items at k then k else first_stop (k + 1)
  in
  let s = first_stop 1 in
  let ending = if at + s < n then Some items.(at + s) else None in
  let raw = List.concat_map (fun (t : M.token) -> t.lexed) (sub items at s) in
  let found =
    match parses form raw with
    | Error (Some d) ->
        List.find_opt
          (fun (t : M.token) ->
            List.exists
              (fun (x : Lexer.token) -> x.line = d.line && x.col = d.col)
              t.lexed)
          (sub items at s)
    | _ -> None
  in
  let message what =
    Printf.sprintf "expected %s, found %s" (form_name form) what
  in
  match (found, ending) with
  | Some t, _ | None, Some t ->
      { M.at = t.span; message = message (shown t); notes = [] }
  | None, None -> { at = close; message = message "the end"; notes = [] }

let parse form (items : M.token array) at close =
  let n = Array.length items in
  let rec longest k =
    if k = 0 then None
    else if
      stops items at k
      && parses form (Macro_lexed.code (sub items at k)) = Ok ()
    then Some k
    else longest (k - 1)
  in
  if at < 0 || at > n then Error (failure form items (min (max at 0) n) close)
  else
    match longest (n - at) with
    | Some k -> Ok (code form items at k, at + k)
    | None when at = n ->
        Error
          {
            M.at = close;
            message =
              Printf.sprintf "expected %s, found the end" (form_name form);
            notes = [];
          }
    | None -> Error (failure form items at close)
