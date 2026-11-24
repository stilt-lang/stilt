open Ast

let syntax_error = Parse_run.syntax_error
let run = Parse_run.run

(* Parses the output of the lexer, returning its first syntax error. *)
let parse_tokens ~file start (lexed : Lexer.output) =
  match (run ~file start lexed.tokens, lexed.error) with
  | Ok result, _ -> Ok result
  | Error (Some diagnostic), _ | Error None, Some diagnostic -> Error diagnostic
  | Error None, None ->
      (* Without a lexical error, the tokens end with [EOF]. *)
      assert false

(* Doc comments (program.doc-comments) *)

let find text pattern =
  let n = String.length pattern in
  let rec go i =
    if i + n > String.length text then None
    else if String.sub text i n = pattern then Some i
    else go (i + 1)
  in
  go 0

let drop_trailing_spaces text =
  let rec last i = if i > 0 && text.[i - 1] = ' ' then last (i - 1) else i in
  String.sub text 0 (last (String.length text))

(* A doc line's text ends before an annotation and the spaces before it
   (program.doc-comments). *)
let without_annotation text =
  match find text "//~" with
  | Some i -> drop_trailing_spaces (String.sub text 0 i)
  | None -> text

(* The doc line of a [///] comment, parsing it if it is an example or a
   property, whose text after [ex:] or [prop:] is lexed as a file is (program.doc-examples; tests.prop-lines). *)
let doc_line ~file (c : Lexer.comment) =
  let text = c.text in
  let from i = String.sub text i (String.length text - i) in
  let rec skip_spaces i =
    if i < String.length text && text.[i] = ' ' then skip_spaces (i + 1) else i
  in
  let first = skip_spaces 0 in
  (* The text of a comment starts after the three characters of [///]. *)
  let parse prefix =
    let start = first + String.length prefix in
    Lexer.tokenize ~line:c.line ~col:(c.col + 3 + start) ~file (from start)
    |> parse_tokens ~file Parser.Incremental.example
    |> Result.map (fun e -> (from (skip_spaces start), e))
  in
  if String.starts_with ~prefix:"ex:" (from first) then
    parse "ex:" |> Result.map (fun (_, e) -> Doc_example e)
  else if String.starts_with ~prefix:"prop:" (from first) then
    parse "prop:"
    |> Result.map (fun (text, e) -> Doc_property (without_annotation text, e))
  else
    (* Any other line's text loses one leading space. *)
    let text = without_annotation text in
    let text =
      if String.starts_with ~prefix:" " text then
        String.sub text 1 (String.length text - 1)
      else text
    in
    Ok (Doc_text text)

let is_code (t : Lexer.token) =
  match t.token with SEP | EOF -> false | _ -> true

(* The index of the first token of code on each line that holds code. Tokens
   come in source order, so a line's first is the first one found. *)
let code_lines (tokens : Lexer.token array) =
  let first = Hashtbl.create 256 in
  Array.iteri
    (fun i (t : Lexer.token) ->
      if is_code t && not (Hashtbl.mem first t.line) then
        Hashtbl.add first t.line i)
    tokens;
  first

(* The index of the first token after [c], of code alone with [~code], or of
   [EOF], or the end. Tokens come in source order, so the first token after [c]
   is found by halving, and the code after it by stepping over separators. *)
let after ?(code = true) (tokens : Lexer.token array) (c : Lexer.comment) =
  let n = Array.length tokens in
  let later (t : Lexer.token) = compare (t.line, t.col) (c.line, c.col) > 0 in
  let rec search lo hi =
    if lo >= hi then lo
    else
      let mid = (lo + hi) / 2 in
      if later tokens.(mid) then search lo mid else search (mid + 1) hi
  in
  let rec go i =
    if i >= n then i
    else
      let t = tokens.(i) in
      if t.token = EOF || is_code t || not code then i else go (i + 1)
  in
  (* [EOF] ends the tokens wherever it stands, so a comment that no token
     follows comes before it. *)
  match go (search 0 n) with
  | i when i = n && n > 0 && tokens.(n - 1).token = EOF -> n - 1
  | i -> i

(* Turns the doc comments into tokens, and returns the token list with them
   in place, and the syntax errors of the doc examples.

   A run of doc comments on consecutive lines, each alone on its line, becomes
   a [DOC] token just before the first token of the next line. Any other doc
   comment becomes a [MISPLACED_DOC]: one that shares its line with code, and a
   run whose next line holds no code. Separators don't count as code. *)
let place_docs ~file (lexed : Lexer.output) =
  let tokens = Array.of_list lexed.tokens in
  let code = code_lines tokens in
  let first_code_on_line line = Hashtbl.find_opt code line in
  let has_code line = Hashtbl.mem code line in
  let errors = ref [] in
  let line c =
    match doc_line ~file c with
    | Ok line -> Some line
    | Error diagnostic ->
        errors := diagnostic :: !errors;
        None
  in
  let inserted = ref [] in
  let insert index token (c : Lexer.comment) =
    inserted :=
      (index, { Lexer.token; line = c.line; col = c.col }) :: !inserted
  in
  let rec take_run line run = function
    | (c : Lexer.comment) :: rest
      when c.doc && c.line = line && not (has_code line) ->
        take_run (line + 1) (c :: run) rest
    | rest -> (List.rev run, line, rest)
  in
  let rec runs = function
    | [] -> ()
    | (c : Lexer.comment) :: rest when not c.doc -> runs rest
    | c :: rest when has_code c.line ->
        ignore (line c);
        (* Before the separators after it, so that it is the error that the
           grammar finds first, at its comment (syntax.doc-comment-placement). *)
        insert (after ~code:false tokens c) MISPLACED_DOC c;
        runs rest
    | c :: _ as comments ->
        let run, next_line, rest = take_run c.line [] comments in
        let lines = List.filter_map line run in
        (match first_code_on_line next_line with
        | Some index -> insert index (DOC lines) c
        | None -> insert (after tokens c) MISPLACED_DOC c);
        runs rest
  in
  runs lexed.comments;
  (* The inserted tokens go before the token at their index, those at one
     index in the order they were inserted, which a stable sort keeps. *)
  let pending =
    List.stable_sort (fun (a, _) (b, _) -> compare a b) (List.rev !inserted)
  in
  let rec merge i pending acc =
    match pending with
    | (index, token) :: rest when index <= i -> merge i rest (token :: acc)
    | _ when i >= Array.length tokens -> List.rev acc
    | _ -> merge (i + 1) pending (tokens.(i) :: acc)
  in
  (merge 0 pending [], List.rev !errors)

let earliest (a : Diagnostic.t) (b : Diagnostic.t) =
  if compare (a.line, a.col) (b.line, b.col) <= 0 then a else b

(* lexical.commented-out-code. Doc comments and annotations aren't [//] comments in
   this sense. A comment is exempt when its text is a single token, perhaps
   after a leading [-] or inside one pair of parentheses, in either order
   (lexical.commented-out-code.single-token), or [()]: so [// fallthrough], [// 42], [// -1],
   [// (-1)], [// (unused)] and [// ?] pass. A string literal counts as one
   token, even when it interpolates, and a written [;] counts as a token, so
   [// x;] gets the warning. *)
let holds_code ~file (c : Lexer.comment) =
  let lexed = Lexer.tokenize ~line:c.line ~col:(c.col + 2) ~file c.text in
  let tokens =
    List.filter
      (fun (t : Lexer.token) ->
        match t.token with SEP | EOF -> false | _ -> true)
      lexed.tokens
  in
  let rec signs : Lexer.token list -> Lexer.token list = function
    | { token = MINUS; _ } :: rest -> signs rest
    | ts -> ts
  in
  let bare ts =
    match (signs ts, List.rev ts) with
    | ({ token = LPAREN; _ } :: _ as ts), { token = RPAREN; _ } :: _ ->
        signs (List.filteri (fun i _ -> i > 0 && i < List.length ts - 1) ts)
    | ts, _ -> ts
  in
  (* Whether the tokens make one string literal: the interpolations that the
     first token opens close only at the last. *)
  let one_string (ts : Lexer.token list) =
    let rec depth d = function
      | [] -> false
      | [ (t : Lexer.token) ] -> (
          match t.token with STRING_TAIL _ -> d = 1 | _ -> false)
      | (t : Lexer.token) :: rest -> (
          match t.token with
          | STRING_HEAD _ -> depth (d + 1) rest
          | STRING_TAIL _ -> d > 1 && depth (d - 1) rest
          | _ -> d > 0 && depth d rest)
    in
    match ts with { token = STRING_HEAD _; _ } :: _ -> depth 0 ts | _ -> false
  in
  (* The text holds no newline, so each separator in it is a written [;]. *)
  let separators = lexed.written - List.length tokens in
  let exempt =
    lexed.written <= 1
    || separators = 0
       && match bare tokens with [] | [ _ ] -> true | ts -> one_string ts
  in
  (not exempt) && Option.is_none lexed.error
  && Result.is_ok (run ~file Parser.Incremental.code lexed.tokens)

let placed_with_examples ?line ~file text =
  let lexed = Lexer.tokenize ?line ~file text in
  let tokens, errors = place_docs ~file lexed in
  ({ lexed with tokens }, errors)

let placed ~file text = fst (placed_with_examples ~file text)

(* views.std-view: only the standard library declares native types. Anywhere
   else, [type T = ?] is a form of [type] that declarations.no-aliases doesn't allow,
   the alias form, which is a syntax error, at its [?]. *)
let native_type ~file (m : module_) =
  List.find_map
    (fun (item : item) ->
      match item.desc with
      | Decl { kind = Type { def = Native at; _ }; _ } ->
          Some
            (syntax_error ~file at
               "unexpected `?`: only the standard library declares a type \
                without a representation; declare a record or a variant type")
      | _ -> None)
    m.items

let parse_part ~file tokens =
  match run ~file Parser.Incremental.file tokens with
  | Ok m -> (
      match native_type ~file m with Some d -> Error (Some d) | None -> Ok m)
  | Error _ as e -> e

let comment_warnings ~file comments =
  List.filter_map
    (fun (c : Lexer.comment) ->
      if
        c.doc
        || String.starts_with ~prefix:"~" c.text
        || not (holds_code ~file c)
      then None
      else
        Some
          (Diagnostic.at ~file Code.w0001
             { line = c.line; col = c.col }
             "this comment holds code; delete code that isn't used"))
    comments

(* tasks.std-task: [await] stays a keyword, and names one declaration, the
   method of [std.task]'s tasks, which only the standard library writes. *)
let rec await_declared : Lexer.token list -> Lexer.token list = function
  | ({ token = FN; _ } as f) :: ({ token = AWAIT; _ } as a) :: rest ->
      f :: { a with token = LIDENT "await" } :: await_declared rest
  | t :: rest -> t :: await_declared rest
  | [] -> []

let parse_lexed ~native ~file (lexed : Lexer.output) =
  let lexed =
    if native then { lexed with tokens = await_declared lexed.tokens }
    else lexed
  in
  let tokens, example_errors = place_docs ~file lexed in
  let parsed =
    parse_tokens ~file Parser.Incremental.file { lexed with tokens }
  in
  let errors =
    match parsed with
    | Ok m when not native -> Option.to_list (native_type ~file m)
    | Ok _ | Error _ -> []
  in
  match (parsed, errors @ example_errors) with
  | Ok m, [] -> Ok (m, comment_warnings ~file lexed.comments)
  | Ok _, e :: es -> Error (List.fold_left earliest e es)
  | Error d, es -> Error (List.fold_left earliest d es)

(* lexical.nesting: a file that nests too deep is not parsed. *)
let parse ?(native = false) ~file text =
  let lexed = Lexer.tokenize ~file text in
  match Lexer_nesting.in_tokens ~file lexed.tokens with
  | Some error -> Error error
  | None -> parse_lexed ~native ~file lexed
