(* The driver of the grammar's automaton. *)

open Ast
module I = Parser.MenhirInterpreter

type 'a start = Lexing.position -> 'a I.checkpoint

let syntax_error ~file (loc : loc) message =
  {
    Diagnostic.code = Code.e0100;
    file;
    line = loc.line;
    col = loc.col;
    message;
  }

let describe : Token.t -> string = function
  | SEP -> "end of the statement"
  | EOF -> "end of the file"
  | LIDENT name | UIDENT name -> Printf.sprintf "`%s`" name
  | INT text | FLOAT text -> Printf.sprintf "the number `%s`" text
  | STRING _ | STRING_HEAD _ -> "a string"
  | STRING_MID _ | STRING_TAIL _ | FORMAT _ -> "the rest of a string"
  | token -> Printf.sprintf "`%s`" (Token.to_string token)

let error_message : Token.t -> string = function
  | DOC _ | MISPLACED_DOC ->
      "a doc comment must come directly before a declaration"
  | token -> "unexpected " ^ describe token

(* The token the parser reads for [t]: a [MACRO_TOKEN] where the grammar
   accepts one, among the tokens of a macro (macros.patterns, macros.templates and macros.uses), a
   contextual keyword where the grammar accepts it, and the lexer's token
   everywhere else (lexical.contextual-keywords). A keyword that a template writes is one
   still, with its mark (macros.hygiene). *)
let contextual ~macros checkpoint (t : Lexer.token) position =
  if
    macros
    && Macro_tokens.stands_for_itself t.token
    && I.acceptable checkpoint (MACRO_TOKEN A_sep) position
  then Token.MACRO_TOKEN (Macro_tokens.atom t.token)
  else
    match t.token with
    | LIDENT text -> (
        match Token.contextual_keyword (Macro_marks.base text) with
        | Some keyword when I.acceptable checkpoint keyword position -> keyword
        | _ -> t.token)
    | token -> token

(* Whether tokens declare a macro or use one, a [lower] name followed by [!]
   and a group, so that the driver asks for [MACRO_TOKEN]s only where it may
   find them. *)
let rec has_macros : Lexer.token list -> bool = function
  | { token = SYNTAX; _ } :: _ -> true
  | { token = LIDENT _; _ }
    :: { token = BANG; _ }
    :: { token = LPAREN | LBRACKET; _ }
    :: _ ->
      true
  | _ :: rest -> has_macros rest
  | [] -> false

(* A token's position, whose [pos_bol] holds its index among the tokens
   offered, through which a quote finds its contents (Quote_tokens). *)
let position ?(index = 0) (t : Lexer.token) =
  {
    Lexing.pos_fname = "";
    pos_lnum = t.line;
    pos_bol = index;
    pos_cnum = t.col;
  }

(* macros.splices: the quotes open where the driver is, each by the depth of
   brackets outside its [{], and the last two tokens offered, so that [$]
   inside a quote is offered as a splice's, and is a syntax error everywhere
   else but in a [syntax] declaration. *)
type quoting = {
  mutable depth : int;
  mutable opened : int list;
  mutable last : Token.t list;
}

let quoting () = { depth = 0; opened = []; last = [] }

let quoted q (token : Token.t) : Token.t =
  let token =
    if token = DOLLAR && q.opened <> [] then Token.SPLICE else token
  in
  (match token with
  | LBRACE | LPAREN | LBRACKET ->
      (match q.last with
      | (QUOTE :: _ | (TYPE | PATTERN | FIELD) :: QUOTE :: _)
        when token = LBRACE ->
          q.opened <- q.depth :: q.opened
      | _ -> ());
      q.depth <- q.depth + 1
  | RBRACE | RPAREN | RBRACKET -> (
      q.depth <- q.depth - 1;
      match q.opened with
      | d :: rest when d = q.depth -> q.opened <- rest
      | _ -> ())
  | _ -> ());
  q.last <- token :: List.filteri (fun i _ -> i = 0) q.last;
  token

let rec resume checkpoint =
  match (checkpoint : _ I.checkpoint) with
  | Shifting _ | AboutToReduce _ -> resume (I.resume checkpoint)
  | _ -> checkpoint

(* Runs an entry point over [tokens], returning its result or its syntax
   error. Positions reach the grammar's actions through [Lexing.position]s
   whose [pos_cnum] holds the column. *)
let run ?macros ~file start (tokens : Lexer.token list) =
  let macros = match macros with Some m -> m | None -> has_macros tokens in
  let q = quoting () in
  Quote_tokens.reading tokens;
  (* [offered] holds the tokens offered so far, latest first. *)
  let index = ref 0 in
  let rec loop checkpoint tokens offered =
    match ((checkpoint : _ I.checkpoint), offered) with
    | InputNeeded _, _ -> (
        match tokens with
        | [] -> Error None
        | (t : Lexer.token) :: rest ->
            let p = position ~index:!index t in
            incr index;
            let token = quoted q (contextual ~macros checkpoint t p) in
            let t = { t with token } in
            loop (I.offer checkpoint (t.token, p, p)) rest (t :: offered))
    | (Shifting _ | AboutToReduce _), _ ->
        loop (I.resume checkpoint) tokens offered
    | HandlingError _, failed :: earlier ->
        (* A doc comment that nothing documents is the error, rather than
           the token after it. *)
        let t =
          match earlier with
          | ({ token = DOC _; _ } as doc) :: _ -> doc
          | _ -> failed
        in
        let loc = { line = t.line; col = t.col } in
        Error (Some (syntax_error ~file loc (error_message t.token)))
    | HandlingError _, [] | Rejected, _ ->
        (* An error is detected only at an offered token, and the loop stops
           at the first. *)
        assert false
    | Accepted result, _ -> Ok result
  in
  loop (start Lexing.dummy_pos) tokens []

(* Offers the tokens one at a time, and remembers the last point at which
   the parser could end. *)
let longest ~file:_ start (tokens : Lexer.token list) =
  let q = quoting () in
  Quote_tokens.reading tokens;
  let rec go checkpoint n tokens best =
    match (checkpoint : _ I.checkpoint) with
    | InputNeeded _ -> (
        let here =
          match (tokens, best) with
          | t :: _, _ -> position t
          | [], Some (_, _, p) -> p
          | [], None -> Lexing.dummy_pos
        in
        let best =
          if I.acceptable checkpoint EOF here then Some (n, checkpoint, here)
          else best
        in
        match tokens with
        | [] -> best
        | (t : Lexer.token) :: rest ->
            let p = position ~index:n t in
            let token = quoted q (contextual ~macros:true checkpoint t p) in
            go (resume (I.offer checkpoint (token, p, p))) (n + 1) rest best)
    | _ -> best
  in
  match go (resume (start Lexing.dummy_pos)) 0 tokens None with
  | Some (n, checkpoint, p) -> (
      match resume (I.offer checkpoint (EOF, p, p)) with
      | Accepted tree -> Some (n, tree)
      | _ -> None)
  | None -> None
