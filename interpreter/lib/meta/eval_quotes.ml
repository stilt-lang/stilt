(* Quotes at run time (macros.splices, macros.quote-hygiene and macros.outside-run): a quote's tokens,
   written out with its splices filled. In a macro's run, the tokens a quote
   writes are placed at the use, and outside one at the quote. *)

open Value
open Eval_state
open Eval_types
module M = Macro_values

(* Outside a run, a quote numbers its names apart from every run's (macros.outside-run). *)
let outside = ref 0

let mark home =
  match !running with
  | Some r -> r.mark home
  | None ->
      decr outside;
      - !outside

let place loc = match !running with Some r -> r.at | None -> loc
let at = Macro_tokens.at

let ident text : Token.t =
  match Seq.find (fun c -> c <> '_') (String.to_seq text) with
  | Some 'A' .. 'Z' -> UIDENT text
  | _ -> LIDENT text

(* macros.quote-hygiene: a spliced name is the user's, where the user wrote it, or a fresh
   one, numbered as an expansion is. *)
let name_token loc (n : M.name) =
  match n.fresh with
  | Some id -> at loc (ident (Macro_marks.mark id n.written))
  | None -> at (M.placed n.at) (ident n.written)

(* numbers.negative-literals: a [-] directly before a literal is part of it, so where
   both are placed at one position, the literal stays one column after the
   [-]. *)
let signed (loc : Ast.loc) literal =
  [ at loc MINUS; at { loc with col = loc.col + 1 } literal ]

(* macros.literal-splices: a number without a type, and a negative one in parentheses, whose
   [-] is part of the literal. *)
let number loc ~literal text =
  if String.starts_with ~prefix:"-" text then
    let digits = String.sub text 1 (String.length text - 1) in
    (at loc LPAREN :: signed loc (literal digits)) @ [ at loc RPAREN ]
  else [ at loc (literal text) ]

let float fr loc ~f32 x =
  if Float.is_finite x || Option.is_none !running then
    number loc ~literal:(fun t -> Token.FLOAT t) (Floats.to_string ~f32 x)
  else panic fr loc "splice" "a NaN or an infinite float can't be spliced"

(* macros.splices: the tokens that a value of type [ty] writes: code as one form, as
   if parenthesized, a name, or a literal. *)
let written fr loc ty v : Lexer.token list =
  match (v, numeric ty) with
  | Meta (Code { form = Code_field; tokens; _ }), _ -> tokens
  | Meta (Code c), _ -> (at loc LPAREN :: c.tokens) @ [ at loc RPAREN ]
  | Meta (Name n), _ -> [ name_token loc n ]
  | Str s, _ -> [ at loc (Token.STRING s) ]
  | Bool b, _ -> [ at loc (if b then Token.TRUE else Token.FALSE) ]
  | Int x, Integer k ->
      number loc ~literal:(fun t -> Token.INT t) (Ints.to_string k x)
  | Float x, Floating f32 -> float fr loc ~f32 x
  | _ -> invalid_arg "Eval_quotes.written"

let closes : Token.t -> bool = function
  | RPAREN | RBRACKET | RBRACE -> true
  | _ -> false

(* The tokens after a splice's [$]: its name, or its parenthesized
   expression, after the [..] of a spread. *)
let after_splice ~spread (tokens : Lexer.token list) =
  let tokens =
    match tokens with
    | { token = DOT_DOT; _ } :: rest when spread -> rest
    | _ -> tokens
  in
  let rec past depth = function
    | [] -> []
    | (t : Lexer.token) :: rest -> (
        match t.token with
        | LPAREN | LBRACKET | LBRACE -> past (depth + 1) rest
        | (RPAREN | RBRACKET | RBRACE) when depth = 1 -> rest
        | RPAREN | RBRACKET | RBRACE -> past (depth - 1) rest
        | _ when depth = 0 -> rest
        | _ -> past depth rest)
  in
  past 0 tokens

(* macros.spreads: a spread's elements, separated by commas. An empty one takes the
   comma after it, and a closing bracket after one keeps it a list of
   elements, as [(x,)] is a tuple. *)
let spread fr loc ty v (rest : Lexer.token list) =
  let element = match Types.resolve ty with Con (_, [ e ]) -> e | _ -> ty in
  let items = match v with List xs -> Vec.to_list xs | _ -> [] in
  let pieces = List.map (written fr loc element) items in
  let joined =
    List.concat
      (List.mapi (fun i p -> if i = 0 then p else at loc COMMA :: p) pieces)
  in
  match (items, rest) with
  | [], { token = COMMA; _ } :: rest -> ([], rest)
  | _ :: _, t :: _ when closes t.token -> (joined @ [ at loc COMMA ], rest)
  | _ -> (joined, rest)

(* macros.quote-hygiene: an identifier the quote writes, but for a member after a [.], is
   marked with the quote's number, and every token it writes is placed at
   [loc]. *)
let own loc id (t : Lexer.token) (out : Lexer.token list) =
  let after_dot =
    match out with { token = DOT; _ } :: _ -> true | _ -> false
  in
  let token : Token.t =
    match t.token with
    | LIDENT s when not after_dot -> LIDENT (Macro_marks.mark id s)
    | UIDENT s when not after_dot -> UIDENT (Macro_marks.mark id s)
    | token -> token
  in
  at loc token :: out

let fill t fr loc id (q : Tast.quote) =
  let rec go out (tokens : Lexer.token list) (splices : Tast.splice list) =
    match (tokens, splices) with
    | [], _ -> List.rev out
    | d :: rest, s :: others
      when d.token = DOLLAR && (d.line, d.col) = (s.at.line, s.at.col) ->
        let rest = after_splice ~spread:s.spread rest in
        let v = t.eval t fr s.value in
        let ty = concrete fr s.value.ty in
        if s.spread then
          let filled, rest = spread fr loc ty v rest in
          go (List.rev_append filled out) rest others
        else go (List.rev_append (written fr loc ty v) out) rest others
    | ( ({ token = MINUS; _ } as minus)
        :: ({ token = INT _ | FLOAT _; _ } as literal)
        :: rest,
        _ )
      when literal.line = minus.line && literal.col = minus.col + 1 ->
        go (List.rev_append (signed loc literal.token) out) rest splices
    | tok :: rest, _ -> go (own loc id tok out) rest splices
  in
  go [] (Macro_tokens.flatten q.tokens) q.splices

let quote t fr loc (q : Tast.quote) =
  let here = place loc in
  let id = mark q.home in
  let filled = fill t fr here id q in
  let tokens =
    match q.form with
    | Code_expr -> (at here LBRACE :: filled) @ [ at here RBRACE ]
    | Code_type | Code_pattern | Code_field -> filled
  in
  (* macros.step-limits: code that splices code may hold twice as much, with no
     step between, so a run that it takes past its memory stops here. *)
  reserve 0;
  Meta (Code { tokens; at = M.point here; form = q.form })
