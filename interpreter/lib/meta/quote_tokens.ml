(* The tokens that the parser reads (macros.quote and macros.outside-run). *)

open Ast

let current : Lexer.token array ref = ref [||]
let reading tokens = current := Array.of_list tokens

let delim : Token.t -> delim option = function
  | LPAREN -> Some Paren
  | LBRACKET -> Some Bracket
  | LBRACE -> Some Brace
  | _ -> None

let closes : Token.t -> bool = function
  | RPAREN | RBRACKET | RBRACE -> true
  | _ -> false

(* The trees of [tokens] up to a closing bracket or their end, and the
   closing bracket's position with what follows it. *)
let rec group (tokens : Lexer.token list) =
  match tokens with
  | [] -> ([], None, [])
  | t :: rest when closes t.token -> ([], Some (Macro_tokens.loc t), rest)
  | t :: rest -> (
      let at = Macro_tokens.loc t in
      match delim t.token with
      | Some d ->
          let inner, close, rest = group rest in
          let close = Option.value close ~default:at in
          let trees, last, rest = group rest in
          ({ desc = Group (d, inner, close); loc = at } :: trees, last, rest)
      | None ->
          let trees, last, rest = group rest in
          ( { desc = Token (Macro_tokens.atom t.token); loc = at } :: trees,
            last,
            rest ))

let trees tokens =
  let rec all tokens =
    match group tokens with
    | trees, None, _ -> trees
    | trees, Some _, rest -> trees @ all rest
  in
  all tokens

let between (a : Lexing.position) (b : Lexing.position) =
  let first = a.pos_bol + 1 in
  let n = b.pos_bol - first in
  if first < 0 || n <= 0 || first + n > Array.length !current then []
  else trees (Array.to_list (Array.sub !current first n))
