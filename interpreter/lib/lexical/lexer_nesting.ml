(* lexical.nesting: brackets and interpolations nest at most [levels] deep.
   Reading the tokens before the file's first lexical error in order, each
   opening bracket and each interpolation's [{] opens a level and each closing
   one closes the innermost open, if any; a middle part of a string ends one
   interpolation and begins the next. The breach is reported at the bracket
   that opens a level with [levels] open, or at the quote of the string whose
   interpolation does, which is where the lexer places a string's first part. *)

let levels = 256

let in_tokens ~file (tokens : Lexer.token list) =
  let rec walk open_ = function
    | [] -> None
    | (t : Lexer.token) :: rest -> (
        let closes =
          match t.token with
          | RPAREN | RBRACKET | RBRACE | STRING_TAIL _ | STRING_MID _ -> true
          | _ -> false
        in
        let open_ = if closes then max 0 (open_ - 1) else open_ in
        match t.token with
        | LPAREN | LBRACKET | LBRACE | STRING_HEAD _ | STRING_MID _ ->
            if open_ = levels then
              Some
                {
                  Diagnostic.code = Code.e0008;
                  file;
                  line = t.line;
                  col = t.col;
                  message =
                    Printf.sprintf
                      "this opens a level %d deep; a file nests at most %d"
                      (levels + 1) levels;
                }
            else walk (open_ + 1) rest
        | _ -> walk open_ rest)
  in
  walk 0 tokens

let too_deep ~file text = in_tokens ~file (Lexer.tokenize ~file text).tokens
