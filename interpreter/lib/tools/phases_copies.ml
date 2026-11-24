(* docs.bodies-compared, docs.body-size, docs.same-body and docs.duplicate-bodies: duplicate bodies. *)

type candidate = {
  file : string;
  path : string;
  at : Ast.loc;
  params : Hir.var list;
  block : Tast.block;
}

(* docs.body-size. *)
let fewest = 20

(* The index of the [{] that opens the body of the function whose name is the
   token at [i]: the first [{] outside brackets that doesn't open a row, which
   follows a [/]. A body written [= ?] has none. *)
let opening (tokens : Lexer.token array) i =
  let rec go i depth previous =
    if i >= Array.length tokens then None
    else
      match tokens.(i).token with
      | Token.LBRACE when depth = 0 && previous <> Token.SLASH -> Some i
      | (Token.EQ | Token.EOF) when depth = 0 -> None
      | (Token.LPAREN | Token.LBRACKET | Token.LBRACE) as t ->
          go (i + 1) (depth + 1) t
      | (Token.RPAREN | Token.RBRACKET | Token.RBRACE) as t ->
          go (i + 1) (depth - 1) t
      | t -> go (i + 1) depth t
  in
  go (i + 1) 0 tokens.(i).token

(* The tokens from the [{] at [i] to the [}] that closes it, without
   separators, a string literal counting as one token even when it
   interpolates, as lexical.commented-out-code.single-token counts them. *)
let counted (tokens : Lexer.token array) i =
  let rec go i braces strings count =
    if i >= Array.length tokens then count
    else
      let inside = if strings = 0 then 1 else 0 in
      match tokens.(i).token with
      | Token.SEP -> go (i + 1) braces strings count
      | Token.STRING_HEAD _ -> go (i + 1) braces (strings + 1) (count + inside)
      | Token.STRING_TAIL _ -> go (i + 1) braces (strings - 1) count
      | Token.LBRACE -> go (i + 1) (braces + 1) strings (count + inside)
      | Token.RBRACE when braces = 1 -> count + inside
      | Token.RBRACE -> go (i + 1) (braces - 1) strings (count + inside)
      | _ -> go (i + 1) braces strings (count + inside)
  in
  go i 0 0 0

(* How many tokens the body of the function named at [at] holds. *)
let tokens_of (tokens : Lexer.token array) (at : Ast.loc) =
  let rec find i =
    if i >= Array.length tokens then None
    else if tokens.(i).line = at.line && tokens.(i).col = at.col then Some i
    else find (i + 1)
  in
  match Option.bind (find 0) (opening tokens) with
  | Some i -> counted tokens i
  | None -> 0

(* The tokens of a file: lexed from its start, and again from the line after
   each lexical error, as errors.parts reads the parts after it. No token
   spans two lines, since a string literal holds no raw newline and no comment
   is a block (lexical.no-block-comments and lexical.string-literals). *)
let lexed ~file text =
  let starts = ref [ 0 ] in
  String.iteri (fun i c -> if c = '\n' then starts := (i + 1) :: !starts) text;
  let starts = Array.of_list (List.rev !starts) in
  let rec from line =
    let at = starts.(line - 1) in
    let out =
      Lexer.tokenize ~line ~file (String.sub text at (String.length text - at))
    in
    match out.error with
    | Some (e : Diagnostic.t) when e.line < Array.length starts ->
        out.tokens @ from (e.line + 1)
    | _ -> out.tokens
  in
  Array.of_list (from 1)

let warnings ~text candidates =
  let files = Hashtbl.create 16 in
  let tokens (c : candidate) =
    let all =
      match Hashtbl.find_opt files c.file with
      | Some all -> all
      | None ->
          let all = lexed ~file:c.file (text c.file) in
          Hashtbl.add files c.file all;
          all
    in
    tokens_of all c.at
  in
  let by_print = Hashtbl.create 64 in
  List.iter
    (fun c ->
      let print = Phases_print.print ~params:c.params c.block in
      let others = Option.value (Hashtbl.find_opt by_print print) ~default:[] in
      Hashtbl.replace by_print print (c :: others))
    candidates;
  let place (c : candidate) = (c.file, c.at.line, c.at.col) in
  let compared group =
    match group with
    | [] | [ _ ] -> []
    | _ ->
        List.sort
          (fun a b -> compare (place a) (place b))
          (List.filter (fun c -> tokens c >= fewest) group)
  in
  Hashtbl.fold
    (fun _ group found ->
      match compared group with
      | first :: (_ :: _ as later) ->
          List.map
            (fun (c : candidate) ->
              Diagnostic.at ~file:c.file Code.w0302 c.at
                ("this function has the same body as `" ^ first.path ^ "`"))
            later
          @ found
      | _ -> found)
    by_print []
