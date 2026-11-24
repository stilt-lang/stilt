(* The natives of [std.meta] that macros use (macros.tokens-and-code and macros.cursor). Each
   performs nothing but the allocation of what it makes. *)

open Value
open Eval_state
module M = Macro_values

let item name = { Hir.home = "std.meta"; name }
let variant name args = Variant (item name, args)
let raised (e : M.error) = raise (Raised (Meta (Error e)))

let delim : Ast.delim -> value = function
  | Paren -> variant "Paren" []
  | Bracket -> variant "Bracket" []
  | Brace -> variant "Brace" []

let rec kind : M.kind -> value = function
  | Word s -> variant "Word" [ Str s ]
  | Number s -> variant "Number" [ Str s ]
  | String_lit t -> variant "Text" [ Meta (Text t) ]
  | Interpolated -> variant "Interpolated" []
  | Punct p -> variant "Punct" [ Str p ]
  | Group (d, items, close) -> variant "Group" [ delim d; tokens items close ]

and tokens items close =
  Record
    ( item "Tokens",
      [
        ("items", List (Vec.of_list (List.map (fun t -> Meta (Token t)) items)));
        ("close", Meta (Span close));
      ] )

let tokens_of = function
  | Record (_, [ ("items", List xs); ("close", Meta (Span close)) ]) ->
      ( Array.of_list
          (List.map
             (function Meta (Token t) -> t | _ -> invalid_arg "tokens_of")
             (Vec.to_list xs)),
        close )
  | _ -> invalid_arg "Eval_macro_natives.tokens_of"

(* A string literal's text, as lexed from a text: in a named file, or in a
   literal of the use's file, its source unknown. *)
let literal_text (outer : M.text) (span : M.span) (t : Lexer.token) : M.text =
  let value = match t.token with STRING s -> s | _ -> "" in
  match outer.origin with
  | File_text named ->
      let raw = Macro_texts.raw_literal outer.value (Macro_tokens.loc t) in
      {
        value;
        origin = Literal { at = Macro_tokens.loc t; raw; named = Some named };
      }
  | Literal _ ->
      {
        value;
        origin = Literal { at = span.start; raw = None; named = span.named };
      }

(* macros.tokens-and-code: a text's tokens as lexical.tokens lexes them, raising at the first
   character it can't lex. *)
let lex (x : M.text) =
  let out = Lexer.tokenize ~file:"" x.value in
  let place (l : Ast.loc) = Macro_texts.place x l in
  match out.error with
  | Some d ->
      raised
        {
          at = place { line = d.line; col = d.col };
          message = d.message;
          notes = [];
        }
  | None ->
      let span (t : Lexer.token) = place (Macro_tokens.loc t) in
      let src =
        {
          Macro_lexed.span;
          text = (fun t -> literal_text x (span t) t);
          written = Some x.value;
        }
      in
      let close =
        match List.rev out.tokens with
        | t :: _ -> span t
        | [] -> place { line = 1; col = 1 }
      in
      tokens (Macro_lexed.tokens src out.tokens) close

let text_span fr loc (x : M.text) a b =
  let n = String.length x.value in
  if a < 0L || b < a || Int64.to_int b > n then
    panic fr loc "bounds"
      "the bytes from %Ld to %Ld are out of bounds for a text of %d bytes" a b n
  else
    Meta
      (Span (Macro_texts.span x ~start:(Int64.to_int a) ~stop:(Int64.to_int b)))

let method_ fr loc owner name args =
  match (owner, name, args) with
  | "Span", "to", [| Meta (Span a); Meta (Span b) |] ->
      Meta (Span { a with stop = b.stop })
  | "Token", "kind", [| Meta (Token t) |] -> kind t.kind
  | "Token", "span", [| Meta (Token t) |] -> Meta (Span t.span)
  | "Token", "name", [| Meta (Token t) |] -> (
      match t.lexed with
      | [ { token = LIDENT s | UIDENT s; _ } ] ->
          some (Meta (Name { written = s; at = t.span; fresh = None }))
      | _ -> none)
  | "Text", "value", [| Meta (Text x) |] -> Str x.value
  | "Text", "span", [| Meta (Text x); Int a; Int b |] -> text_span fr loc x a b
  | "Text", "lex", [| Meta (Text x) |] -> lex x
  | "Name", "text", [| Meta (Name n) |] -> Str (M.text n)
  | "Name", "span", [| Meta (Name n) |] -> Meta (Span n.at)
  | ("Expr" | "Pattern" | "Type" | "FieldInit"), "span", [| Meta (Code c) |] ->
      Meta (Span c.at)
  | "Error", "note", [| Meta (Error e); Meta (Span s); Str m |] ->
      let notes =
        if List.length e.notes < 3 then e.notes @ [ (s, m) ] else e.notes
      in
      Meta (Error { e with notes })
  | _ -> invalid_arg ("Eval_macro_natives.method_: " ^ owner ^ "." ^ name)

let parsed form ts at =
  let items, close = tokens_of ts in
  match Macro_parse.parse form items (Int64.to_int at) close with
  | Ok (code, next) -> Tuple [ Meta (Code code); Int (Int64.of_int next) ]
  | Error e -> raised e

let function_ loc name args =
  match (name, args) with
  | "fresh", [| Str s |] ->
      let home = match !running with Some r -> r.home | None -> "" in
      let at = M.point (Eval_quotes.place loc) in
      Meta (Name { written = s; at; fresh = Some (Eval_quotes.mark home) })
  | "error", [| Meta (Span s); Str m |] ->
      Meta (Error { at = s; message = m; notes = [] })
  | "parse_expr", [| ts; Int at |] -> parsed Hir.Code_expr ts at
  | "parse_pattern", [| ts; Int at |] -> parsed Code_pattern ts at
  | "parse_type", [| ts; Int at |] -> parsed Code_type ts at
  | _ -> invalid_arg ("Eval_macro_natives.function_: " ^ name)

(* The owners of the methods of macros' values. *)
let owners =
  [
    "Span";
    "Token";
    "Text";
    "Name";
    "Expr";
    "Pattern";
    "Type";
    "FieldInit";
    "Error";
  ]
