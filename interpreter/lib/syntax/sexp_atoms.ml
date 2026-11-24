(* The atoms of the tree form of a syntax tree, as [stilt-ref parse --sexp]
   prints it, and the token trees of macros. *)

open Ast

type t = Atom of string | List of t list

let rec write buffer = function
  | Atom atom -> Buffer.add_string buffer atom
  | List items ->
      Buffer.add_char buffer '(';
      List.iteri
        (fun i item ->
          if i > 0 then Buffer.add_char buffer ' ';
          write buffer item)
        items;
      Buffer.add_char buffer ')'

let to_string tree =
  let buffer = Buffer.create 256 in
  write buffer tree;
  Buffer.contents buffer

let quote text =
  let buffer = Buffer.create (String.length text + 2) in
  Buffer.add_char buffer '"';
  String.iter
    (function
      | '"' -> Buffer.add_string buffer "\\\""
      | '\\' -> Buffer.add_string buffer "\\\\"
      | '\n' -> Buffer.add_string buffer "\\n"
      | '\t' -> Buffer.add_string buffer "\\t"
      | '\r' -> Buffer.add_string buffer "\\r"
      | '\000' -> Buffer.add_string buffer "\\0"
      | c when Char.code c < 0x20 || Char.code c = 0x7F ->
          Buffer.add_string buffer (Printf.sprintf "\\u{%x}" (Char.code c))
      | c -> Buffer.add_char buffer c)
    text;
  Buffer.add_char buffer '"';
  Buffer.contents buffer

let str text = Atom (quote text)
let tagged tag items = List (Atom tag :: items)
let name (n : name) = Atom n.desc

let path (p : path) =
  Atom (String.concat "." (List.map (fun (n : name) -> n.desc) p))

let with_mode (mode : mode) tree =
  match mode with Let -> tree | Inout -> tagged "inout" [ tree ]

(* Macros: a token as written, and a literal or a piece of an
   interpolated string as a string of its text. *)

let atom = function
  | A_lower s | A_upper s | A_word s | A_punct s -> Atom s
  | A_int s
  | A_float s
  | A_string s
  | A_string_head s
  | A_string_mid s
  | A_string_tail s
  | A_format s ->
      str s
  | A_sep -> Atom ";"

let delim = function
  | Paren -> "paren"
  | Bracket -> "bracket"
  | Brace -> "brace"

let rec tree (t : tree) =
  match t.desc with
  | Token a -> atom a
  | Group (d, ts, _) -> tagged (delim d) (List.map tree ts)
  | Fragment (n, None) -> tagged "frag" [ name n ]
  | Fragment (n, Some k) -> tagged "frag" [ name n; name k ]
  | Repeat (ts, sep, op) ->
      tagged "rep"
        (Atom (Option.value sep ~default:"_") :: Atom op :: List.map tree ts)

let macro_arm { pattern; block; template } =
  let block =
    Option.map (fun (n, k) -> tagged "frag" [ name n; name k ]) block
  in
  tagged "arm"
    ((tree pattern :: Option.to_list block)
    @ [ tagged "template" (List.map tree template) ])

(* Expressions *)

let binary = function
  | Add -> "+"
  | Sub -> "-"
  | Mul -> "*"
  | Div -> "/"
  | Rem -> "%"
  | Add_wrap -> "+%"
  | Sub_wrap -> "-%"
  | Mul_wrap -> "*%"
  | Eq -> "=="
  | Ne -> "!="
  | Lt -> "<"
  | Le -> "<="
  | Gt -> ">"
  | Ge -> ">="
  | And -> "&&"
  | Or -> "||"
  | Bit_and -> "&"
  | Bit_or -> "|"
  | Bit_xor -> "^"
  | Shl -> "<<"
  | Shr -> ">>"
