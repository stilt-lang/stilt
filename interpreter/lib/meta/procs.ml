(* What name resolution asks of procedural macros (macros.procedural-uses). *)

type input = Takes_code of Hir.code | Takes_text | Takes_file | Takes_tokens
type signature = { inputs : input list; result : Hir.code }
type state = Usable of signature | Unusable
type literal = { token : Lexer.token; text : string }

type arg =
  | Code_arg of Hir.code * Lexer.token list
  | Text_arg of literal
  | File_arg of literal * string
  | Tokens_arg of Ast.tree list * Ast.loc

type use = {
  home : string;
  name : string;
  file : string;
  at : Ast.loc;
  args : arg list;
  mark : string -> int;
}

type outcome =
  | Expanded of Lexer.token list
  | Raised of Ast.loc * string
  | Stopped of string

type host = {
  state : find:(int -> string -> string option) -> string -> string -> state;
  run : use -> outcome;
  read : file:string -> string -> (string, string) result;
  source : string -> string option;
}

(* macros.procedural-declarations: the input types and result types of [std.meta]. *)
let meta_type (t : Hir.ty) =
  match t.desc with
  | Ty_con ({ home = "std.meta"; name }, []) -> Some name
  | _ -> None

let input t =
  match meta_type t with
  | Some "Expr" -> Some (Takes_code Code_expr)
  | Some "Pattern" -> Some (Takes_code Code_pattern)
  | Some "Type" -> Some (Takes_code Code_type)
  | Some "Text" -> Some Takes_text
  | Some "File" -> Some Takes_file
  | Some "Tokens" -> Some Takes_tokens
  | _ -> None

let result t = match input t with Some (Takes_code c) -> Some c | _ -> None

let none =
  {
    state = (fun ~find:_ _ _ -> Unusable);
    run = (fun _ -> Stopped "no macro runs here");
    read = (fun ~file:_ _ -> Error "no file is read here");
    source = (fun _ -> None);
  }
