include Token_type

type token = t

let word text = List.assoc_opt text Lexicon.keywords
let contextual_keyword text = List.assoc_opt text Lexicon.contextual
let punctuation = Lexicon.punctuation

let to_string = function
  | LIDENT name -> Printf.sprintf "LIDENT %s" name
  | UIDENT name -> Printf.sprintf "UIDENT %s" name
  | UNDERSCORE -> "_"
  | INT text -> Printf.sprintf "INT %s" text
  | FLOAT text -> Printf.sprintf "FLOAT %s" text
  | STRING text -> Printf.sprintf "STRING %S" text
  | STRING_HEAD text -> Printf.sprintf "STRING_HEAD %S" text
  | STRING_MID text -> Printf.sprintf "STRING_MID %S" text
  | STRING_TAIL text -> Printf.sprintf "STRING_TAIL %S" text
  | FORMAT spec -> Printf.sprintf "FORMAT %S" spec
  | SEP -> "SEP"
  | DOC _ -> "DOC"
  | MISPLACED_DOC -> "MISPLACED_DOC"
  | MACRO_TOKEN _ -> "MACRO_TOKEN"
  | SPLICE -> "$"
  | EOF -> "EOF"
  | token -> (
      let spelled (_, candidate) = candidate = token in
      match List.find_opt spelled (Lexicon.keywords @ Lexicon.contextual) with
      | Some (text, _) -> text
      | None -> fst (List.find spelled punctuation))
