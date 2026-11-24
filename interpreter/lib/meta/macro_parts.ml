(* The parts of a procedural macro's use (macros.procedural-uses and macros.parts). *)

open Ast

type given =
  | Code of Hir.code * Lexer.token list
  | Literal of Procs.literal * bool
  | Tokens of tree list * loc

(* A part: its trees, where it starts, and the comma or bracket after it. *)
type part = { trees : tree list; start : loc; after : loc }

let is_comma (t : tree) = t.desc = Token (A_punct ",")

(* The parts of a group's trees, split at its commas, with the trees from
   each part on, for a parameter that takes the rest. An empty part is E0227
   at the comma that ends it, and one trailing comma is ignored. *)
let split trees close =
  let rec go acc current rest =
    match rest with
    | [] -> (
        match List.rev current with
        | [] -> Ok (List.rev acc)
        | (first : tree) :: _ as trees ->
            Ok (List.rev ({ trees; start = first.loc; after = close } :: acc)))
    | (t : tree) :: rest when is_comma t -> (
        match current with
        | [] -> Error (t.loc, "this part of the use is empty")
        | _ ->
            let trees = List.rev current in
            let start = (List.hd trees).loc in
            go ({ trees; start; after = t.loc } :: acc) [] rest)
    | t :: rest -> go acc (t :: current) rest
  in
  go [] [] trees

(* The trees from a part on, with the commas between the parts, and without
   a trailing comma. *)
let from (part : part) trees =
  let rec drop = function
    | (t : tree) :: _ as all when t == List.hd part.trees -> all
    | _ :: rest -> drop rest
    | [] -> []
  in
  match List.rev (drop trees) with
  | last :: rest when is_comma last -> List.rev rest
  | all -> List.rev all

(* Where a tree ends: its token, or a group's closing bracket. *)
let ending (t : tree) =
  match t.desc with Group (_, _, close) -> close | _ -> t.loc

(* The trees without the separators that newlines inserted among them, each
   on the token before it: a macro's input has no terminator at its top
   level, as inside [( … )] (lexical.inside-brackets). A written [;] stays,
   and so does every separator inside a group. *)
let written trees =
  let rec go previous = function
    | [] -> []
    | ({ desc = Token A_sep; loc } : tree) :: rest
      when Option.map ending previous = Some loc ->
        go previous rest
    | t :: rest -> t :: go (Some t) rest
  in
  go None trees

let parse ~file (code : Hir.code) ~at tokens =
  let ok = function Ok _ -> Ok () | Error d -> Error d in
  match code with
  | Code_expr -> ok (Macro_expand.parse_expr ~file ~at tokens)
  | Code_pattern -> ok (Macro_expand.parse_pattern ~file ~at tokens)
  | Code_type -> ok (Macro_expand.parse_type ~file ~at tokens)
  | Code_field -> ok (Macro_expand.parse_expr ~file ~at tokens)

let form_name : Hir.code -> string = function
  | Code_expr | Code_field -> "an expression"
  | Code_pattern -> "a pattern"
  | Code_type -> "a type"

(* What a part gives a parameter: a part that parses whole as the code it
   takes, or a string literal without interpolation. *)
let given ~file (input : Procs.input) (part : part) =
  match (input, part.trees) with
  | Takes_code code, trees -> (
      let tokens = Macro_tokens.flatten trees in
      match parse ~file code ~at:part.after tokens with
      | Ok () -> Ok (Code (code, tokens))
      | Error (Some (d : Diagnostic.t)) ->
          Error
            ( { line = d.line; col = d.col },
              Printf.sprintf "this part isn't %s here" (form_name code) )
      | Error None -> Error (part.after, "this part ends before its form does"))
  | (Takes_text | Takes_file), [ ({ desc = Token (A_string text); _ } as t) ] ->
      let token = Macro_tokens.at t.loc (Token.STRING text) in
      Ok (Literal ({ token; text }, input = Takes_file))
  | (Takes_text | Takes_file), _ ->
      Error
        ( part.start,
          "this part isn't a string literal without interpolation, which its \
           parameter takes" )
  | Takes_tokens, trees -> Ok (Tokens (trees, part.after))

let rec all = function
  | [] -> Ok []
  | Ok x :: rest -> Result.map (fun xs -> x :: xs) (all rest)
  | (Error _ as e) :: _ -> e

(* The parts given in order to the parameters, a [meta.Tokens] last one
   taking every part from its own on. *)
let match_parts ~file inputs parts trees close =
  let rec go inputs parts =
    match (inputs, parts) with
    | [], [] -> []
    | [], (extra : part) :: _ ->
        [ Error (extra.start, "this part is one too many for the macro") ]
    | [ Procs.Takes_tokens ], part :: _ ->
        [ Ok (Tokens (from part trees, close)) ]
    | [ Procs.Takes_tokens ], [] -> [ Ok (Tokens ([], close)) ]
    | _ :: _, [] -> [ Error (close, "a part is missing here") ]
    | input :: inputs, part :: parts ->
        given ~file input part :: go inputs parts
  in
  all (go inputs parts)

let args ~file inputs groups =
  match groups with
  | [ { desc = Group (_, trees, close); _ } ] -> (
      match split trees close with
      | Error e -> Error e
      | Ok parts -> match_parts ~file inputs parts trees close)
  | [ { desc = Group (_, trees, close); _ }; block ] -> (
      match (split trees close, List.rev inputs, block.desc) with
      | Error e, _, _ -> Error e
      | Ok _, [], _ ->
          Error (block.loc, "this block is one too many for the macro")
      | Ok parts, last :: others, Group (_, contents, block_close) -> (
          let contents = written contents in
          let start =
            match contents with t :: _ -> t.loc | [] -> block_close
          in
          let body = { trees = contents; start; after = block_close } in
          match match_parts ~file (List.rev others) parts trees close with
          | Error e -> Error e
          | Ok given_parts ->
              Result.map (fun g -> given_parts @ [ g ]) (given ~file last body))
      | Ok _, _ :: _, _ -> invalid_arg "Macro_parts.args")
  | _ -> invalid_arg "Macro_parts.args"
