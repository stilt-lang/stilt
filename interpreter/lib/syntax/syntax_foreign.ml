(* The words that other languages begin a declaration with, which begin a part of their own
   (syntax.parts), and what a part that begins with one declares when it breaks
   (errors.broken-parts and errors.broken-blocks). *)

open Token

(* What a part that begins with the word [w] declares, when another language begins a
   declaration with it (syntax.parts and errors.broken-parts): [`Before_fn] for [mutating],
   which comes before [fn]. *)
let word = function
  | "def" | "func" | "function" | "fun" -> Some `Fn
  | "struct" | "class" | "enum" -> Some `Type
  | "interface" | "protocol" -> Some `Trait
  | "extension" -> Some `Nothing
  | "mutating" -> Some `Before_fn
  | _ -> None

(* Whether [token] is a word that another language begins a declaration with, given the token
   after it: before a name, or before [fn] for [async] and [mutating]. In a block, only those
   that begin a function (errors.broken-blocks). *)
let starts ~block (token : Token.t) (next : Token.t option) =
  let named =
    match next with Some (LIDENT _ | UIDENT _) -> true | _ -> false
  in
  match token with
  | ASYNC -> next = Some FN
  | LET | VAR -> (not block) && named
  | LIDENT w -> (
      match word w with
      | Some `Before_fn -> next = Some FN
      | Some `Fn -> named
      | Some (`Type | `Trait | `Nothing) -> (not block) && named
      | None -> false)
  | _ -> false

(* What a part from [kw] to [hi] that begins with another language's word declares, with the
   index of the token before its name (errors.broken-parts). *)
let kind (ts : Lexer.token array) kw hi =
  let at j = if j < hi then Some ts.(j).token else None in
  match (ts.(kw).token, at (kw + 1), at (kw + 2)) with
  | (ASYNC | LIDENT "mutating"), Some FN, Some (LIDENT _) -> Some (kw + 1, `Fn)
  | LIDENT w, Some (LIDENT _), _ when word w = Some `Fn -> Some (kw, `Fn)
  | LIDENT w, Some (UIDENT _), _ when word w = Some `Type -> Some (kw, `Type)
  | LIDENT w, Some (UIDENT _), _ when word w = Some `Trait -> Some (kw, `Trait)
  | _ -> None
