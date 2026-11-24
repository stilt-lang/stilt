(* A procedural macro's run on a use (macros.running, macros.failed-uses and macros.step-limits): the values of
   its parts, the call of the macro, and how the run ends. *)

open Value
open Eval_state
module M = Macro_values

type call = Hir.item -> value array -> Ast.loc -> value

let item name = { Hir.home = "std.meta"; name }

(* A string literal of the use's file, whose source the file's text gives. *)
let literal source (token : Lexer.token) text : M.text =
  let at = Macro_tokens.loc token in
  let raw = Option.bind source (fun s -> Macro_texts.raw_literal s at) in
  { value = text; origin = Literal { at; raw; named = None } }

let tokens source trees (close : Ast.loc) =
  let span t = M.point (Macro_tokens.loc t) in
  let text (t : Lexer.token) =
    match t.token with
    | STRING s -> literal source t s
    | _ -> literal source t ""
  in
  let items =
    Macro_lexed.tokens
      { span; text; written = source }
      (Macro_tokens.flatten trees)
  in
  Eval_macro_natives.tokens items (M.point close)

let span_of (tokens : Lexer.token list) =
  match (tokens, List.rev tokens) with
  | first :: _, last :: _ ->
      { (M.point (Macro_tokens.loc first)) with stop = Macro_tokens.loc last }
  | _ -> M.point { line = 1; col = 1 }

(* macros.tokens-and-code: the values of a use's parts. *)
let arg source : Procs.arg -> value = function
  | Code_arg (form, tokens) -> Meta (Code { tokens; at = span_of tokens; form })
  | Text_arg l -> Meta (Text (literal source l.token l.text))
  | File_arg (l, contents) ->
      let at = Macro_tokens.loc l.token in
      Record
        ( item "File",
          [
            ("path", Str l.text);
            ("text", Meta (Text { value = contents; origin = File_text at }));
            ("span", Meta (Span (M.point at)));
          ] )
  | Tokens_arg (trees, close) -> tokens source trees close

(* macros.raised-errors: a raised error's message, with its notes and the macro's name. *)
let message (e : M.error) name =
  let note ((s : M.span), m) =
    Printf.sprintf "; note at %d:%d: %s" s.start.line s.start.col m
  in
  let file =
    match e.at.named with
    | Some _ ->
        Printf.sprintf " (at %d:%d of the file)" e.at.start.line e.at.start.col
    | None -> ""
  in
  Printf.sprintf "%s%s%s; raised by `%s!`" e.message file
    (String.concat "" (List.map note e.notes))
    name

(* macros.step-limits: the frames of the module's own functions that were running,
   innermost last, by their names, a run of one function's frames written
   once with its count. *)
let frames (r : run) named =
  let rec runs = function
    | [] -> []
    | f :: rest -> (
        match runs rest with
        | (g, n) :: more when g = f -> (f, n + 1) :: more
        | more -> (f, 1) :: more)
  in
  let shown (f, n) =
    if n = 1 then "`" ^ f ^ "`" else Printf.sprintf "`%s` %d times" f n
  in
  match runs (List.rev_map (fun (_, at) -> named at) r.frames) with
  | [] -> ""
  | fs -> "; running " ^ String.concat ", then " (List.map shown fs)

let ended (r : run) named = function
  | Stopped why -> Procs.Stopped (why ^ frames r named)
  | Panicked { kind; detail; _ } ->
      Procs.Stopped
        (Printf.sprintf "it panicked: %s: %s%s" kind detail (frames r named))
  | Fatal why -> Procs.Stopped (why ^ frames r named)
  | Stack_overflow -> Procs.Stopped ("it ran out of stack" ^ frames r named)
  | e -> raise e

let run (call : call) ~named ~source (use : Procs.use) : Procs.outcome =
  let args = Array.of_list (List.map (arg source) use.args) in
  let r =
    {
      at = use.at;
      home = use.home;
      mark = use.mark;
      steps = 0;
      frames = [];
      depth = 0;
    }
  in
  running := Some r;
  let outcome =
    match call { home = use.home; name = use.name } args use.at with
    | Meta (Code c) -> Procs.Expanded c.tokens
    | _ -> invalid_arg "Macro_run.run"
    | exception Raised (Meta (Error e)) ->
        Procs.Raised (M.placed e.at, message e use.name)
    | exception e -> ended r named e
  in
  running := None;
  outcome
