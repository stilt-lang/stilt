(* A file with a syntax error, read a part at a time (errors.parts and errors.resuming): from
   its start, and again from each line where reading resumes after a part
   that breaks. Each part reports its first syntax error, and holds back
   every other diagnostic in its text. *)

open Ast
module P = Syntax_parts

type report = { error : Diagnostic.t; from : loc; until : loc option }

type t = {
  module_ : module_;
  broken : loc list;
  reports : report list;
  extents : P.extent list;
  comments : Lexer.comment list;
  unreadable : bool;
}

(* The words that begin a part. *)
let words =
  [
    "use";
    "impl";
    "pub";
    "extern";
    "fn";
    "type";
    "trait";
    "const";
    "test";
    "syntax";
    "effect";
    "macro";
  ]

(* Whether a line starts, in its first column, with a word that begins a
   part, as a whole word. *)
let starts_with_word line w =
  let n = String.length line and k = String.length w in
  String.starts_with ~prefix:w line
  && (n = k || not (Lexer_source.is_ident_char line.[k]))

(* [line] after the spaces and tabs that start it, which are the only
   whitespace within a line (lexical.whitespace). *)
let after_blanks line =
  let n = String.length line in
  let rec skip i =
    if i < n && (line.[i] = ' ' || line.[i] = '\t') then skip (i + 1) else i
  in
  let i = skip 0 in
  String.sub line i (n - i)

(* [meta] begins a part when [use] follows it (macros.meta-use). *)
let starts_part line =
  List.exists (starts_with_word line) words
  || starts_with_word line "meta"
     &&
     let rest = String.sub line 4 (String.length line - 4) in
     let trimmed = after_blanks rest in
     trimmed <> rest && starts_with_word trimmed "use"

(* Whether [line] is a doc comment. A line that starts with another
   character, such as a form feed, holds a lexical error instead, so that
   reading never resumes before it. *)
let is_doc_line line = String.starts_with ~prefix:"///" (after_blanks line)

(* The text of a file by lines, and the offset where each starts. *)
type text = { text : string; lines : string array; starts : int array }

let split text =
  let lines = Array.of_list (String.split_on_char '\n' text) in
  let starts = Array.make (Array.length lines) 0 in
  for i = 1 to Array.length lines - 1 do
    starts.(i) <- starts.(i - 1) + String.length lines.(i - 1) + 1
  done;
  { text; lines; starts }

let line_text t n = t.lines.(n - 1)

(* The line where reading resumes after a part that breaks: the first line
   from [low] to [high] that starts with a word that begins a part, or the
   first of the doc comments just above it. *)
let resumption t ~low ~high =
  let rec find n =
    if n > high then None
    else if starts_part (line_text t n) then Some n
    else find (n + 1)
  in
  let rec docs n =
    if n > 1 && is_doc_line (line_text t (n - 1)) then docs (n - 1) else n
  in
  Option.map docs (find low)

let at (l : loc) = (l.line, l.col)

let before_until until (l : loc) =
  match until with None -> true | Some u -> at l < at u

let within ~from ~until (d : Diagnostic.t) =
  at from <= (d.line, d.col)
  && before_until until { line = d.line; col = d.col }

let earliest (a : Diagnostic.t) (b : Diagnostic.t) =
  if compare (a.line, a.col) (b.line, b.col) <= 0 then a else b

(* What has been read so far. *)
type acc = {
  mutable header : header node option;
  mutable items : item list list;
  mutable reports : report list;
  mutable extents : P.extent list;
  mutable comments : Lexer.comment list;
  mutable broken : loc list;
}

let loc_of (t : Lexer.token) = { line = t.line; col = t.col }

(* Reports the first syntax error of a part from [from] to [until]: [broke],
   if it breaks there, or the first error of its doc examples. *)
let report acc examples ~from ~until broke =
  match
    List.fold_left
      (fun found d ->
        if within ~from ~until d then
          Some (Option.fold ~none:d ~some:(earliest d) found)
        else found)
      broke examples
  with
  | Some error -> acc.reports <- { error; from; until } :: acc.reports
  | None -> ()

(* The first index from [lo] whose token is on line [line] or later. *)
let cut_at ts lo hi line =
  let rec go i =
    if i < hi && (ts.(i) : Lexer.token).line < line then go (i + 1) else i
  in
  go lo

(* Where the part [lo, hi) starts, and where the next part starts, if one does. *)
let bounds ts (error : Diagnostic.t option) (lo, hi) rest =
  let from =
    if lo < hi then loc_of ts.(lo)
    else
      (* A part with no token before its lexical error starts there. *)
      let d = Option.get error in
      { line = d.line; col = d.col }
  in
  let until =
    match rest with (l, _) :: _ -> Some (loc_of ts.(l)) | [] -> None
  in
  (from, until)

(* The lines where reading may resume after the part [lo, hi), which breaks at
   [d]: after the line its declaration starts on, and after a lexical error's
   own line, up to the part's last line. *)
let resumable t (ts : Lexer.token array) r (lo, hi) (d : Diagnostic.t) lexical =
  let start = if lo < hi then (P.declared_at r lo hi).line else d.line in
  let low = max (start + 1) (if lexical then d.line + 1 else d.line) in
  let high = if lexical then Array.length t.lines else ts.(hi - 1).line in
  (low, high)

let rec section ~file t acc line =
  let lexed, examples =
    Syntax.placed_with_examples ~line ~file
      (String.sub t.text
         t.starts.(line - 1)
         (String.length t.text - t.starts.(line - 1)))
  in
  let r = P.reader ~file lexed in
  let ts, hi = P.code lexed in
  let keep_until resume =
    acc.comments <-
      List.rev_append
        (List.filter
           (fun (c : Lexer.comment) ->
             before_until resume { line = c.line; col = c.col })
           lexed.comments)
        acc.comments;
    acc.broken <- List.rev_append (P.broken r) acc.broken
  in
  let rec walk first = function
    | [] -> keep_until None
    | (lo, hi) :: rest -> (
        let from, until = bounds ts lexed.error (lo, hi) rest in
        let declared items (lo, hi) =
          acc.items <- items :: acc.items;
          if lo < hi then acc.extents <- P.extent ts (lo, hi) :: acc.extents
        in
        match P.parse_alone r (lo, hi) with
        | Parsed m ->
            if first && line = 1 then acc.header <- m.header;
            declared m.items (lo, hi);
            report acc examples ~from ~until None;
            walk false rest
        | Breaks (d, lexical) -> (
            let low, high = resumable t ts r (lo, hi) d lexical in
            match resumption t ~low ~high with
            | Some resume ->
                let cut = cut_at ts lo hi resume in
                let until = Some { line = resume; col = 1 } in
                declared (P.declare_broken r (lo, cut) d) (lo, cut);
                report acc examples ~from ~until (Some d);
                keep_until until;
                section ~file t acc resume
            | None ->
                declared (P.declare_broken r (lo, hi) d) (lo, hi);
                report acc examples ~from ~until (Some d);
                walk false rest))
  in
  let parts =
    match P.cut ~starts:P.item_start ts 0 hi with
    | [] when Option.is_some lexed.error -> [ (0, 0) ]
    | parts -> parts
  in
  walk true parts

let unreadable (error : Diagnostic.t) =
  {
    module_ = { header = None; items = [] };
    broken = [];
    reports = [ { error; from = { line = 1; col = 1 }; until = None } ];
    extents = [];
    comments = [];
    unreadable = true;
  }

(* The parse of a file's normalized text, section by section. *)
let sections ~file text =
  let acc =
    {
      header = None;
      items = [];
      reports = [];
      extents = [];
      comments = [];
      broken = [];
    }
  in
  section ~file (split text) acc 1;
  {
    module_ = { header = acc.header; items = List.concat (List.rev acc.items) };
    broken = List.rev acc.broken;
    reports = List.rev acc.reports;
    extents = List.rev acc.extents;
    comments = List.rev acc.comments;
    unreadable = false;
  }

(* lexical.source-text and lexical.nesting: a file that breaks either is not
   parsed, and the breach is its only diagnostic. *)
let read ~file text =
  match Lexer_source.normalize ~line:1 ~col:1 text with
  | exception Lexer_source.Error { code; line; col; message } ->
      unreadable { Diagnostic.code; file; line; col; message }
  | text -> (
      match Lexer_nesting.too_deep ~file text with
      | Some error -> unreadable error
      | None -> sections ~file text)
