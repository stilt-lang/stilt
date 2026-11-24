(* Text beyond ASCII in a csmith program, made from a stream of its own, so
   that the rest of the program is the one the same seed makes without it.
   [main] binds strings of accented Latin, Greek, CJK, combining marks, emoji
   and characters outside the Basic Multilingual Plane, and prints what the
   methods of [str] (std.str and the paragraphs after it) and the functions of
   [std.text] (std.text) give for them: lengths in bytes and in scalar
   values, slices on the boundaries of characters, the characters, bytes and
   code points, searches for parts of the text, splits and replacements,
   comparisons by bytes (traits.prelude-impls), padding and format specs
   whose widths count scalar values (std.width-fill-and-alignment), case
   mappings and classes, and strings made from code points and from bytes,
   valid or not (std.code-points). Two functions walk a string's characters
   and its bytes. Nothing here can panic: every offset is on a boundary. *)

open Code
open Context

(* How likely a program is to use text beyond ASCII. *)
let using = 0.2

let wanted seed =
  Pick.chance (Pick.make (Hashtbl.hash (seed, "uses text"))) using

let print_of splices =
  line (Printf.sprintf "print(\"%s\")" (String.concat " " splices))

(* The functions that walk a string's characters and its bytes. Each program
   gives them a mark [k] of its own, so that the ten programs that
   [just differential] runs as one don't declare equal bodies, which W0302
   would report (docs.duplicate-bodies). *)
let helpers k =
  [
    block_lines "fn tx_wide(s: str) -> (i64, i64, List<i64>) {"
      (line "var wide = 0"
      @ line (Printf.sprintf "var seen = %d" k)
      @ line "var sizes: List<i64> = []"
      @ block_lines "for c in s.chars() {"
          (line "if c.len() > 1 { wide += 1 }"
          @ line "seen = seen *% 31 +% c.code_points()[0].to_i64()"
          @ line "sizes.push(c.len())")
          "}"
      @ line "(wide, seen, sizes)")
      "}";
    block_lines "fn tx_tails(s: str) -> i64 {"
      (line (Printf.sprintf "var n = %d" k)
      @ line "for b in s.bytes() { if b & 0xC0 == 0x80 { n += 1 } }"
      @ line "n")
      "}";
  ]

(* A text, the literal that writes it, and its variable. *)
type text = { t : Unicode.t; name : string }

let lit t = Unicode.literal t

(* A part of [s], from one boundary to another, which a search finds. *)
let part r s =
  let i, j = Unicode.span r s.t in
  Unicode.sub s.t i j

(* Lengths, the pieces of the text, and slices on its boundaries. *)
let pieces r s =
  let v = s.name in
  let i, j = Unicode.span r s.t in
  let a = Unicode.offset s.t i and z = Unicode.offset s.t j in
  [
    Printf.sprintf
      "{%s.len()} {%s.char_count()} {%s.is_empty()} {%s.is_ascii()}" v v v v;
    Printf.sprintf "{%s.chars()}" v;
    Printf.sprintf "{%s.bytes()}" v;
    Printf.sprintf "{%s.code_points()}" v;
    Printf.sprintf "{%s.reversed()} {[%s]}" v v;
    Printf.sprintf "{%s.slice(%d, %d)} {%s.chars().slice(%d, %d)}" v a z v i j;
    Printf.sprintf "{tx_wide(%s)} {tx_tails(%s)}" v v;
    Printf.sprintf "{%s.lines()} {%s.split_whitespace()} {%s.trim()}" v v v;
    Printf.sprintf "{\"%s\".join(%s.chars())}" (Unicode.fill r) v;
    Printf.sprintf "{%s.repeat(%d)}" v (Pick.between r (-1) 3);
  ]

(* Searches, splits and replacements, by parts of the text and by other
   text. *)
let searches r s other =
  let v = s.name in
  let needle () = lit (if Pick.chance r 0.8 then part r s else other) in
  let n = needle () in
  [
    Printf.sprintf "{%s.find(%s)} {%s.rfind(%s)} {%s.count(%s)}" v n v n v n;
    Printf.sprintf "{%s.contains(%s)} {%s.starts_with(%s)} {%s.ends_with(%s)}" v
      (needle ()) v (needle ()) v (needle ());
    Printf.sprintf "{%s.split(%s)}" v (needle ());
    Printf.sprintf "{%s.split_once(%s)} {%s.rsplit_once(%s)}" v (needle ()) v
      (needle ());
    Printf.sprintf "{%s.strip_prefix(%s)} {%s.strip_suffix(%s)}" v (needle ()) v
      (needle ());
    Printf.sprintf "{%s.replace(%s, %s)}" v (needle ()) (lit other);
    Printf.sprintf "{%s.replace_first(%s, %s)}" v (needle ()) (lit other);
  ]

(* Comparisons by bytes, padding and format specs that count scalar
   values. *)
let comparisons r s other =
  let v = s.name and o = lit other in
  let width () = Pick.between r 0 14 in
  let align = Pick.one r [ "<"; "^"; ">" ] in
  [
    Printf.sprintf "{%s < %s} {%s == %s} {%s >= %s}" v o v o o v;
    Printf.sprintf "{[%s, %s, %s].sorted()}" v o (lit (part r s));
    Printf.sprintf "{%s.eq_ignore_ascii_case(%s)}" v o;
    Printf.sprintf "{%s.pad_start(%d, %s)} {%s.pad_end(%d, %s)}" v (width ())
      (lit (Unicode.text r (Pick.between r 1 2)))
      v (width ())
      (lit (Unicode.text r (Pick.between r 1 2)));
    Printf.sprintf "[{%s:%s%s%d}]" v (Unicode.fill r) align (width ());
    Printf.sprintf "[{%s:%d}] [{%s:%s%d}]" v (width ()) v align (width ());
  ]

(* Case mappings and classes, of the whole text and of each character. *)
let classes r s =
  let v = s.name in
  let class_ () =
    Pick.one r
      [
        "is_letter";
        "is_upper";
        "is_lower";
        "is_numeric";
        "is_alphanumeric";
        "is_whitespace";
      ]
  in
  [
    Printf.sprintf "{text.upper(%s)} {text.lower(%s)}" v v;
    Printf.sprintf "{%s.ascii_upper()} {%s.ascii_lower()}" v v;
    Printf.sprintf "{text.%s(%s)} {text.%s(%s)}" (class_ ()) v (class_ ()) v;
    Printf.sprintf "{%s.chars().map(|c| text.%s(c))}" v (class_ ());
    Printf.sprintf "{%s.chars().filter(|c| text.%s(c))}" v (class_ ());
    Printf.sprintf "{%s.chars().map(|c| text.upper(c).char_count())}" v;
  ]

(* Strings made from code points and from bytes. *)
let made r s =
  let v = s.name in
  let point =
    Pick.one r
      [ 0x41; 0xE9; 0x65E5; 0x1F389; 0x10FFFF; 0xD800; 0xDFFF; 0x110000; 0 ]
  in
  let bytes = String.concat ", " (List.map string_of_int (Unicode.bytes r)) in
  [
    Printf.sprintf "{str.from_code_points(%s.code_points()) == Some(%s)}" v v;
    Printf.sprintf "{str.from_utf8(%s.bytes())}" v;
    Printf.sprintf "{str.from_code_point(%d)}" point;
    Printf.sprintf "{str.from_utf8([%s])} {str.from_utf8_lossy([%s])}" bytes
      bytes;
  ]

let round b =
  let r = b.p.r in
  let s = { t = Unicode.text r (Pick.between r 0 14); name = fresh b.p "tx" } in
  let other = Unicode.text r (Pick.between r 0 4) in
  let all =
    pieces r s @ searches r s other @ comparisons r s other @ classes r s
    @ made r s
  in
  let chosen = List.filter (fun _ -> Pick.chance r 0.4) all in
  line (Printf.sprintf "let %s = %s" s.name (lit s.t))
  @ List.concat_map (fun splice -> print_of [ splice ]) chosen

let uses p seed =
  let p = { p with r = Pick.make (Hashtbl.hash (seed, "text")) } in
  let b = { p; budget = 0; spent = 0 } in
  let rounds = Pick.times (Pick.between p.r 1 2) (fun () -> round b) in
  let tail = print_of [ "{text.unicode_version()}" ] in
  (helpers (Pick.between p.r 7 999_999), List.concat rounds @ tail)
