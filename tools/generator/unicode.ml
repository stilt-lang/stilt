(* Text beyond ASCII: accented Latin, Greek, Cyrillic, CJK, digits of other
   scripts, combining marks, emoji and characters outside the Basic
   Multilingual Plane, each written as itself or as a [\u{…}] escape
   (lexical.escapes). The generator knows each text's scalar values, so it
   can name the byte offsets on their boundaries, where [slice] and
   [View.of] don't panic (std.str; views.making-view). *)

(* A scalar value, with the text a literal writes it as. *)
type scalar = { utf8 : string; source : string }
type t = scalar list

let encode cp =
  let b = Buffer.create 4 in
  Buffer.add_utf_8_uchar b (Uchar.of_int cp);
  Buffer.contents b

(* Letters, digits and punctuation that a literal writes as they are, with
   none of the characters an escape or a splice starts with. *)
let ascii =
  List.init 26 (fun i -> 97 + i)
  @ [ 65; 75; 81; 90; 48; 55; 57; 32; 32; 44; 46; 45; 33; 63 ]

(* Each group holds characters whose case, class or width the Reference's
   functions treat apart: [ß], [ŉ], [ǅ], [ﬁ] and [ΐ] map to several scalar
   values or to a title case, [İ] lowers to two, [ς] is a final sigma, the
   digits are of category N outside ASCII, and the emoji, the Deseret,
   Adlam and Gothic letters and the mathematical letters lie outside the
   Basic Multilingual Plane. *)
let latin =
  [ 0xE9; 0xFC; 0xDF; 0xC7; 0xF1; 0xC5; 0xF8; 0xE6; 0x1E9E; 0x130; 0x131 ]
  @ [ 0x17F; 0x149; 0x1C4; 0x1C5; 0x1C6; 0xFB01; 0xFB00 ]

let greek_cyrillic =
  [ 0x3A3; 0x3C3; 0x3C2; 0x3B1; 0x3A9; 0x3AC; 0x390; 0x436; 0x416; 0x44F ]
  @ [ 0x531; 0x587; 0x13A0; 0xAB70 ]

let cjk = [ 0x65E5; 0x672C; 0x8A9E; 0x6F22; 0x3042; 0xD55C; 0x30AB ]
let numeric = [ 0x663; 0x216B; 0x2177; 0xBD; 0x1D7D8; 0xFF15 ]
let combining = [ 0x301; 0x308; 0x307; 0x20DD ]
let emoji = [ 0x1F389; 0x1F44D; 0x1F3FD; 0x1F600; 0x200D; 0x2764; 0xFE0F ]
let astral = [ 0x10348; 0x1D538; 0x10400; 0x10428; 0x1E900; 0x1E922 ]
let spaces = [ 0xA0; 0x3000; 0x2003; 0x2028 ]

(* Characters that a literal always escapes, since an editor would hide
   them. *)
let hidden = [ 0x200D; 0xFE0F; 0x2028; 0xA0; 0x2003 ]

let scalar r cp =
  let escaped = List.mem cp hidden || (cp >= 0x80 && Pick.chance r 0.15) in
  let utf8 = encode cp in
  { utf8; source = (if escaped then Printf.sprintf "\\u{%x}" cp else utf8) }

let code_point r =
  Pick.run r
    [
      (8, fun () -> Pick.one r ascii);
      (4, fun () -> Pick.one r latin);
      (3, fun () -> Pick.one r greek_cyrillic);
      (3, fun () -> Pick.one r cjk);
      (2, fun () -> Pick.one r numeric);
      (2, fun () -> Pick.one r combining);
      (2, fun () -> Pick.one r emoji);
      (2, fun () -> Pick.one r astral);
      (1, fun () -> Pick.one r spaces);
      (1, fun () -> Pick.one r [ 9; 10 ]);
    ]

let text r n = Pick.times n (fun () -> scalar r (code_point r))

(* One character fit to be a format spec's fill: a letter or a symbol written
   as itself (lexical.format-specs). *)
let fill r =
  encode (Pick.one r ([ 42; 46; 95 ] @ latin @ cjk @ astral @ [ 0x1F389 ]))

let literal t =
  "\""
  ^ String.concat ""
      (List.map
         (fun s ->
           match s.utf8 with "\t" -> "\\t" | "\n" -> "\\n" | _ -> s.source)
         t)
  ^ "\""

let length t = List.fold_left (fun n s -> n + String.length s.utf8) 0 t

(* The byte offset of the boundary before the [i]th scalar value. *)
let offset t i = length (List.filteri (fun j _ -> j < i) t)

(* The scalar values from the [i]th up to the [j]th. *)
let sub t i j = List.filteri (fun k _ -> k >= i && k < j) t

(* Two boundaries, in order, as scalar indices. *)
let span r t =
  let n = List.length t in
  let a = Pick.between r 0 n in
  (a, Pick.between r a n)

(* Bytes for [str.from_utf8_lossy]: valid sequences, lone continuation bytes,
   truncated sequences, overlong forms, surrogates and values above
   [0x10FFFF] (std.code-points). *)
let bytes r =
  let piece () =
    Pick.one r
      [
        [ 0x41 ];
        [ 0xC3; 0xA9 ];
        [ 0xE6; 0x97; 0xA5 ];
        [ 0xF0; 0x9F; 0x8E; 0x89 ];
        [ 0x80 ];
        [ 0xBF ];
        [ 0xC3 ];
        [ 0xE6; 0x97 ];
        [ 0xF0; 0x9F; 0x8E ];
        [ 0xC0; 0xAF ];
        [ 0xE0; 0x80; 0xAF ];
        [ 0xED; 0xA0; 0x80 ];
        [ 0xF4; 0x90; 0x80; 0x80 ];
        [ 0xF5 ];
        [ 0xFF ];
      ]
  in
  List.concat (Pick.times (Pick.between r 0 6) piece)
