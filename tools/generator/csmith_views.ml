(* Views (views.what-view-is) in a csmith program, made from a stream of their
   own, so that the rest of the program is the one the same seed makes
   without them. A record holds a list, a string and a list of strings, and
   another record holds it and a list of it; [main] views their fields, and
   views those views, reads through each, by index, [view.get], [for] and
   iterators, compares them with each other and with copies of their parts,
   and passes them to functions that return views of their parameters
   (views.across-calls). It then writes through writable views of the fields
   (projections.writable-views), of a view and of [view.split]'s parts, and
   reads the records back, beside a copy made before the writes, which keeps
   what it held. Every offset lies inside its source and on the boundary of a
   character, so nothing panics. *)

open Code
open Context

(* How likely a program is to view the fields of records. *)
let using = 0.2

let wanted seed =
  Pick.chance (Pick.make (Hashtbl.hash (seed, "uses views"))) using

let typed t = Ty.to_string t
let list_of t = "view.View<List<" ^ typed t ^ ">>"

let print_of splices =
  line (Printf.sprintf "print(\"%s\")" (String.concat " " splices))

(* The record types and the functions on views of their fields. Each
   program gives them a mark [k] of its own, so that the ten programs that
   [just differential] runs as one don't declare equal bodies, which W0302
   would report (docs.duplicate-bodies). *)
let helpers t k =
  let l = typed t and v = list_of t in
  [
    line
      (Printf.sprintf
         "type VwBag = { label: str, items: List<%s>, words: List<str>, n: i64 \
          }"
         l);
    line "type VwRack = { top: VwBag, rows: List<VwBag> }";
    block_lines
      (Printf.sprintf "fn vw_part(xs: List<%s>, a: i64, b: i64) -> %s {" l v)
      (line "let s = a.max(0).min(xs.len())"
      @ line
          (Printf.sprintf
             "view.View.of(xs, s, (s + b.max(0).min(%d)).min(xs.len()))" k))
      "}";
    block_lines
      (Printf.sprintf "fn vw_some(xs: List<%s>, n: i64) -> Option<%s> {" l v)
      (line
         (Printf.sprintf
            "if n >= 0 && n <= xs.len() && n < %d { Some(view.View.of(xs, 0, \
             n)) } else { None }"
            k))
      "}";
    block_lines
      (Printf.sprintf "fn vw_pass(w: %s, a: i64) -> %s {" v v)
      (line (Printf.sprintf "w.view(a.max(0).min(w.len()).min(%d), w.len())" k))
      "}";
    block_lines
      (Printf.sprintf "fn vw_fill(inout w: %s, x: %s) {" v l)
      (line
         (Printf.sprintf
            "for i in 0..w.len() { if (i + %d) %% 2 == 1 { w[i] = x } }" k))
      "}";
    block_lines
      (Printf.sprintf "fn vw_shown(w: %s) -> str {" v)
      (line
         (Printf.sprintf
            "view.Iter.of_view(w).fold(\"%d\", |acc, x| \"{acc}/{x}\")" k))
      "}";
    block_lines "fn vw_head(s: str, n: i64) -> view.View<str> {"
      (line "var at = 0" @ line "var i = 0"
      @ line
          (Printf.sprintf
             "for c in s.chars() { if i < n && i < %d { at += c.len() }; i += \
              1 }"
             k)
      @ line "view.View.of(s, 0, at)")
      "}";
  ]

(* A value of the elements' type: for strings, sometimes text beyond
   ASCII. *)
let value b sc t =
  let r = b.p.r in
  if t = Ty.Str && Pick.chance r 0.4 then
    Unicode.literal (Unicode.text r (Pick.between r 0 5))
  else (Expr.expr b sc ~depth:2 ~known:false t).text

let values b sc t n = String.concat ", " (Pick.times n (fun () -> value b sc t))

let words r n =
  String.concat ", "
    (Pick.times n (fun () ->
         Unicode.literal (Unicode.text r (Pick.between r 0 4))))

(* Two offsets in order, from 0 to [n]. *)
let range r n =
  let a = Pick.between r 0 n in
  (a, Pick.between r a n)

type bag = {
  bag : string;  (** The record's variable. *)
  rack : string;  (** The record that holds it. *)
  kept : string;  (** A copy made before the writes. *)
  len : int;  (** The length of its list. *)
  label : Unicode.t;
  count : int;  (** The length of its list of words. *)
}

(* The lines that bind a record of each type, and a copy of the first. *)
let made b sc t =
  let r = b.p.r in
  let len = Pick.between r 0 7 and count = Pick.between r 1 4 in
  let label = Unicode.text r (Pick.between r 0 10) in
  let g =
    {
      bag = fresh b.p "vw";
      rack = fresh b.p "vr";
      kept = fresh b.p "vk";
      len;
      label;
      count;
    }
  in
  ( g,
    line
      (Printf.sprintf
         "var %s = VwBag { label: %s, items: [%s], words: [%s], n: %d }" g.bag
         (Unicode.literal label) (values b sc t len) (words r count) len)
    @ line
        (Printf.sprintf "var %s = VwRack { top: %s, rows: [%s, %s] }" g.rack
           g.bag g.bag g.bag)
    @ line (Printf.sprintf "let %s = %s" g.kept g.bag) )

(* Reads through views of the list field and of a view of it. *)
let list_reads b g =
  let r = b.p.r in
  let va = fresh b.p "va" and vb = fresh b.p "vb" and seen = fresh b.p "vs" in
  let a, z = range r g.len in
  let c, d = range r (z - a) in
  let index n =
    if n = 0 then [] else [ Printf.sprintf "{%s[%d]}" va (Pick.below r n) ]
  in
  let arg () = string_of_int (Pick.between r (-2) (g.len + 2)) in
  line (Printf.sprintf "let %s = view.View.of(%s.items, %d, %d)" va g.bag a z)
  @ line (Printf.sprintf "let %s = %s.view(%d, %d)" vb va c d)
  @ print_of
      ([
         "{" ^ va ^ "}";
         "{" ^ vb ^ "}";
         Printf.sprintf "{%s.len()} {%s.is_empty()}" va vb;
         Printf.sprintf "{%s < %s} {%s == %s} {%s >= %s}" va vb va vb vb va;
         Printf.sprintf "{%s.copy() == %s.items.slice(%d, %d)}" va g.bag a z;
         Printf.sprintf "{view.get(%s, %s)}" vb (arg ());
       ]
      @ index (z - a))
  @ print_of
      [
        Printf.sprintf "{vw_part(%s.items, %s, %s)}" g.bag (arg ()) (arg ());
        Printf.sprintf "{vw_some(%s.items, %s)}" g.bag (arg ());
        Printf.sprintf "{vw_pass(%s, %s)}" va (arg ());
        Printf.sprintf "{vw_pass(vw_part(%s.items, %s, %s), %s)}" g.bag (arg ())
          (arg ()) (arg ());
        Printf.sprintf "{vw_shown(%s)}" vb;
      ]
  @ line (Printf.sprintf "var %s: List<str> = []" seen)
  @ line (Printf.sprintf "for x in %s { %s.push(\"{x}\") }" vb seen)
  @ print_of
      [
        "{" ^ seen ^ "}";
        Printf.sprintf "{view.Iter.of_view(%s).enumerate(%d).collect()}" va
          (Pick.between r 0 2);
        Printf.sprintf
          "{view.Iter.of_view(%s).max()} {view.Iter.of_view(%s).min()}" va vb;
        Printf.sprintf "{view.Iter.of_view(%s).count()}" vb;
      ]

(* Reads through views of the string field, on the boundaries of its
   characters, and of the list of words. *)
let text_reads b g =
  let r = b.p.r in
  let vl = fresh b.p "vl" and vt = fresh b.p "vt" in
  let i, j = Unicode.span r g.label in
  let part = Unicode.sub g.label i j in
  let other = Unicode.text r (Pick.between r 0 3) in
  let a, z = range r g.count in
  line
    (Printf.sprintf "let %s = view.View.of(%s.label, %d, %d)" vl g.bag
       (Unicode.offset g.label i) (Unicode.offset g.label j))
  @ line (Printf.sprintf "let %s = view.View.of(%s.words, %d, %d)" vt g.bag a z)
  @ print_of
      [
        Printf.sprintf "{%s} {[%s.copy()]} {%s.len()}" vl vl vl;
        Printf.sprintf "{view.chars(%s).collect()} {view.bytes(%s).count()}" vl
          vl;
        Printf.sprintf "{%s == view.View.all(%s)} {%s.copy() == %s}" vl
          (Unicode.literal part) vl (Unicode.literal part);
        Printf.sprintf "{%s < view.View.all(%s)}" vl (Unicode.literal other);
        Printf.sprintf "{vw_head(%s.label, %d)}" g.bag (Pick.between r 0 6);
      ]
  @ print_of
      [
        Printf.sprintf "{%s} {view.get(%s, %d)}" vt vt (Pick.between r 0 3);
        Printf.sprintf "{view.Iter.of_view(%s).map(|w| w.len()).collect()}" vt;
        Printf.sprintf "{view.Iter.of_view(%s).max()}" vt;
      ]

(* Reads through a view of a field of a record in a list in a record. *)
let nested_reads b g =
  let r = b.p.r in
  let vn = fresh b.p "vn" in
  let a, z = range r g.len in
  line
    (Printf.sprintf "let %s = view.View.of(%s.rows[%d].items, %d, %d)" vn g.rack
       (Pick.below r 2) a z)
  @ print_of
      [
        "{" ^ vn ^ "}";
        Printf.sprintf "{view.View.all(%s.top.words).view(0, %d)}" g.rack
          (Pick.between r 0 g.count);
        Printf.sprintf
          "{view.Iter.of_view(%s).zip(view.Iter.of_view(view.View.all(%s.top.words))).collect()}"
          vn g.rack;
      ]

(* Writes through a writable view of [place], of length [len], and through
   a writable view of that view. *)
let writes b sc t place len =
  let r = b.p.r in
  let w = fresh b.p "vw" and p = fresh b.p "vp" in
  let a, z = range r len in
  let c, d = range r (z - a) in
  let store v n =
    if n = 0 then []
    else line (Printf.sprintf "%s[%d] = %s" v (Pick.below r n) (value b sc t))
  in
  block_lines "{"
    (line (Printf.sprintf "var %s = view.into(inout %s, %d, %d)" w place a z)
    @ store w (z - a)
    @ (if Pick.chance r 0.6 then
         line (Printf.sprintf "vw_fill(inout %s, %s)" w (value b sc t))
       else [])
    @ line (Printf.sprintf "var %s = view.part(inout %s, %d, %d)" p w c d)
    @ store p (d - c))
    "}"

(* [view.split] of the list of words, whose closure writes both parts. *)
let split b g =
  let r = b.p.r in
  let word () = Unicode.literal (Unicode.text r (Pick.between r 0 3)) in
  line
    (Printf.sprintf
       "view.split(inout %s.words, %d, |inout x, inout y| { if x.len() > 0 { \
        x[0] = %s }; if y.len() > 0 { y[y.len() - 1] = %s } })"
       g.bag (Pick.between r 0 g.count) (word ()) (word ()))

let round b sc t =
  let g, lines = made b sc t in
  let r = b.p.r in
  lines
  @ block_lines "{" (list_reads b g @ text_reads b g @ nested_reads b g) "}"
  @ writes b sc t (g.bag ^ ".items") g.len
  @ (if Pick.chance r 0.5 then
       writes b sc t
         (Printf.sprintf "%s.rows[%d].items" g.rack (Pick.below r 2))
         g.len
     else [])
  @ split b g
  @ print_of
      [
        Printf.sprintf "{%s.items} {%s.words}" g.bag g.bag;
        Printf.sprintf "{%s.items} {%s.words}" g.kept g.kept;
        Printf.sprintf "{%s.rows} {%s.top == %s}" g.rack g.rack g.kept;
      ]

let uses p sc seed =
  let p = { p with r = Pick.make (Hashtbl.hash (seed, "views")) } in
  let b = { p; budget = 4_000; spent = 0 } in
  let sc = { sc with weight = 1 } in
  let t = leaf_ty p.r in
  let helpers = helpers t (Pick.mark p.r seed) in
  ( helpers,
    List.concat
      (Pick.times
         (if Pick.chance p.r 0.25 then 2 else 1)
         (fun () -> round b sc t)) )
