(* Reflection (meta.shapes and meta.reflects) in a csmith program, made from a stream of its own, so
   that the rest of the program is the one the same seed makes without it.
   The compiler reads a type's shape from a descriptor passed at run time and
   the reference interpreter from the type it instantiates, so differential testing compares
   the two where they could differ: every case of a shape and its accessors,
   fields and cases iterated by [comptime for], values made again by
   [fields.build] and [make], a type's name, and bound tests, true for the
   types that implement the program's trait and false for the others. Nothing
   here can panic. *)

open Code
open Context

(* How likely a program is to use reflection. *)
let using = 0.3

let wanted seed =
  Pick.chance (Pick.make (Hashtbl.hash (seed, "uses reflection"))) using

let print_of names =
  line
    (Printf.sprintf "print(\"%s\")"
       (String.concat " " (List.map (fun n -> "{" ^ n ^ "}") names)))

(* A function that writes a value through its shape, case by case. Each
   program gives its texts a mark [k] of its own, so that the ten programs
   that [just differential] runs as one don't declare equal bodies, which
   W0302 would report (docs.duplicate-bodies). *)
let show_r k =
  block_lines "fn show_r<T>(value: T) -> str {"
    [
      (0, "comptime match T.shape() {");
      (1, "Int(n) => n.text(value)");
      (1, "Float(x) => \"{x.get(value)}\"");
      (1, "Bool(b) => \"{b.get(value)}\"");
      (1, "Str(s) => \"'{s.get(value)}'\"");
      (1, "Unit(_) => \"()\"");
      ( 1,
        "Option(o) => match o.get(value) { Some(x) => \"some {show_r(x)}\", \
         None => \"none\" }" );
      (1, "List(l) => \"[{show_all(l.get(value))}]\"");
      (1, "Set(l) => \"set[{show_all(l.get(value))}]\"");
      (1, "Map(m) => \"map[{show_all(m.get(value))}]\"");
      (1, "Array(a) => \"arr[{show_all(a.get(value))}]\"");
      (1, "Tuple(fields) => {");
      (2, "var parts: List<str> = []");
      (2, "comptime for f in fields { parts.push(show_r(f.get(value))) }");
      (2, "\"({\", \".join(parts)})\"");
      (1, "}");
      (1, "Record(fields) => {");
      (2, "var parts: List<str> = []");
      ( 2,
        Printf.sprintf
          "comptime for f in fields { \
           parts.push(\"{f.index()}:{f.name()}%d={show_r(f.get(value))}\") }"
          k );
      (2, "\"\\{{\", \".join(parts)}}\"");
      (1, "}");
      (1, "Variants(cases) => {");
      (2, "var shown = \"\"");
      ( 2,
        "comptime for c in cases { if let Some(p) = c.get(value) { shown = \
         \"{c.name()}#{c.index()}{show_r(p)}\" } }" );
      (2, "shown");
      (1, "}");
      (0, "}");
    ]
    "}"

(* The elements of a list, each written by [show_r]. *)
let show_all k =
  block_lines "fn show_all<E>(xs: List<E>) -> str {"
    [
      (0, "var parts: List<str> = []");
      (0, "for x in xs { parts.push(show_r(x)) }");
      (0, Printf.sprintf "\"%d:{\", \".join(parts)}\"" k);
    ]
    "}"

(* A function that makes a value again from its parts, through
   [fields.build] and [make], which gives back an equal value; [k] stands
   where it changes nothing. *)
let copy_r k =
  block_lines "fn copy_r<T>(value: T) -> T {"
    [
      (0, "comptime match T.shape() {");
      (1, "Record(fields) => fields.build(|f| copy_r(f.get(value)))");
      (1, "Tuple(fields) => fields.build(|f| copy_r(f.get(value)))");
      (1, "Variants(cases) => {");
      (2, "var out = value");
      ( 2,
        "comptime for c in cases { if let Some(p) = c.get(value) { out = \
         c.make(copy_r(p)) } }" );
      (2, "out");
      (1, "}");
      (1, "List(l) => l.make(copy_all(l.get(value)))");
      (1, "Set(l) => l.make(copy_all(l.get(value)))");
      (1, "Map(m) => m.make(copy_all(m.get(value)))");
      ( 1,
        "Option(o) => match o.get(value) { Some(x) => o.make(Some(copy_r(x))), \
         None => value }" );
      ( 1,
        "Int(n) => match n.parse(n.text(value)) { Some(m) => m, None => value }"
      );
      (1, Printf.sprintf "Bool(b) => b.make(b.get(value) || %d < 0)" k);
      (1, "_ => value");
      (0, "}");
    ]
    "}"

let copy_all k =
  block_lines "fn copy_all<E>(xs: List<E>) -> List<E> {"
    [
      (0, "var out: List<E> = []");
      (0, "for x in xs { out.push(copy_r(x)) }");
      (0, Printf.sprintf "if out.len() < %d { out } else { xs }" (k + 1_000_000));
    ]
    "}"

(* A trait that some of the program's types implement, which a bound test
   finds, with and without [comptime]. *)
let tagged k =
  [
    line "trait Tagged { fn tag(self) -> str }";
    block_lines "fn tag_r<T>(value: T) -> str {"
      [
        (0, "let first = if T: Tagged { value.tag() } else { \"untagged\" }");
        ( 0,
          Printf.sprintf
            "let second = comptime if T: Tagged { \"%d\" } else { \"-\" }" k );
        (0, "\"{first} {second}\"");
      ]
      "}";
    line "fn name_r<T>(value: T) -> str { T.name() }";
  ]

let impls p k =
  List.filter_map
    (fun (name, _) ->
      if Pick.chance p.r 0.5 then
        Some
          (line
             (Printf.sprintf
                "impl Tagged for %s { fn tag(self) -> str { \"%s %d\" } }" name
                name k))
      else None)
    p.decls

(* A value of a random type, written, made again and named. *)
let reflect b sc =
  let t = random_ty b.p ~maps:true 2 in
  let x = fresh b.p "rfl" in
  let value = (Expr.expr b sc ~depth:2 ~known:false t).text in
  line (Printf.sprintf "let %s: %s = %s" x (Ty.to_string t) value)
  @ print_of [ "show_r(" ^ x ^ ")"; "name_r(" ^ x ^ ")" ]
  @ print_of [ "show_r(copy_r(" ^ x ^ "))"; "copy_r(" ^ x ^ ")" ]
  @ print_of [ "tag_r(" ^ x ^ ")" ]

let uses p sc seed =
  let p = { p with r = Pick.make (Hashtbl.hash (seed, "reflection")) } in
  let b = { p; budget = 4_000; spent = 0 } in
  let sc = { sc with weight = 1 } in
  let lines =
    List.concat (Pick.times (Pick.between p.r 2 4) (fun () -> reflect b sc))
  in
  let k = Pick.between p.r 7 999_999 in
  let items =
    [ show_r k; show_all k; copy_r k; copy_all k ] @ tagged k @ impls p k
  in
  (items, lines)
