(* Fixed-size arrays, value parameters and staging annotations (generics.value-parameters and generics.arrays,
   meta.staging-annotations) in a csmith program, made from a stream of their own, so that the
   rest of the program is the one the same seed makes without them. The
   compiler stores an array inline, in a local, a record's field and a list's
   element, and the reference interpreter holds it as a value, so differential testing
   compares the two where they could differ: copies written after the copy,
   writes through [inout] and through a field or an element, generic code
   over the array's size, structural equality and [Show], and [comptime]
   forms, which run as the forms they annotate. Nothing here can panic: every
   index is a literal below the size. *)

open Code
open Context

(* How likely a program is to use arrays. *)
let using = 0.3

let wanted seed =
  Pick.chance (Pick.make (Hashtbl.hash (seed, "uses arrays"))) using

let typed t = Ty.to_string t
let array_ty t k = Printf.sprintf "array.Array<%s, %d>" (typed t) k

let print_of names =
  line
    (Printf.sprintf "print(\"%s\")"
       (String.concat " " (List.map (fun n -> "{" ^ n ^ "}") names)))

(* The generic functions every such program declares: one that reverses an
   array through writes to a copy, one that shows its size and last element
   through a [comptime if] chain, one that rotates it in place through an
   [inout] parameter and a [comptime for], and a ring of integers modulo a
   value parameter. Each program gives them a bound [k] above every size it
   writes, so that the ten programs that [just differential] runs as one
   don't declare equal bodies, which W0302 would report (docs.duplicate-bodies). *)
let helpers k =
  [
    block_lines
      "fn rev_a<T, n: i64>(a: array.Array<T, n>) -> array.Array<T, n> {"
      [
        (0, "var b = a");
        (0, Printf.sprintf "comptime if n < %d {" k);
        (1, "for i in 0..n / 2 {");
        (2, "let t = b[i]");
        (2, "b[i] = b[n - 1 - i]");
        (2, "b[n - 1 - i] = t");
        (1, "}");
        (0, "}");
        (0, "b");
      ]
      "}";
    block_lines "fn count_a<T: Show, n: i64>(a: array.Array<T, n>) -> str {"
      [
        ( 0,
          Printf.sprintf
            "comptime if n == 0 { \"none\" } else if n == 1 { \"one {a[0]}\" } \
             else if n < %d { \"{n}: {a[n - 1]}\" } else { \"many\" }"
            k );
      ]
      "}";
    block_lines "fn rotate_a<T, n: i64>(inout a: array.Array<T, n>) {"
      [
        (0, Printf.sprintf "comptime if n > 1 && n < %d {" k);
        (1, "let first = a[0]");
        (1, "comptime for i in 1..n { a[i - 1] = a[i] }");
        (1, "a[n - 1] = first");
        (0, "}");
      ]
      "}";
    line "type Ring<m: i64> = { v: i64 }";
    line
      "fn ring_add<m: i64>(a: Ring<m>, b: Ring<m>) -> Ring<m> { Ring { v: (a.v \
       + b.v) % m } }";
  ]

let value b sc t = (Expr.expr b sc ~depth:2 ~known:false t).text
let values b sc t k = String.concat ", " (Pick.times k (fun () -> value b sc t))

(* An array literal of [k] elements of type [t], bound to a new name, which
   the generic functions read, copy, rotate and compare. *)
let made b sc t k =
  let a = fresh b.p "arr" and c = fresh b.p "brr" in
  let r = b.p.r in
  let write =
    if k = 0 then []
    else
      line
        (Printf.sprintf "%s[%d] = %s" c
           (Pick.between r 0 (k - 1))
           (value b sc t))
  in
  ( a,
    c,
    line (Printf.sprintf "let %s: %s = [%s]" a (array_ty t k) (values b sc t k))
    @ line (Printf.sprintf "var %s = %s" c a)
    @ write
    @ line (Printf.sprintf "rotate_a(inout %s)" c)
    @ print_of [ a; c; "rev_a(" ^ c ^ ")"; "count_a(" ^ c ^ ")" ]
    @ print_of [ a ^ " == " ^ c; a ^ ".len()"; c ^ ".to_list()" ] )

(* The elements of [c] read by a [for], a [comptime for] and a list
   pattern. *)
let read b c k =
  let acc = fresh b.p "acc" and seen = fresh b.p "acc" in
  let pattern =
    if k < 2 then []
    else
      let x = fresh b.p "elt" and y = fresh b.p "elt" in
      line (Printf.sprintf "let [%s, %s, ..] = %s" x y c) @ print_of [ x; y ]
  in
  line (Printf.sprintf "var %s: List<str> = []" acc)
  @ line (Printf.sprintf "for x in %s { %s.push(\"{x}\") }" c acc)
  @ line (Printf.sprintf "var %s: List<str> = []" seen)
  @ line
      (Printf.sprintf "comptime for i in 0..%d { %s.push(\"{i}={%s[i]}\") }" k
         seen c)
  @ print_of [ acc; seen ]
  @ pattern

(* [c] kept in a list and in a record, each written through after the copy,
   which leaves [c] as it was. *)
let kept b sc t k c ~hold =
  let l = fresh b.p "lst" and h = fresh b.p "hld" in
  let r = b.p.r in
  let writes =
    if k = 0 then []
    else
      let i = Pick.between r 0 (k - 1) and j = Pick.between r 0 (k - 1) in
      line (Printf.sprintf "%s[1][%d] = %s" l i (value b sc t))
      @ line (Printf.sprintf "%s.items[%d] = %s" h j (value b sc t))
  in
  line (Printf.sprintf "var %s: List<%s> = [%s, %s]" l (array_ty t k) c c)
  @ line (Printf.sprintf "var %s = %s { items: %s, tag: %d }" h hold c k)
  @ writes
  @ print_of [ l; h; c ]

(* [fill], [from_list] and [map] of std.array. *)
let library b sc t k c =
  let f = fresh b.p "arr" and o = fresh b.p "arr" and m = fresh b.p "arr" in
  let r = b.p.r in
  let u = random_ty b.p ~maps:false 1 in
  let x = { name = fresh b.p "x"; ty = t; mutable_ = false } in
  let mapped =
    (Expr.expr b (closure_scope sc [ x ]) ~depth:2 ~known:true u).text
  in
  let n = if Pick.chance r 0.7 then k else k + 1 in
  line
    (Printf.sprintf "let %s: %s = array.fill(%s)" f (array_ty t k)
       (value b sc t))
  @ line
      (Printf.sprintf "let %s: Option<%s> = array.from_list([%s])" o
         (array_ty t k) (values b sc t n))
  @ line
      (Printf.sprintf "let %s: %s = %s.map(|%s| %s)" m (array_ty u k) c x.name
         mapped)
  @ print_of [ f; o; m ]

(* One round: an array of a random type and size, and what is done with it.
   Its record type for [kept] is an item of its own. *)
let round b sc =
  let r = b.p.r in
  let t = random_ty b.p ~maps:false 1 in
  let k =
    Pick.run r
      [ (1, fun () -> 0); (2, fun () -> 1); (6, fun () -> Pick.between r 2 6) ]
  in
  let hold = fresh b.p "Hold" in
  let item =
    line
      (Printf.sprintf "type %s = { items: %s, tag: i64 }" hold (array_ty t k))
  in
  let _, c, lines = made b sc t k in
  (item, lines @ read b c k @ kept b sc t k c ~hold @ library b sc t k c)

(* Two rings of one modulus, added. *)
let rings b =
  let r = b.p.r in
  let m = Pick.between r 2 97 in
  let x = fresh b.p "rng" and y = fresh b.p "rng" in
  let v () = Pick.between r 0 (m - 1) in
  line (Printf.sprintf "let %s: Ring<%d> = Ring { v: %d }" x m (v ()))
  @ line (Printf.sprintf "let %s: Ring<%d> = Ring { v: %d }" y m (v ()))
  @ print_of [ Printf.sprintf "ring_add(%s, %s).v" x y ]

let uses p sc seed =
  let p = { p with r = Pick.make (Hashtbl.hash (seed, "arrays")) } in
  let b = { p; budget = 4_000; spent = 0 } in
  let sc = { sc with weight = 1 } in
  let rounds = Pick.times (Pick.between p.r 1 3) (fun () -> round b sc) in
  let ring = rings b in
  let k = Pick.mark p.r seed in
  (helpers k @ List.map fst rounds, List.concat_map snd rounds @ ring)
