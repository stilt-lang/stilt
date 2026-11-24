(* A trait, its impls and generic functions bounded by it (traits.impl-blocks,
   traits.bounds) in a csmith program, made from a stream of their own, so
   that the rest of the program is the one the same seed makes without them.
   The trait has one method, [weight], whose impls for two or three of the
   program's types are drawn like any other code, with [self] in scope; two
   generic functions call it, on each element of a list and on two values,
   and [main] calls them at each type. The debug build passes the impl at run
   time and the release build compiles each function once for each type
   (builds.specialization), so differential testing compares both with the
   reference interpreter's dispatch. *)

open Code
open Context

(* How likely a program is to declare the trait. *)
let using = 0.3

let wanted seed =
  Pick.chance (Pick.make (Hashtbl.hash (seed, "uses generics"))) using

(* The scope of a method's body, whose one variable is [self], of type [t]. *)
let method_scope t =
  {
    vars = [ { name = "self"; ty = t; mutable_ = false } ];
    frozen = [];
    loop = false;
    may_raise = false;
    io = false;
    returns = None;
    weight = 1;
  }

(* Two or three of the types the program can name, each once: [i64], [str] and
   [bool], and the records and variant types it declares. *)
let impl_types p =
  let declared = List.map (fun (name, _) -> Ty.Named name) p.decls in
  let all = [ Ty.Int Ty.I64; Ty.Str; Ty.Bool ] @ declared in
  let rec pick n left =
    if n = 0 || left = [] then []
    else
      let t = Pick.one p.r left in
      t :: pick (n - 1) (List.filter (( <> ) t) left)
  in
  pick (Pick.between p.r 2 3) all

(* The impl of the trait for [t]: [weight]'s body drawn with [self] in scope,
   plus the program's mark [k], so that the ten programs that
   [just differential] runs as one don't declare equal bodies, which W0302
   would report (docs.duplicate-bodies). *)
let impl b t k =
  let body =
    (Expr.expr b (method_scope t) ~depth:3 ~known:true (Ty.Int Ty.I64)).text
  in
  block_lines
    (Printf.sprintf "impl Weigh for %s {" (Ty.to_string t))
    (block_lines "fn weight(self) -> i64 {"
       (line (Printf.sprintf "(%s) +%% %d" body k))
       "}")
    "}"

(* The trait and the generic functions that call it. *)
let generic k =
  [
    block_lines "trait Weigh {" (line "fn weight(self) -> i64") "}";
    block_lines "fn weigh_all<T: Weigh>(xs: List<T>) -> i64 {"
      (line (Printf.sprintf "var total = %d" k)
      @ block_lines "for x in xs {" (line "total = total +% x.weight()") "}"
      @ line "total")
      "}";
    block_lines "fn heavier<T: Weigh>(a: T, b: T) -> T {"
      (line "if a.weight() >= b.weight() { a } else { b }")
      "}";
  ]

(* The lines of [main] that call the generic functions at [t]: on a list of
   up to three values of [t], and on two. *)
let calls b sc t =
  let r = b.p.r in
  let value () = (Expr.expr b sc ~depth:2 ~known:true t).text in
  let xs = Pick.times (Pick.between r 0 3) value in
  let list = Printf.sprintf "[%s]" (String.concat ", " xs) in
  let typed = Ty.to_string t in
  line (Printf.sprintf "let gs: List<%s> = %s" typed list)
  @ line "print(\"weigh_all {weigh_all(gs)}\")"
  @ line
      (Printf.sprintf "print(\"heavier {heavier(%s, %s).weight()}\")" (value ())
         (value ()))

let uses p sc seed =
  let p = { p with r = Pick.make (Hashtbl.hash (seed, "generics")) } in
  let b = { p; budget = 2_000; spent = 0 } in
  let k = Pick.between p.r 1 999 in
  let types = impl_types p in
  let impls = List.map (fun t -> impl b t k) types in
  let main =
    List.concat_map (fun t -> block_lines "{" (calls b sc t) "}") types
  in
  (generic k @ impls, main)
