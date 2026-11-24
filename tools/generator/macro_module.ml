(* The module of procedural macros (macros.procedural-declarations and macros.procedural-bodies) of a csmith program: its helpers,
   the macros that read tokens with a cursor, the pattern macros, and those of
   Macro_kinds, from a stream of their own. Every module declares a macro of
   the kinds that Macro_mistakes plants mistakes in, and some of the others.
   Each module marks its fixed functions and macros with a number [k] of its
   own, so that the ten programs that [just differential] runs as one declare
   no equal bodies, which W0302 would report (docs.duplicate-bodies). *)

open Code
open Context
open Macro_kinds

let name seed = Printf.sprintf "macros_%d" seed

(* The expressions of a part's tokens, separated by commas (macros.tokens-and-code). *)
let reader k =
  block_lines
    (Printf.sprintf
       "fn exprs_%d(ts: meta.Tokens) -> List<meta.Expr> / raise<meta.Error> {" k)
    [
      (0, "var c = meta.cursor(ts)");
      (0, "var xs: List<meta.Expr> = []");
      (0, Printf.sprintf "while !c.at_end() && xs.len() < %d {" (k + 1_000_000));
      (1, "xs.push(try c.expr())");
      (1, "if !c.at_end() { let _ = try c.punct(\",\") }");
      (0, "}");
      (0, "xs");
    ]
    "}"

(* What each token is, groups described within their brackets. *)
let describer k =
  block_lines
    (Printf.sprintf "fn describe_%d(ts: meta.Tokens) -> str {" k)
    [
      (0, "var parts: List<str> = []");
      (0, "for t in ts.items {");
      (1, "match t.kind() {");
      (2, "Word(w) => parts.push(\"w:{w}\")");
      (2, "Number(n) => parts.push(\"n:{n}\")");
      (2, "Text(x) => parts.push(\"t:{x.value()}\")");
      (2, "Interpolated => parts.push(\"i\")");
      (2, "Punct(p) => parts.push(\"p:{p}\")");
      ( 2,
        Printf.sprintf
          "Group(Paren, inner) => parts.push(\"({describe_%d(inner)})\")" k );
      ( 2,
        Printf.sprintf
          "Group(Bracket, inner) => parts.push(\"[{describe_%d(inner)}]\")" k );
      ( 2,
        Printf.sprintf
          "Group(Brace, inner) => parts.push(\"\\{{describe_%d(inner)}}\")" k );
      (1, "}");
      (0, "}");
      (0, Printf.sprintf "\"%d \".join(parts)" (k mod 10));
    ]
    "}"

let decl name kind doc params result ~raises body =
  { called = name; kind; doc; params; result; raises; body }

(* Expressions read by the reader: a list of them, their number and them, or
   the helper [h] called with them, through [$..xs] splices. *)
let read k name kind =
  let doc, made =
    match kind with
    | Listed -> ("A list of its parts.", [ "quote { [$..xs] }" ])
    | Tupled ->
        ( "Its parts' number, then its parts.",
          [ "let n = xs.len()"; "quote { ($n, $..xs) }" ] )
    | Called h ->
        ( "A helper's call with its parts.",
          [ Printf.sprintf "quote { %s($..xs) }" h.fname ] )
    | _ -> invalid_arg "Macro_module.read"
  in
  decl name kind doc
    [ ("ts", "meta.Tokens") ]
    "Expr" ~raises:true
    (List.map
       (fun text -> (0, text))
       (Printf.sprintf "let xs = try exprs_%d(ts)" k :: made))

(* [name = expr] fields, read by a cursor: a record literal of them, the
   user's names spliced as its fields'. *)
let record k name =
  decl name Record "A record of its fields."
    [ ("ts", "meta.Tokens") ]
    "Expr" ~raises:true
    [
      (0, "var c = meta.cursor(ts)");
      (0, "var fields: List<meta.FieldInit> = []");
      ( 0,
        Printf.sprintf "while !c.at_end() && fields.len() < %d {" (k + 2_000_000)
      );
      (1, "let n = try c.name()");
      (1, "let _ = try c.punct(\"=\")");
      (1, "let e = try c.expr()");
      (1, "fields.push(quote field { $n: $e })");
      (1, "if !c.at_end() { let _ = try c.punct(\",\") }");
      (0, "}");
      (0, "quote { { $..fields } }");
    ]

let words k name =
  decl name Words "What its tokens are."
    [ ("ts", "meta.Tokens") ]
    "Expr" ~raises:false
    [ (0, Printf.sprintf "let s = describe_%d(ts)" k); (0, "quote { $s }") ]

let pattern name kind =
  let doc, params, text =
    match kind with
    | Either -> ("Either pattern.", [ "a"; "b" ], "$a | $b")
    | Some_of -> ("[Some] of the pattern.", [ "a" ], "Some($a)")
    | Pair -> ("The pair of the patterns.", [ "a"; "b" ], "($a, $b)")
    | _ -> invalid_arg "Macro_module.pattern"
  in
  decl name kind doc
    (List.map (fun p -> (p, "meta.Pattern")) params)
    "Pattern" ~raises:false
    (quote ~form:"pattern" (line text))

(* A macro of [kind], named after it. *)
let declare mp k helpers kind =
  let named prefix = fresh mp prefix in
  match kind with
  | `Mix -> mix mp ~mark:k (named "mix")
  | `Spell -> spell mp ~mark:k (named "spell")
  | `Listed -> read k (named "listed") Listed
  | `Tupled -> read k (named "tupled") Tupled
  | `Called -> read k (named "called") (Called (Pick.one mp.r helpers))
  | `Record -> record k (named "record")
  | `Words -> words k (named "words")
  | `Twice -> twice mp (named "twice") (Pick.one mp.r helpers)
  | `Either -> pattern (named "either") Either
  | `Some_of -> pattern (named "some_of") Some_of
  | `Pair -> pattern (named "pair") Pair
  | `Spelled -> spelled mp ~mark:k (named "spelled")
  | `Shape -> shape mp (named "shape")

(* The kinds of a module's macros: a [Mix], a [Listed], a [Twice], a pattern
   macro and a [Shape] in each, and some of the others. *)
let kinds r =
  let maybe p kind = if Pick.chance r p then [ kind ] else [] in
  let patterns = [ `Either; `Some_of; `Pair; `Spelled ] in
  let first = Pick.one r patterns in
  let second = Pick.one r (List.filter (( <> ) first) patterns) in
  [ `Mix ] @ maybe 0.7 `Spell @ [ `Listed ] @ maybe 0.5 `Tupled
  @ maybe 0.5 `Called @ maybe 0.5 `Record @ maybe 0.5 `Words @ [ `Twice; first ]
  @ maybe 0.5 second @ [ `Shape ] @ maybe 0.3 `Mix

let make seed =
  let mp =
    {
      r = Pick.make (Hashtbl.hash (seed, "macros"));
      decls = [];
      fns = [];
      count = 0;
      fault;
      fault_variants;
      panics = false;
    }
  in
  let k = Pick.between mp.r 7 999_999 in
  let helpers = Pick.times (Pick.between mp.r 1 2) (fun () -> helper mp) in
  let decls = List.map (declare mp k (List.map fst helpers)) (kinds mp.r) in
  let reads =
    List.exists
      (fun d ->
        match d.kind with Listed | Tupled | Called _ -> true | _ -> false)
      decls
  in
  {
    module_name = name seed;
    helpers =
      (List.map snd helpers
      @ (if reads then [ reader k ] else [])
      @
      if List.exists (fun d -> d.kind = Words) decls then [ describer k ]
      else []);
    decls;
  }

(* The lines of [d], with [planted] at the top of its body and the type of
   its parameter [i] written [t] when [retyped] is [(i, t)]. *)
let render ?(planted = []) ?retyped d =
  let param i (name, t) =
    let t = match retyped with Some (j, t') when i = j -> t' | _ -> t in
    name ^ ": " ^ t
  in
  let row = if d.raises then " / raise<meta.Error>" else "" in
  line ("/// " ^ d.doc)
  @ block_lines
      (Printf.sprintf "pub macro %s(%s) -> meta.%s%s {" d.called
         (String.concat ", " (List.mapi param d.params))
         d.result row)
      (planted @ d.body) "}"

let text ?(edit = fun _ -> None) m =
  let decl d = Option.value (edit d) ~default:(render d) in
  let items = (line "use std.meta" :: m.helpers) @ List.map decl m.decls in
  String.concat "\n" (List.map Code.render items)
