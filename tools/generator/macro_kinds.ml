(* The module of procedural macros (macros.procedural-declarations and macros.procedural-bodies) that a csmith program imports with
   [meta use], made from a stream of its own: private helpers, which quotes
   and macros call (macros.linking), and macros of the kinds below. Each kind fixes
   what a use gives the macro and what it expands to, so that Csmith_macros
   writes uses that check by construction. A macro's own code and the code its
   quotes write are generated as a function's body is, over the types of the
   standard library, which the module can name, so they can't panic, raise or
   loop without end (macros.step-limits). *)

open Code
open Context
open Ty

type kind =
  | Mix of Ty.t list * Ty.t
  | Spell of Ty.t list * Ty.t
  | Listed
  | Tupled
  | Called of fn_sig
  | Record
  | Words
  | Twice of fn_sig
  | Either
  | Some_of
  | Pair
  | Spelled
  | Shape of Ty.t * string list

type decl = {
  called : string;
  kind : kind;
  doc : string;
  params : (string * string) list;
  result : string;
  raises : bool;
  body : line list;
}

type t = { module_name : string; helpers : line list list; decls : decl list }

let scope vars =
  {
    vars = List.rev vars;
    frozen = [];
    loop = false;
    may_raise = false;
    io = false;
    returns = None;
    weight = 1;
  }

let var p prefix ty = { name = fresh p prefix; ty; mutable_ = false }
let typed (v : var) = v.name ^ ": " ^ Ty.to_string v.ty
let arrow t = if t = Unit then "" else " -> " ^ Ty.to_string t

(* A private function of the module: statements, then its result. *)
let helper mp =
  let r = mp.r in
  let fname = fresh mp "h" in
  let params = Pick.times (Pick.between r 1 3) (fun () -> random_ty mp 2) in
  let vars = List.map (var mp "x") params in
  let ret = random_ty mp 2 in
  let b = { p = mp; budget = 600; spent = 0 } in
  let sc = { (scope vars) with returns = Some ret } in
  let sc, body = Statements.stmts b sc ~depth:2 (Pick.between r 1 3) in
  let result = Expr.expr b sc ~depth:2 ~known:false ret in
  let f =
    {
      fname;
      params = List.map (fun t -> (false, t)) params;
      ret;
      raises = false;
      cost = max 1 b.spent;
    }
  in
  mp.fns <- mp.fns @ [ f ];
  let opening =
    Printf.sprintf "fn %s(%s)%s {" fname
      (String.concat ", " (List.map typed vars))
      (arrow ret)
  in
  (f, block_lines opening (body @ line result.text) "}")

let quote ?(form = "") lines =
  let opening = if form = "" then "quote {" else "quote " ^ form ^ " {" in
  block_lines opening lines "}"

let expr b vars ty = (Expr.expr b (scope vars) ~depth:3 ~known:false ty).text

(* A value of the macro's own code, spliced as a literal, a negative one as
   [(-3)], whose [-] is part of the literal, so that it fits the type it has
   there however small it is (macros.literal-splices; numbers.negative-literals): an integer, a
   [bool] or a [str]. One that [$(e)] splices is [~known], since nothing
   outside [e] types it. *)
let literal_ty r =
  Pick.run r
    [
      (3, fun () -> Int (Pick.one r int_kinds));
      (1, fun () -> Bool);
      (2, fun () -> Str);
    ]

let literal ?(known = false) b vars ty =
  (Expr.expr b (scope vars) ~depth:2 ~known ty).text

(* The module's mark, an [i64] bound to a new variable of [vars], with the
   variables after it and the line that binds it. Each module has a mark of its
   own, so that no two modules of the ten programs that [just differential]
   runs as one declare macros of the same body, which W0302 would report
   (docs.same-body). *)
let marked b ~mark vars =
  let v = var b.p "v" (Int I64) in
  (vars @ [ v ], line (Printf.sprintf "let %s = %d" (typed v) mark))

(* Lines that bind [n] new variables to values made from [vars], with the
   variables after them. *)
let rec values b vars n =
  if n = 0 then (vars, [])
  else
    let v = var b.p "v" (random_ty b.p 2) in
    let first = (0, "let " ^ typed v ^ " = " ^ expr b vars v.ty) in
    let vars, rest = values b (vars @ [ v ]) (n - 1) in
    (vars, first :: rest)

(* Lines that bind each part to a variable of its type, then the module's
   mark, then a few more values, and the variables in scope after them. *)
let bindings b ~mark parts vars =
  let bound =
    List.map
      (fun (part, v) ->
        (0, Printf.sprintf "let %s: %s = $%s" v.name (to_string v.ty) part))
      parts
  in
  let vars, mark = marked b ~mark (vars @ List.map snd parts) in
  let vars, more = values b vars (Pick.between b.p.r 0 2) in
  (vars, bound @ mark @ more)

let exprs = List.map (fun (a, _) -> (a, "meta.Expr"))
let parts_of mp ts = List.map (fun t -> (fresh mp "a", var mp "v" t)) ts
let body mp = { p = mp; budget = 600; spent = 0 }

(* Parts of the types [ts], bound by the quote, and combined, with a few more
   values, into an expression of type [ty]: [$x] splices. *)
let mix mp ~mark name =
  let r = mp.r in
  let b = body mp in
  let ts = Pick.times (Pick.between r 1 3) (fun () -> random_ty mp 2) in
  let parts = parts_of mp ts in
  let ty = random_ty mp 2 in
  let vars, lines = bindings b ~mark parts [] in
  {
    called = name;
    kind = Mix (ts, ty);
    doc = "Its parts, combined into one value.";
    params = exprs parts;
    result = "Expr";
    raises = false;
    body = quote (lines @ line (expr b vars ty));
  }

(* A string literal, whose value and values that the macro computes from it
   the quote splices as literals, with [$x] and [$(e)], then parts of the
   types [ts], all combined into an expression of type [ty]. *)
let spell mp ~mark name =
  let r = mp.r in
  let b = body mp in
  let t = fresh mp "t" in
  let s = var mp "s" Str in
  let n = var mp "n" (literal_ty r) in
  let code =
    [
      (0, Printf.sprintf "let %s = %s.value()" s.name t);
      (0, "let " ^ typed n ^ " = " ^ literal b [ s ] n.ty);
    ]
  in
  let text = var mp "v" Str and value = var mp "v" n.ty in
  let computed = var mp "v" (literal_ty r) in
  let spliced =
    [
      (0, Printf.sprintf "let %s = $%s" (typed text) s.name);
      (0, Printf.sprintf "let %s = $%s" (typed value) n.name);
      ( 0,
        Printf.sprintf "let %s = $(%s)" (typed computed)
          (literal ~known:true b [ s; n ] computed.ty) );
    ]
  in
  let ts = Pick.times (Pick.between r 0 2) (fun () -> random_ty mp 2) in
  let parts = parts_of mp ts in
  let ty = random_ty mp 2 in
  let vars, lines = bindings b ~mark parts [ text; value; computed ] in
  {
    called = name;
    kind = Spell (ts, ty);
    doc = "Values spelled from a string literal, combined with its parts.";
    params = (t, "meta.Text") :: exprs parts;
    result = "Expr";
    raises = false;
    body = code @ quote (spliced @ lines @ line (expr b vars ty));
  }

(* A part bound to a fresh name by one quote, which another quote passes to
   the helper [h], whose other arguments it computes. *)
let twice mp name (h : fn_sig) =
  let b = body mp in
  let first, rest =
    match h.params with
    | (_, t) :: rest -> (t, List.map snd rest)
    | [] -> invalid_arg "Macro_kinds.twice"
  in
  let e = fresh mp "e" and v = fresh mp "v" and named = fresh mp "q" in
  let args = ("$" ^ v) :: List.map (expr b []) rest in
  let call = call_text h.fname args in
  let text = Pick.one mp.r [ "v"; "value"; "tmp"; "it" ] in
  {
    called = name;
    kind = Twice h;
    doc = "Its part, computed once, passed to a helper.";
    params = [ (e, "meta.Expr") ];
    result = "Expr";
    raises = false;
    body =
      [
        (0, Printf.sprintf "let %s = meta.fresh(\"%s\")" v text);
        (0, Printf.sprintf "let %s = quote { %s }" named call);
      ]
      @ quote
          [
            (0, Printf.sprintf "let $%s: %s = $%s" v (to_string first) e);
            (0, "$" ^ named);
          ];
  }

(* A string literal: a pattern of its value, or of a [str] the macro computes
   from it and the module's mark. *)
let spelled mp ~mark name =
  let b = body mp in
  let t = fresh mp "t" and s = var mp "s" Str in
  let vars, marking = marked b ~mark [ s ] in
  {
    called = name;
    kind = Spelled;
    doc = "A pattern of a string literal's value, or of another string.";
    params = [ (t, "meta.Text") ];
    result = "Pattern";
    raises = false;
    body =
      line (Printf.sprintf "let %s = %s.value()" s.name t)
      @ marking
      @ quote ~form:"pattern"
          [
            ( 0,
              Printf.sprintf "$%s | $(%s)" s.name
                (literal ~known:true b vars Str) );
          ];
  }

(* A type of the standard library's around each hole, a [Named] type
   written [$t], which it holds once. *)
let rec template mp holes =
  let r = mp.r in
  match holes with
  | [ hole ] ->
      let inner () =
        Pick.run r
          [ (2, fun () -> Named hole); (1, fun () -> template mp holes) ]
      in
      Pick.run r
        [
          (2, fun () -> List (inner ()));
          (2, fun () -> Option (inner ()));
          ( 1,
            fun () ->
              if Pick.chance r 0.5 then Tuple [ inner (); random_ty mp 1 ]
              else Tuple [ random_ty mp 1; inner () ] );
          (1, fun () -> Map (key_ty r, inner ()));
        ]
  | holes -> Tuple (List.map (fun hole -> template mp [ hole ]) holes)

(* [ty] with each hole replaced by its type in [types]. *)
let rec fill types = function
  | Named n as t -> Option.value (List.assoc_opt n types) ~default:t
  | Tuple ts -> Tuple (List.map (fill types) ts)
  | List t -> List (fill types t)
  | Option t -> Option (fill types t)
  | Map (k, v) -> Map (fill types k, fill types v)
  | (Int _ | Float _ | Bool | Str | Unit) as t -> t

(* How many tokens [text], a type, holds, each [>] counted alone. *)
let tokens text =
  let words, others, _ =
    String.fold_left
      (fun (words, others, inside) c ->
        match c with
        | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' ->
            ((if inside then words else words + 1), others, true)
        | ' ' -> (words, others, false)
        | _ -> (words, others + 1, false))
      (0, 0, false) text
  in
  words + others

(* Types: a type of the standard library's around them. A body holds no
   mark, so it is kept under the 20 tokens that W0302 compares (docs.body-size): the quote, its form and its four braces, then the type in 13. *)
let shape mp name =
  let names = Pick.times (Pick.between mp.r 1 2) (fun () -> fresh mp "t") in
  let holes = List.map (fun n -> "$" ^ n) names in
  let rec short () =
    let ty = template mp holes in
    if tokens (to_string ty) <= 13 then ty else short ()
  in
  let ty = short () in
  {
    called = name;
    kind = Shape (ty, holes);
    doc = "A type around its parts.";
    params = List.map (fun n -> (n, "meta.Type")) names;
    result = "Type";
    raises = false;
    body = quote ~form:"type" (line (to_string ty));
  }
