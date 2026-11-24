(* Procedural macros (macros.procedural-declarations and macros.procedural-uses) in a csmith program, made from streams of their
   own, so that the rest of the program is the one the same seed makes without
   them: a module of macros (Macro_module), which the program imports with
   [meta use] since a macro is used only from another module (macros.meta-use), and
   uses of each of its macros, in [main] and in functions of their own, the
   pattern macros' in the arms of matches, each giving a value that [main]
   prints. Each use's parts are code of its scope, of the types its macro
   takes, so that the expansion checks where the use stands (macros.running). *)

open Code
open Context
open Ty
open Macro_kinds

(* How likely a program is to use macros: one in ten, fewer than the other
   streams, since a program's macros are run by both implementations each
   time it is checked, and nearly every bundle of ten would hold one. *)
let using = 0.1

let wanted seed =
  Pick.chance (Pick.make (Hashtbl.hash (seed, "uses macros"))) using

(* [text] as a part, parenthesized if a comma outside its brackets would
   split it (macros.parts). *)
let part text =
  let depth = ref 0 and quoted = ref false and escaped = ref false in
  let splits = ref false in
  String.iter
    (fun c ->
      if !quoted then
        if !escaped then escaped := false
        else if c = '\\' then escaped := true
        else if c = '"' then quoted := false
        else ()
      else
        match c with
        | '"' -> quoted := true
        | '(' | '[' | '{' -> incr depth
        | ')' | ']' | '}' -> decr depth
        | ',' when !depth = 0 -> splits := true
        | _ -> ())
    text;
  if !splits then "(" ^ text ^ ")" else text

let call m d parts =
  Printf.sprintf "%s.%s!(%s)" m.module_name d.called (String.concat ", " parts)

(* Code of type [t] in the scope [sc], for a part or an argument: now and
   then, for a list, a use of the [Listed] macro of [m], which, as a part,
   expands inside the expansion it is spliced into (macros.nested-expansions). *)
let rec value b sc m t =
  let r = b.p.r in
  match (t, List.find_opt (fun d -> d.kind = Listed) m.decls) with
  | List u, Some d when Pick.chance r 0.25 ->
      call m d (Pick.times (Pick.between r 0 2) (fun () -> value b sc m u))
  | _ -> part (Expr.expr b sc ~depth:2 ~known:false t).text

(* A use of a macro whose one parameter takes tokens: its parts in its group,
   or, without a group, in a trailing block (macros.parts). *)
let tokens_call r m d parts =
  if parts <> [] && Pick.chance r 0.4 then
    Printf.sprintf "%s.%s!() { %s }" m.module_name d.called
      (String.concat ", " parts)
  else call m d parts

(* A part's tokens: one to five, of every kind that [Words] tells apart, and
   groups, which may be empty, of them; no comma, which would end the part
   (macros.parts). *)
let rec tokens r depth =
  let token () =
    Pick.run r
      [
        ( 4,
          fun () ->
            Pick.one r
              [ "alpha"; "beta"; "x1"; "y_2"; "if"; "in"; "true"; "self" ] );
        (2, fun () -> Lit.int r (Pick.one r int_kinds));
        (1, fun () -> Pick.one r [ "0x1F"; "0o17"; "0b101"; "1_000"; "2.5e3" ]);
        (1, fun () -> Lit.float r);
        (2, fun () -> Lit.string r);
        (1, fun () -> "\"at {alpha} and {x1 + 1}\"");
        ( 3,
          fun () ->
            Pick.one r
              [
                "+";
                "-%";
                "*";
                "==";
                "<=";
                "=>";
                "->";
                "..";
                ":";
                ";";
                "&&";
                "|";
              ] );
        ( (if depth > 0 then 2 else 0),
          fun () ->
            let open_, close =
              Pick.one r [ ("(", ")"); ("[", "]"); ("{", "}") ]
            in
            if Pick.chance r 0.2 then open_ ^ close
            else open_ ^ tokens r (depth - 1) ^ close );
      ]
  in
  String.concat " " (Pick.times (Pick.between r 1 5) token)

(* A use of the expression macro [d], in the scope [sc], and the type of
   what it gives. *)
let use_of b sc m d =
  let r = b.p.r in
  let several lo hi make = Pick.times (Pick.between r lo hi) make in
  match d.kind with
  | Mix (ts, ty) -> (call m d (List.map (value b sc m) ts), ty)
  | Spell (ts, ty) -> (call m d (Lit.string r :: List.map (value b sc m) ts), ty)
  | Listed ->
      let t = random_ty b.p 2 in
      (tokens_call r m d (several 0 4 (fun () -> value b sc m t)), List t)
  | Tupled ->
      let ts = several 1 3 (fun () -> random_ty b.p 2) in
      (tokens_call r m d (List.map (value b sc m) ts), Tuple (Int I64 :: ts))
  | Called h ->
      ( tokens_call r m d (List.map (fun (_, t) -> value b sc m t) h.params),
        h.ret )
  | Twice h -> (call m d [ value b sc m (snd (List.hd h.params)) ], h.ret)
  | Words -> (tokens_call r m d (several 0 3 (fun () -> tokens r 2)), Str)
  | Record | Either | Some_of | Pair | Spelled | Shape _ ->
      invalid_arg "Csmith_macros.use_of"

(* A use of the [Record] macro [d], in the scope [sc], and the anonymous
   record type of what it gives, written. Its fields' names are fresh, so no
   two of its uses give the same code. *)
let record_of b sc m d =
  let r = b.p.r in
  let fields =
    Pick.times (Pick.between r 1 3) (fun () ->
        (fresh b.p "fl", random_ty b.p 2))
  in
  ( tokens_call r m d
      (List.map (fun (f, t) -> f ^ " = " ^ value b sc m t) fields),
    "{ "
    ^ String.concat ", "
        (List.map (fun (f, t) -> f ^ ": " ^ to_string t) fields)
    ^ " }" )

(* [n] distinct literal patterns of [ty], an integer type or [str]. *)
let literals r ty n =
  let rec draw found =
    if List.length found = n then found
    else
      let l =
        match ty with
        | Int k when signed k -> string_of_int (Pick.between r (-5) 20)
        | Int _ -> string_of_int (Pick.between r 0 25)
        | _ -> Lit.string r
      in
      draw (if List.mem l found then found else found @ [ l ])
  in
  draw []

(* The type of a literal pattern. *)
let pattern_ty r =
  if Pick.chance r 0.75 then Int (Pick.one r int_kinds) else Str

(* The type that a match on uses of the pattern macro [d] matches, and the
   arms' patterns, each with the variables it binds. Every arm holds a literal
   that no arm before it does, so none is unreachable (patterns.unreachable-arms). *)
let arms b m d =
  let r = b.p.r in
  let n = Pick.between r 1 3 in
  match d.kind with
  | Either ->
      let t = pattern_ty r in
      let ls = literals r t (2 * n) in
      ( t,
        List.init n (fun i ->
            (call m d [ List.nth ls (2 * i); List.nth ls ((2 * i) + 1) ], []))
      )
  | Some_of ->
      let t = pattern_ty r in
      (Option t, List.map (fun l -> (call m d [ l ], [])) (literals r t n))
  | Pair ->
      let t = pattern_ty r and u = random_ty b.p 1 in
      let arm l =
        if Pick.chance r 0.3 then (call m d [ l; "_" ], [])
        else
          let y = { name = fresh b.p "y"; ty = u; mutable_ = false } in
          (call m d [ l; y.name ], [ y ])
      in
      (Tuple [ t; u ], List.map arm (literals r t n))
  | Spelled -> (Str, [ (call m d (literals r Str 1), []) ])
  | _ -> invalid_arg "Csmith_macros.arms"

(* The lines of a match on uses of the pattern macro [d], whose value, of a
   random type, a new variable [v] holds, and that type. *)
let matched b sc m d v =
  let ty = random_ty b.p 2 in
  let s, arms = arms b m d in
  let scrutinee = Expr.expr b sc ~depth:2 ~known:true s in
  let arm (pattern, bound) =
    let sc = { sc with vars = bound @ sc.vars } in
    (0, pattern ^ " => " ^ (Expr.expr b sc ~depth:2 ~known:false ty).text)
  in
  let fallback = Expr.expr b sc ~depth:2 ~known:false ty in
  ( block_lines
      (Printf.sprintf "let %s: %s = match %s {" v (to_string ty)
         (head scrutinee.text))
      (List.map arm arms @ line ("_ => " ^ fallback.text))
      "}",
    ty )

(* Lines that bind a new variable to what a use of [d] gives, in the scope
   [sc], with the variable's name, its type, written, and its type but for an
   anonymous record's. A type macro's use is the variable's type. *)
let bound b sc m d =
  let name = fresh b.p "mc" in
  let bind ty text = line (Printf.sprintf "let %s: %s = %s" name ty text) in
  let made lines ty written = (lines, name, written, ty) in
  match d.kind with
  | Either | Some_of | Pair | Spelled ->
      let lines, ty = matched b sc m d name in
      made lines (Some ty) (to_string ty)
  | Shape (ty, holes) ->
      (* A map's type would hold a comma outside a group, which would split
         the part. *)
      let types = List.map (fun h -> (h, random_ty b.p ~maps:false 2)) holes in
      let use = call m d (List.map (fun (_, t) -> to_string t) types) in
      let ty = fill types ty in
      let value = Expr.expr b sc ~depth:2 ~known:false ty in
      made (bind use value.text) (Some ty) use
  | Record ->
      let text, written = record_of b sc m d in
      made (bind written text) None written
  | _ ->
      let text, ty = use_of b sc m d in
      made (bind (to_string ty) text) (Some ty) (to_string ty)

let shown v = line (Printf.sprintf "print(\"%s: {%s}\")" v v)

(* A function of a few parameters that binds what a use of [d] gives, then,
   but for a record, runs a few statements that may read it, and returns it,
   and the lines of [main] that call it and print what it returns. The
   statements make its body unlike any other's, which W0302 would report
   (docs.duplicate-bodies). *)
let in_function b sc m d =
  let r = b.p.r in
  let params =
    List.map (var b.p "q")
      (Pick.times (Pick.between r 0 2) (fun () -> random_ty b.p 2))
  in
  let inner = Macro_kinds.scope params in
  let lines, v, written, ty = bound b inner m d in
  let after =
    match ty with
    | None -> []
    | Some ty ->
        let sc =
          declare { inner with returns = Some ty } v ty ~mutable_:false
        in
        let body = { p = b.p; budget = 600; spent = 0 } in
        snd (Statements.stmts body sc ~depth:2 (Pick.between r 1 3))
  in
  let name = fresh b.p "mf" in
  let opening =
    Printf.sprintf "fn %s(%s)%s {" name
      (String.concat ", " (List.map typed params))
      (if written = "()" then "" else " -> " ^ written)
  in
  let result = fresh b.p "mc" in
  let args = List.map (fun q -> value b sc m q.ty) params in
  ( [ block_lines opening (lines @ after @ line v) "}" ],
    line (Printf.sprintf "let %s: %s = %s" result written (call_text name args))
    @ shown result )

let uses m p sc seed =
  let p = { p with r = Pick.make (Hashtbl.hash (seed, "macro uses")) } in
  let b = { p; budget = 4_000; spent = 0 } in
  let sc = { sc with weight = 1 } in
  let one d =
    if Pick.chance p.r 0.6 then
      let lines, v, _, _ = bound b sc m d in
      ([], lines @ shown v)
    else in_function b sc m d
  in
  let made =
    List.concat_map
      (fun d -> Pick.times (Pick.between p.r 1 2) (fun () -> one d))
      m.decls
  in
  (List.concat_map fst made, List.concat_map snd made)
