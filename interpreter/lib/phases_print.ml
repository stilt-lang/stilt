(* docs.same-body: the print of a typed body. *)

open Tast

type state = { out : Buffer.t; locals : (int, int) Hashtbl.t }

let add st s =
  Buffer.add_string st.out s;
  Buffer.add_char st.out ' '

(* Each local by its number, in the order the body binds them. *)
let local st (v : Hir.var) =
  let n =
    match Hashtbl.find_opt st.locals v.id with
    | Some n -> n
    | None ->
        let n = Hashtbl.length st.locals in
        Hashtbl.add st.locals v.id n;
        n
  in
  add st ("l" ^ string_of_int n)

let item st (i : Hir.item) = add st (i.home ^ "." ^ i.name)
let text st s = add st (Printf.sprintf "%S" s)
let mode (m : Ast.mode) = match m with Let -> "Let" | Inout -> "Inout"
let literal s = String.concat "" (String.split_on_char '_' s)

let rec ty st t =
  match Types.resolve t with
  | Types.Con (i, args) ->
      item st i;
      tys st args
  | Types.Param v -> add st ("'" ^ v.name)
  | Types.Tuple items ->
      add st "tuple";
      tys st items
  | Types.Record fields ->
      add st "record";
      List.iter
        (fun (f, t) ->
          add st f;
          ty st t)
        fields
  | Types.Spread (_, t) ->
      add st "..";
      ty st t
  | Types.Fn (params, ret, _) ->
      add st "fn";
      List.iter
        (fun (m, p) ->
          add st (mode m);
          ty st p)
        params;
      add st "->";
      ty st ret
  | Types.App (h, args) ->
      ty st h;
      tys st args
  | Types.Forall p ->
      add st "forall";
      ty st p.body
  | Types.Handler h ->
      add st "handler";
      item st h.eff;
      tys st (h.hargs @ Option.to_list h.answer)
  | Types.Var _ -> add st "_"
  | Types.Value v -> add st v
  | Types.Error -> add st "!"

and tys st items =
  add st "<";
  List.iter (ty st) items;
  add st ">"

let callee st = function
  | Function i -> item st i
  | Member (i, name) ->
      item st i;
      text st name
  | Trait_method (i, name, t) ->
      item st i;
      text st name;
      ty st t
  | Operation (i, name) ->
      add st "perform";
      item st i;
      text st name

let rec expr st (e : expr) =
  match e.desc with
  | Int s | Float s ->
      text st (literal s);
      ty st e.ty
  | Str s -> text st s
  | Interpolated segments ->
      add st "\"";
      List.iter
        (function
          | Text s -> text st s
          | Splice (e, spec) ->
              expr st e;
              text st (Option.value spec ~default:""))
        segments;
      add st "\""
  | Bool b -> add st (string_of_bool b)
  | Local v ->
      local st v;
      ty st e.ty
  (* generics.value-parameters-in-body: a value parameter, as its type prints it. *)
  | Value_param v ->
      add st ("'" ^ v.name);
      ty st e.ty
  (* meta.erasure: deleting an annotation changes no observable, so a body
     prints as its erased form. *)
  | Comptime form -> expr st form
  | _ -> compound st e

and compound st (e : expr) =
  match e.desc with
  | Constant i ->
      add st "const";
      item st i
  | Member_constant (i, name, ts) ->
      add st "member";
      item st i;
      text st name;
      tys st ts
  | Callee (c, ts) ->
      add st "fnval";
      callee st c;
      tys st ts
  | Constructor (i, ts) ->
      add st "ctor";
      item st i;
      tys st ts
  | Construct (i, ts, args) ->
      add st "construct";
      item st i;
      tys st ts;
      exprs st args
  | Record (i, ts, fields) ->
      add st "record";
      item st i;
      tys st ts;
      List.iter
        (fun (name, value) ->
          text st name;
          expr st value)
        fields;
      add st "end"
  | _ -> values st e

and values st (e : expr) =
  match e.desc with
  | Tuple items ->
      add st "tuple";
      exprs st items
  | Update (base, fields) ->
      add st "update";
      expr st base;
      List.iter
        (fun (name, value) ->
          text st name;
          expr st value)
        fields;
      add st "end"
  | Spread s ->
      add st "spread";
      ty st s.pack;
      expr st s.body
  | List items ->
      add st "list";
      exprs st items
  | Field (of_, name) ->
      add st "field";
      expr st of_;
      text st name
  | Tuple_field (of_, n) ->
      add st ("field" ^ string_of_int n);
      expr st of_
  | Call (c, ts, a, _) ->
      add st "call";
      callee st c;
      tys st ts;
      args st a
  | Call_value (f, a) ->
      add st "callvalue";
      expr st f;
      args st a
  | Index (of_, at) ->
      add st "index";
      expr st of_;
      expr st at
  | _ -> operations st e

and operations st (e : expr) =
  match e.desc with
  | Unary (op, operand) ->
      add st (match op with Neg -> "Neg" | Not -> "Not");
      expr st operand
  | Binary (op, left, right) ->
      add st (Sexp.binary op);
      expr st left;
      expr st right
  | Else (value, otherwise) ->
      add st "else";
      expr st value;
      expr st otherwise
  | Try (operand, catch) ->
      add st "try";
      expr st operand;
      Option.iter
        (fun (c : catch) ->
          add st "catch";
          ty st c.error;
          arms st c.arms)
        catch;
      add st "end"
  | Raise value ->
      add st "raise";
      expr st value
  | Return value ->
      add st "return";
      Option.iter (expr st) value;
      add st "end"
  | _ -> control st e

and control st (e : expr) =
  match e.desc with
  | Break -> add st "break"
  | Continue -> add st "continue"
  | Closure (params, _, body) ->
      add st "closure";
      List.iter (pattern st) params;
      expr st body
  | Block b -> block st b
  | If (cond, then_, otherwise) ->
      add st "if";
      expr st cond;
      block st then_;
      Option.iter
        (fun e ->
          add st "else";
          expr st e)
        otherwise;
      add st "end"
  | If_let (p, scrutinee, then_, otherwise) ->
      add st "iflet";
      expr st scrutinee;
      pattern st p;
      block st then_;
      Option.iter
        (fun e ->
          add st "else";
          expr st e)
        otherwise;
      add st "end"
  | Match (scrutinee, a) ->
      add st "match";
      expr st scrutinee;
      arms st a
  | _ -> loops st e

and loops st (e : expr) =
  match e.desc with
  | Loop b ->
      add st "loop";
      block st b
  | While (cond, b) ->
      add st "while";
      expr st cond;
      block st b
  | For (p, iterable, b) ->
      add st "for";
      (match iterable with
      | Iter e -> expr st e
      | Range (from, to_, end_) ->
          add st
            (match end_ with Exclusive -> "range" | Inclusive -> "range=");
          expr st from;
          expr st to_);
      pattern st p;
      block st b
  | Hole -> add st "?"
  | _ -> handling st e

(* handlers.handler-literals, handlers.with and handlers.resuming *)
and handling st (e : expr) =
  match e.desc with
  | Handler h ->
      add st (if h.control then "handler->" else "handler");
      item st h.heffect;
      List.iter
        (fun (name, op) ->
          text st name;
          expr st op)
        h.ops;
      add st "end"
  | With (h, eff, ts, b) ->
      add st "with";
      expr st h;
      item st eff;
      tys st ts;
      block st b
  | Resume value ->
      add st "resume";
      Option.iter (expr st) value;
      add st "end"
  (* shared.when *)
  | When (names, b) ->
      add st "when";
      List.iter
        (fun (h, v) ->
          expr st h;
          local st v)
        names;
      block st b
  (* macros.quote: a quote, as its tokens and its splices. *)
  | Quote q ->
      add st "quote";
      List.iter
        (fun (t : Lexer.token) -> add st (Token.to_string t.token))
        (Macro_tokens.flatten q.tokens);
      List.iter (fun (s : splice) -> expr st s.value) q.splices;
      add st "end"
  | _ -> add st "!"

and exprs st items =
  add st "(";
  List.iter (expr st) items;
  add st ")"

and args st items =
  add st "(";
  List.iter
    (fun (a : arg) ->
      add st (mode a.mode);
      expr st a.value)
    items;
  add st ")"

and arms st items =
  List.iter
    (fun (a : arm) ->
      add st "arm";
      pattern st a.pattern;
      Option.iter
        (fun g ->
          add st "if";
          expr st g)
        a.guard;
      add st (if a.because then "because" else "=>");
      expr st a.body)
    items;
  add st "end"

and block st b =
  add st "{";
  List.iter (stmt st) b;
  add st "}"

and stmt st (s : stmt) =
  match s.stmt with
  | Let b -> binding st "let" b
  | Var b -> binding st "var" b
  | Assign (op, place, value) ->
      add st ("assign" ^ Option.fold ~none:"" ~some:Sexp.binary op);
      expr st place;
      expr st value
  | Assert e ->
      add st "assert";
      expr st e
  | Yield e ->
      add st "yield";
      expr st e
  | Expr e -> expr st e

and binding st tag (b : binding) =
  add st tag;
  expr st b.value;
  pattern st b.pattern;
  Option.iter
    (fun e ->
      add st "else";
      expr st e)
    b.otherwise

and pattern st (p : pattern) =
  match p.pat with
  | P_wild -> add st "_"
  | P_bind v ->
      local st v;
      ty st p.pty
  | P_int s ->
      text st (literal s);
      ty st p.pty
  | P_str s -> text st s
  | P_bool b -> add st (string_of_bool b)
  | P_tuple items ->
      add st "tuple";
      patterns st items
  | P_const e ->
      add st "const";
      expr st e
  | _ -> compound_pattern st p

and compound_pattern st (p : pattern) =
  match p.pat with
  | P_variant (i, payload) ->
      add st "variant";
      item st i;
      patterns st payload
  | P_record fields ->
      add st "record";
      List.iter
        (fun (name, field) ->
          text st name;
          pattern st field)
        fields;
      add st "end"
  | P_list (items, rest) -> (
      add st "list";
      patterns st items;
      match rest with
      | Exact -> add st "exact"
      | Rest -> add st ".."
      | Rest_bind v ->
          add st "..";
          local st v)
  | P_or alternatives ->
      add st "or";
      patterns st alternatives
  | _ -> add st "!"

and patterns st items =
  add st "(";
  List.iter (pattern st) items;
  add st ")"

let print ~params b =
  let st = { out = Buffer.create 256; locals = Hashtbl.create 16 } in
  List.iter (local st) params;
  block st b;
  Buffer.contents st.out
