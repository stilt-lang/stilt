(* The walk itself (facts.acceptance-places), in the order the code is written, which
   fills an [Accept_walk.t]. *)

open Tast
module C = Accept_code
module W = Accept_walk

let gives (st : W.state) c positive = C.gives st.w.reader c positive

let rec block (st : W.state) b =
  let depth = List.length st.active in
  List.iter (stmt st) b;
  W.truncate st depth

and stmt st (s : stmt) =
  let span = W.open_span st in
  st.stmts <- span :: st.stmts;
  (match s.stmt with
  | Assign (op, place, value) -> assign st op place value
  | Let b -> binding st b false
  | Var b -> binding st b true
  | Yield place ->
      expr st place;
      W.write st place W.Yield None
  | Assert e | Expr e -> expr st e);
  st.stmts <- List.tl st.stmts;
  W.close_span st span;
  after st s (Dynarray.get st.w.spans span).first

(* The facts a statement gives the code after it in its block: an [if] whose
   then-branch can't complete gives its condition's negation, and a store of a
   key gives it present. *)
and after st (s : stmt) start =
  let negation =
    match s.stmt with
    | Expr e -> (
        match (C.unwrap e).desc with
        | If (c, then_, _) when C.ends_block then_ -> gives st c false
        | _ -> [])
    | _ -> []
  in
  let r = st.w.reader in
  let stored =
    match C.stored r s with Some _ as k -> k | None -> C.stored_if_missing r s
  in
  let present =
    Option.fold ~none:[] ~some:(fun (m, k) -> [ C.Contains (m, k) ]) stored
  in
  W.guard st (negation @ present) start

and assign st op (place : expr) value =
  (match (place.desc, op) with
  | Index (m, _), None when C.is_map m.ty -> st.stores <- place :: st.stores
  | _, Some (Div | Rem) when C.divides place value ->
      W.pend st (W.Division value) place
  | _ -> ());
  expr st place;
  expr st value;
  W.write st place (W.Assign op) (Some value)

and binding st (b : binding) var =
  expr st b.value;
  Option.iter (expr st) b.otherwise;
  match b.pattern.pat with
  | P_bind v ->
      Hashtbl.replace st.w.decls v.id
        (st.current, if var then W.Var_init b.value else W.Let_init b.value)
  | _ -> ()

and parts st e =
  List.iter
    (function Walk.Expr x -> expr st x | Walk.Block b -> block st b)
    (Walk.parts e)

and expr st (e : expr) =
  match e.desc with
  | Closure (_, _, body) -> closure st body
  | If (c, then_, alt) -> if_ st c then_ alt
  | While (c, b) -> looped st e (Some c) b
  | Loop b -> looped st e None b
  | For (p, iterable, b) -> for_ st p iterable b
  | Index (base, key) ->
      if not (List.memq e st.stores) then W.pend st (W.Index (base, key)) e;
      parts st e
  | Binary (((And | Or) as op), a, b) -> operands st (op = And) a b
  | Binary ((Div | Rem), a, b) when C.divides a b ->
      W.pend st (W.Division b) e;
      parts st e
  | Call (c, _, args, _) | Project (c, _, args, _) -> call st e (Some c) args
  | Call_value (_, args) -> call st e None args
  | When (names, _) ->
      List.iter
        (fun (_, (v : Hir.var)) -> Hashtbl.replace st.w.reader.whens v.id ())
        names;
      parts st e
  | _ -> parts st e

and call st e c args =
  (match (c, st.self) with
  | Some c, Some key when Implicit_names.callee_key st.env c = Some key ->
      W.pend st (W.Self_call args) e
  | _ -> ());
  parts st e;
  List.iteri
    (fun i (a : arg) ->
      if a.mode = Inout then
        let insert =
          i = 0 && Option.fold ~none:false ~some:(C.is_map_method "insert") c
        in
        W.write st a.value (if insert then W.Insert else W.Inout) None)
    args

(* A closure literal's body, a body of its own. *)
and closure st body =
  let outer = st.current and active = st.active in
  let loops = st.loops_in and stmts = st.stmts in
  st.current <- st.bodies;
  st.bodies <- st.bodies + 1;
  st.active <- [];
  st.loops_in <- [];
  st.stmts <- [];
  expr st body;
  st.active <- active;
  st.loops_in <- loops;
  st.stmts <- stmts;
  st.current <- outer

(* The condition of an [if] or a [while], a statement of its own. *)
and condition st c =
  let span = W.open_span st in
  st.stmts <- span :: st.stmts;
  expr st c;
  st.stmts <- List.tl st.stmts;
  W.close_span st span

and if_ st c then_ alt =
  let start = Dynarray.length st.w.log in
  condition st c;
  let depth = List.length st.active in
  W.guard st (gives st c true) start;
  block st then_;
  W.truncate st depth;
  Option.iter
    (fun alt ->
      W.guard st (gives st c false) start;
      expr st alt;
      W.truncate st depth)
    alt

(* The operands of [&&], when [and_], or of [||]: the left one guards the right
   one, with its facts where it holds for [&&], and where it fails for [||]. *)
and operands st and_ a b =
  let start = Dynarray.length st.w.log in
  expr st a;
  let depth = List.length st.active in
  W.guard st (gives st a and_) start;
  expr st b;
  W.truncate st depth

(* A [while], whose condition guards its body, or a [loop]. *)
and looped st e c b =
  let span = W.open_span st in
  let id = W.id st in
  st.loops_in <- st.loops_in @ [ (id, span) ];
  let start = Dynarray.length st.w.log in
  let depth = List.length st.active in
  Option.iter
    (fun c ->
      condition st c;
      W.guard st (gives st c true) start)
    c;
  block st b;
  W.truncate st depth;
  st.loops_in <- List.filter (fun (i, _) -> i <> id) st.loops_in;
  W.close_span st span;
  st.w.looped <-
    { loop = e; lbody = st.current; cond = c; block = b; lspan = span }
    :: st.w.looped

and for_ st (p : pattern) iterable b =
  (match iterable with
  | Iter source -> expr st source
  | Range (a, z, _) ->
      expr st a;
      expr st z);
  let span = W.open_span st in
  let id = W.id st in
  st.loops_in <- st.loops_in @ [ (id, span) ];
  let ranges = st.ranges_in in
  (match (p.pat, iterable) with
  | P_bind v, Range (a, z, last) ->
      Hashtbl.replace st.w.decls v.id (st.current, W.Range_start a);
      Dynarray.add_last st.w.ranges
        {
          W.rbody = st.current;
          var = v;
          rstart = a;
          rend = z;
          inclusive = last = Ast.Inclusive;
          rspan = span;
        };
      st.ranges_in <- st.ranges_in @ [ Dynarray.length st.w.ranges - 1 ]
  | _ -> ());
  block st b;
  st.ranges_in <- ranges;
  st.loops_in <- List.filter (fun (i, _) -> i <> id) st.loops_in;
  W.close_span st span

(* Walks the code of a body, a function's block or a lone expression. *)
let run env ~constant ~self (code : [ `Block of block | `Expr of expr ]) =
  let w =
    {
      W.log = Dynarray.create ();
      spans = Dynarray.create ();
      frames = Dynarray.create ();
      ranges = Dynarray.create ();
      pending = [];
      looped = [];
      decls = Hashtbl.create 16;
      reader = { C.constant; whens = Hashtbl.create 4 };
    }
  in
  let st =
    {
      W.w;
      env;
      self;
      active = [];
      loops_in = [];
      stmts = [];
      ranges_in = [];
      stores = [];
      current = 0;
      bodies = 1;
      ids = 0;
    }
  in
  (match code with `Block b -> block st b | `Expr e -> expr st e);
  w.pending <- List.rev w.pending;
  w.looped <- List.rev w.looped;
  w
