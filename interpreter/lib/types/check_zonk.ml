(* Elaborated code with every type of its nodes, and every row a call performs,
   replaced: by their solutions, or by a substitution's instances. *)

module T = Types
module A = Tast

type mapping = {
  ty : T.ty -> T.ty;
  row : T.row -> T.row;
  spec : A.expr -> string -> string;
  node : A.expr -> A.expr;
}

let rec map_expr m (e : A.expr) : A.expr =
  let e = m.node e in
  { e with ty = m.ty e.ty; desc = map_desc m e.desc }

and map_desc m (d : A.expr_desc) : A.expr_desc =
  let ex = map_expr m and ty = m.ty in
  let callee : A.callee -> A.callee = function
    | Trait_method (t, n, s) -> Trait_method (t, n, ty s)
    | c -> c
  in
  let arg (a : A.arg) = { a with value = ex a.value } in
  match d with
  | Int _ | Float _ | Str _ | Bool _ | Local _ | Value_param _ | Constant _
  | Hole | Error | Break | Continue ->
      d
  | Interpolated segs -> Interpolated (List.map (map_segment m) segs)
  | Member_constant (i, n, ts) -> Member_constant (i, n, List.map ty ts)
  | Trait_constant (t, n, s) -> Trait_constant (t, n, ty s)
  | Callee (c, ts) -> Callee (callee c, List.map ty ts)
  | Constructor (i, ts) -> Constructor (i, List.map ty ts)
  | Generalize (vs, e) -> Generalize (vs, ex e)
  | Instantiate (e, ts) -> Instantiate (ex e, List.map ty ts)
  | Construct (i, ts, es) -> Construct (i, List.map ty ts, List.map ex es)
  | Record (i, ts, fs) ->
      Record (i, List.map ty ts, List.map (fun (n, e) -> (n, ex e)) fs)
  | Update (b, fs) -> Update (ex b, List.map (fun (n, e) -> (n, ex e)) fs)
  | Spread s -> Spread { s with pack = ty s.pack; body = ex s.body }
  | Tuple es -> Tuple (List.map ex es)
  | List es -> List (List.map ex es)
  | Field (e, n) -> Field (ex e, n)
  | Tuple_field (e, i) -> Tuple_field (ex e, i)
  | Call (c, ts, args, row) ->
      Call (callee c, List.map ty ts, List.map arg args, m.row row)
  | Project (c, ts, args, row) ->
      Project (callee c, List.map ty ts, List.map arg args, m.row row)
  | Call_value (f, args) -> Call_value (ex f, List.map arg args)
  | Index (a, b) -> Index (ex a, ex b)
  | Unary (op, e) -> Unary (op, ex e)
  | Binary (op, a, b) -> Binary (op, ex a, ex b)
  | Else (a, b) -> Else (ex a, ex b)
  | Try (e, catch) -> Try (ex e, Option.map (map_catch m) catch)
  | Raise e -> Raise (ex e)
  | Return e -> Return (Option.map ex e)
  | Closure (ps, written, e) ->
      Closure (List.map (map_pattern m) ps, written, ex e)
  | Block b -> Block (map_block m b)
  | If (c, b, alt) -> If (ex c, map_block m b, Option.map ex alt)
  | If_let (p, s, b, alt) ->
      If_let (map_pattern m p, ex s, map_block m b, Option.map ex alt)
  | Match (s, arms) -> Match (ex s, List.map (map_arm m) arms)
  | Loop b -> Loop (map_block m b)
  | While (c, b) -> While (ex c, map_block m b)
  | For (p, it, b) -> For (map_pattern m p, map_iterable m it, map_block m b)
  | Handler h ->
      Handler { h with ops = List.map (fun (n, e) -> (n, ex e)) h.ops }
  | With (h, eff, args, b) -> With (ex h, eff, List.map ty args, map_block m b)
  | Resume e -> Resume (Option.map ex e)
  | When (names, b) ->
      When (List.map (fun (h, v) -> (ex h, v)) names, map_block m b)
  | Comptime e -> Comptime (ex e)
  | Reflect r -> Reflect (map_reflect m r)
  | Quote q -> Quote { q with splices = List.map (map_splice m) q.splices }

and map_segment m : A.segment -> A.segment = function
  | Text s -> Text s
  | Splice (e, s) -> Splice (map_expr m e, Option.map (m.spec e) s)

and map_splice m (s : A.splice) = { s with value = map_expr m s.value }

and map_reflect m : A.reflect -> A.reflect = function
  | Shape_of t -> Shape_of (m.ty t)
  | Name_of t -> Name_of (m.ty t)
  | Implements (t, bounds) ->
      Implements
        ( m.ty t,
          List.map
            (fun (b : T.bound) -> { b with args = List.map m.ty b.args })
            bounds )

and map_catch m (c : A.catch) =
  { A.error = m.ty c.error; arms = List.map (map_arm m) c.arms }

and map_iterable m : A.iterable -> A.iterable = function
  | Iter e -> Iter (map_expr m e)
  | Range (a, b, k) -> Range (map_expr m a, map_expr m b, k)

and map_arm m (a : A.arm) =
  {
    a with
    pattern = map_pattern m a.pattern;
    guard = Option.map (map_expr m) a.guard;
    body = map_expr m a.body;
  }

and map_block m b = List.map (map_stmt m) b

and map_stmt m (s : A.stmt) =
  let binding (b : A.binding) : A.binding =
    {
      pattern = map_pattern m b.pattern;
      written = b.written;
      value = map_expr m b.value;
      otherwise = Option.map (map_expr m) b.otherwise;
    }
  in
  let stmt : A.stmt_desc =
    match s.stmt with
    | Let b -> Let (binding b)
    | Var b -> Var (binding b)
    | Assign (op, p, v) -> Assign (op, map_expr m p, map_expr m v)
    | Yield e -> Yield (map_expr m e)
    | Assert e -> Assert (map_expr m e)
    | Expr e -> Expr (map_expr m e)
  in
  { s with stmt }

and map_pattern m (p : A.pattern) : A.pattern =
  let pat : A.pattern_desc =
    match p.pat with
    | P_tuple ps -> P_tuple (List.map (map_pattern m) ps)
    | P_const e -> P_const (map_expr m e)
    | P_variant (i, ps) -> P_variant (i, List.map (map_pattern m) ps)
    | P_record fs -> P_record (List.map (fun (n, p) -> (n, map_pattern m p)) fs)
    | P_list (ps, r) -> P_list (List.map (map_pattern m) ps, r)
    | P_or ps -> P_or (List.map (map_pattern m) ps)
    | d -> d
  in
  { p with pat; pty = m.ty p.pty }

let same _ s = s
let map_expr ~ty ~row e = map_expr { ty; row; spec = same; node = Fun.id } e

let map_block ?(spec = same) ?(node = Fun.id) ~ty ~row b =
  map_block { ty; row; spec; node } b

let zonk = { ty = T.zonk; row = Fun.id; spec = same; node = Fun.id }
let zonk_expr e = map_expr ~ty:zonk.ty ~row:zonk.row e
let zonk_block b = map_block ~ty:zonk.ty ~row:zonk.row b
