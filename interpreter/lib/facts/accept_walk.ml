(* The walk of a body's code in the order it is written, which records what
   the rules of acceptance read (facts.acceptance-places): the writes of each body's
   own code, the tests that guard each operation, the loops and the statement
   that hold it, and the [for] loops over ranges around it. Each closure
   literal's body is a body of its own, with a number. *)

open Tast
module C = Accept_code

type write_kind = Assign of Ast.binary option | Inout | Insert | Yield

type write = {
  body : int;
  root : int;
  fields : string list;
  indexed : bool;
  kind : write_kind;
  value : expr option;
  place : expr;
  line : int;
}

let rec prefix a b =
  match (a, b) with
  | [], _ -> true
  | x :: a, y :: b -> x = y && prefix a b
  | _ :: _, [] -> false

let changes w (p : C.place) =
  (not w.indexed) && w.root = p.root && prefix w.fields p.fields

let unstores w (p : C.place) =
  changes w p && not (w.kind = Insert && w.fields = p.fields)

type frame = { atoms : C.atom list; start : int; id : int }
type span = { mutable first : int; mutable last : int }

type range = {
  rbody : int;
  var : Hir.var;
  rstart : expr;
  rend : expr;
  inclusive : bool;
  rspan : int;
}

type op = Index of expr * expr | Division of expr | Self_call of arg list

type pending = {
  op : op;
  node : expr;
  pbody : int;
  log_at : int;
  frames : int list;
  loops : (int * int) list;
  stmt : int option;
  ranges : int list;
}

type looped = {
  loop : expr;
  lbody : int;
  cond : expr option;
  block : block;
  lspan : int;
}

type declared = Let_init of expr | Var_init of expr | Range_start of expr

type t = {
  log : write Dynarray.t;
  spans : span Dynarray.t;
  frames : frame Dynarray.t;
  ranges : range Dynarray.t;
  mutable pending : pending list;
  mutable looped : looped list;
  decls : (int, int * declared) Hashtbl.t;
  reader : C.reader;
}

type state = {
  w : t;
  env : Env.t;
  self : Implicit_names.key option;
  mutable active : int list;
  mutable loops_in : (int * int) list;
  mutable stmts : int list;
  mutable ranges_in : int list;
  mutable stores : expr list;
  mutable current : int;
  mutable bodies : int;
  mutable ids : int;
}

let in_span (w : t) body span =
  let s = Dynarray.get w.spans span in
  List.filter
    (fun (x : write) -> x.body = body)
    (List.init (s.last - s.first) (fun i -> Dynarray.get w.log (s.first + i)))

(* The writes between a frame and an operation: those since its test, those of
   the loops inside its code that hold the operation, and those of the
   statement that holds it. *)
let between (w : t) frame (p : pending) =
  let f = Dynarray.get w.frames frame in
  let since =
    List.filter
      (fun (x : write) -> x.body = p.pbody)
      (List.init (p.log_at - f.start) (fun i ->
           Dynarray.get w.log (f.start + i)))
  in
  let loops =
    List.concat_map
      (fun (id, span) -> if id > f.id then in_span w p.pbody span else [])
      p.loops
  in
  let stmt = Option.fold ~none:[] ~some:(in_span w p.pbody) p.stmt in
  since @ loops @ stmt

(* The innermost frame guarding [p] that gives a fact [holds] accepts. *)
let frame (w : t) (p : pending) holds =
  List.find_opt
    (fun f -> List.exists holds (Dynarray.get w.frames f).atoms)
    (List.rev p.frames)

(* The line of the first of the writes [f] accepts. *)
let first writes f =
  List.fold_left
    (fun acc (x : write) ->
      if f x then Some (Option.fold ~none:x.line ~some:(min x.line) acc)
      else acc)
    None writes

let id st =
  st.ids <- st.ids + 1;
  st.ids

let open_span st =
  let at = Dynarray.length st.w.log in
  Dynarray.add_last st.w.spans { first = at; last = at };
  Dynarray.length st.w.spans - 1

let close_span st span =
  (Dynarray.get st.w.spans span).last <- Dynarray.length st.w.log

let guard st atoms start =
  if atoms <> [] then (
    let id = id st in
    Dynarray.add_last st.w.frames { atoms; start; id };
    st.active <- st.active @ [ Dynarray.length st.w.frames - 1 ])

let truncate st depth =
  st.active <- List.filteri (fun i _ -> i < depth) st.active

let pend st op node =
  st.w.pending <-
    {
      op;
      node;
      pbody = st.current;
      log_at = Dynarray.length st.w.log;
      frames = st.active;
      loops = st.loops_in;
      stmt = (match st.stmts with s :: _ -> Some s | [] -> None);
      ranges = st.ranges_in;
    }
    :: st.w.pending

(* The binding that roots a place, the fields after it before any index or
   tuple's element, and whether one follows them. *)
let rec path (e : expr) =
  match e.desc with
  | Local v -> Some (v.id, [], false)
  | Field (base, name) ->
      Option.map
        (fun (root, fields, indexed) ->
          (root, (if indexed then fields else fields @ [ name ]), indexed))
        (path base)
  | Index (base, _) | Tuple_field (base, _) ->
      Option.map (fun (root, fields, _) -> (root, fields, true)) (path base)
  | _ -> None

let write st (place : expr) kind value =
  Option.iter
    (fun (root, fields, indexed) ->
      Dynarray.add_last st.w.log
        {
          body = st.current;
          root;
          fields;
          indexed;
          kind;
          value;
          place;
          line = place.loc.line;
        })
    (path place)
