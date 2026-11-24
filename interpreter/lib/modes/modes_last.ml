(* Last uses (facts.last-use): a use of a binding is its last use when no use
   of the binding follows it in source order and it isn't inside a loop that
   the binding's declaration is outside of. A use inside a closure literal
   counts as a use at the literal. *)

open Tast

type use = { var : int; tick : int; loops : int list; expr : expr }

(* The last uses, by their variable and position, which no two uses share. *)
type t = (int * Ast.loc, unit) Hashtbl.t

type state = {
  mutable tick : int;
  mutable loops : int list;
  mutable loop_count : int;
  mutable closure : (int * int list) option;
      (* The tick and loops of the outermost closure literal being walked. *)
  mutable uses : use list;
  decls : (int, int list) Hashtbl.t;
}

let declare st (p : pattern) =
  List.iter
    (fun id -> Hashtbl.replace st.decls id st.loops)
    (Modes_places.pattern_vars p)

let in_loop st f =
  let outer = st.loops in
  st.loop_count <- st.loop_count + 1;
  st.loops <- st.loop_count :: outer;
  f ();
  st.loops <- outer

let rec expr st (e : expr) =
  st.tick <- st.tick + 1;
  (match e.desc with
  | Local v ->
      let tick, loops = Option.value st.closure ~default:(st.tick, st.loops) in
      st.uses <- { var = v.id; tick; loops; expr = e } :: st.uses
  | _ -> ());
  match e.desc with
  | While (c, b) ->
      in_loop st (fun () ->
          expr st c;
          block st b)
  | Loop b -> in_loop st (fun () -> block st b)
  | For (p, iterable, b) ->
      (match iterable with
      | Iter source -> expr st source
      | Range (a, z, _) ->
          expr st a;
          expr st z);
      in_loop st (fun () ->
          declare st p;
          block st b)
  | Closure (ps, _, body) ->
      let outer = st.closure in
      if outer = None then st.closure <- Some (st.tick, st.loops);
      List.iter (declare st) ps;
      expr st body;
      st.closure <- outer
  | Match (_, arms) ->
      List.iter (fun (a : arm) -> declare st a.pattern) arms;
      parts st e
  | Try (_, catch) ->
      List.iter (fun (a : arm) -> declare st a.pattern) (Walk.catch_arms catch);
      parts st e
  | If_let (p, _, _, _) ->
      declare st p;
      parts st e
  | _ -> parts st e

and parts st e =
  List.iter
    (function Walk.Expr x -> expr st x | Block b -> block st b)
    (Walk.parts e)

and block st b =
  List.iter
    (fun (s : stmt) ->
      List.iter (expr st) (Walk.stmt_exprs s);
      match s.stmt with Let b | Var b -> declare st b.pattern | _ -> ())
    b

let compute b =
  let st =
    {
      tick = 0;
      loops = [];
      loop_count = 0;
      closure = None;
      uses = [];
      decls = Hashtbl.create 16;
    }
  in
  block st b;
  let latest = Hashtbl.create 16 in
  List.iter
    (fun u ->
      let seen = Option.value (Hashtbl.find_opt latest u.var) ~default:0 in
      Hashtbl.replace latest u.var (max seen u.tick))
    st.uses;
  let last u =
    let outside = Option.value (Hashtbl.find_opt st.decls u.var) ~default:[] in
    List.for_all (fun l -> List.mem l outside) u.loops
    && Hashtbl.find latest u.var <= u.tick
  in
  let t = Hashtbl.create 16 in
  List.iter
    (fun u -> if last u then Hashtbl.replace t (u.var, u.expr.loc) ())
    st.uses;
  t

let is_last t (e : expr) =
  match e.desc with Local v -> Hashtbl.mem t (v.id, e.loc) | _ -> false
