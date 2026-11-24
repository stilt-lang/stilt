type mode = Ast.mode
type kind = Any | Int_literal | Float_literal

type ty =
  | Con of Hir.item * ty list
  | Param of Hir.var
  | Tuple of ty list
  | Record of (string * ty) list
  | Spread of ty * ty
  | Fn of (mode * ty) list * ty * row
  | App of ty * ty list
  | Forall of forall
  | Handler of handler
  | Var of var
  | Value of string
  | Error

and handler = {
  eff : Hir.item;
  hargs : ty list;
  answer : ty option;
  hrow : row;
}

and forall = { generics : (Hir.var * bound list) list; body : ty }
and bound = { trait : Hir.item; args : ty list }

and var = {
  id : int;
  kind : kind;
  origin : Ast.loc;
  mutable solution : ty option;
  mutable tainted : bool;
  mutable level : int;
}

and row = {
  io : bool;
  raise : ty option;
  effects : (Hir.item * ty list) list;
  tail : tail;
}

and tail = Closed | Row_params of row_param list | Row_var of row_var
and row_param = { var : Hir.var; implicit : bool }

and row_var = {
  mutable state : row_state;
  mutable uppers : (row * handled) list;
  least : bool;
}

and row_state = Open of row | Link of row
and handled = Nothing | Raise_of of ty | Effect_of of Hir.item * ty list

(* Built-in types *)

let prelude_item name = { Hir.home = "std.prelude"; name }
let named name = Con (prelude_item name, [])
let never = named "Never"
let unit = Tuple []
let bool = named "bool"
let str = named "str"
let i64 = named "i64"
let f64 = named "f64"
let list t = Con (prelude_item "List", [ t ])
let map k v = Con (prelude_item "Map", [ k; v ])
let option t = Con (prelude_item "Option", [ t ])
let integer_types = [ "i8"; "i16"; "i32"; "i64"; "u8"; "u16"; "u32"; "u64" ]
let float_types = [ "f32"; "f64" ]

(* Variables *)

let counter = ref 0

let fresh ?(kind = Any) origin =
  incr counter;
  Var
    {
      id = !counter;
      kind;
      origin;
      solution = None;
      tainted = false;
      level = !counter;
    }

let empty_row = { io = false; raise = None; effects = []; tail = Closed }

let fresh_row ?(least = false) () =
  {
    empty_row with
    tail = Row_var { state = Open empty_row; uppers = []; least };
  }

(* records.anonymous-types: an anonymous record type, its fields in the alphabetical
   order of their names, by their bytes (records.field-order), whatever order they are
   written in. *)
let record fields =
  Record (List.stable_sort (fun (a, _) (b, _) -> String.compare a b) fields)

(* The item that an anonymous record's values and literals name, which no
   module declares (records.no-home). *)
let anonymous = { Hir.home = "std.prelude"; name = "{}" }

(* tasks.async: the effect [async], a keyword, which no module declares. *)
let async_effect = { Hir.home = "std.prelude"; name = "async" }

(* The effects of a row with each argument mapped by [f]. *)
let map_effects f effects =
  List.map (fun (e, args) -> (e, List.map f args)) effects

let effect_types (r : row) = List.concat_map snd r.effects

(* The last variable of a chain of solved variables, or the type itself, so
   that a pack is found inside a spread's body before its solution
   replaces it. *)
let rec representative = function
  | Var { solution = Some (Var _ as next); _ } -> representative next
  | t -> t

let same_pack pack t =
  match (representative pack, representative t) with
  | Var a, Var b -> a == b
  | Param p, Param q -> p.id = q.id
  | _ -> false

(* [replace pack by t]: [t] with [by] in place of the pack [pack], a type
   parameter or a variable. *)
let rec replace pack by t =
  if same_pack pack t then by
  else
    let go = replace pack by in
    match t with
    | Var { solution = Some s; _ } -> go s
    | Var _ | Param _ | Value _ | Error -> t
    | Con (item, ts) -> Con (item, List.map go ts)
    | Tuple ts -> Tuple (List.map go ts)
    | Record fields -> Record (List.map (fun (f, t) -> (f, go t)) fields)
    | Spread (p, body) -> Spread (go p, go body)
    | App (h, ts) -> App (go h, List.map go ts)
    | Fn (ps, ret, row) ->
        Fn (List.map (fun (m, t) -> (m, go t)) ps, go ret, row_by go row)
    | Handler h ->
        Handler
          {
            h with
            hargs = List.map go h.hargs;
            answer = Option.map go h.answer;
            hrow = row_by go h.hrow;
          }
    | Forall p -> Forall { p with body = go p.body }

and row_by go row =
  {
    row with
    raise = Option.map go row.raise;
    effects = map_effects go row.effects;
  }

(* variadics.type-spreads: a spread whose pack is known stands for one element for
   each of the pack's, with the pack replaced by that element. An element
   that is itself a spread, of another pack, gives a spread of that pack. *)
let rec expand ts = List.concat_map expand_one ts

and expand_one t =
  match t with
  | Spread (pack, body) -> (
      match resolve pack with
      | Tuple es -> List.map (element pack body) es
      | _ -> [ t ])
  | t -> [ t ]

(* The element of a spread of [pack] over [body] at the pack's element
   [e]. *)
and element pack body = function
  | Spread (q, b) -> Spread (q, replace pack b body)
  | e -> replace pack e body

and solved_spread = function
  | Spread (pack, _) -> (
      match resolve pack with Tuple _ -> true | _ -> false)
  | _ -> false

(* traits.constructor-parameters: a constructor applied to arguments is the type it makes
   once its head is a named type constructor. A head that is no constructor,
   such as a tuple that a call's argument gives a constructor parameter,
   makes the error type, whose bound the call reports (E0318). A tuple or a
   function type whose spreads' packs are known has their elements in their
   place (variadics.type-spreads). *)
and resolve = function
  | Var { solution = Some t; _ } -> resolve t
  | App (head, args) as t -> (
      match resolve head with
      | Con (item, []) -> Con (item, args)
      | (Param _ | Var _) as h -> if h == head then t else App (h, args)
      | Con _ | Tuple _ | Record _ | Spread _ | Fn _ | Forall _ | App _
      | Handler _ | Value _ | Error ->
          Error)
  | Tuple ts when List.exists solved_spread ts -> Tuple (expand ts)
  | Fn (ps, ret, row) when List.exists (fun (_, t) -> solved_spread t) ps ->
      Fn (expand_params ps, ret, row)
  | t -> t

and expand_params ps =
  List.concat_map (fun (m, t) -> List.map (fun t -> (m, t)) (expand_one t)) ps

(* [App (head, args)] once [head] is replaced. *)
let apply head args =
  match resolve head with
  | Con (item, []) -> Con (item, args)
  | (Param _ | Var _) as h -> App (h, args)
  | Con _ | Tuple _ | Record _ | Spread _ | Fn _ | Forall _ | App _ | Handler _
  | Value _ | Error ->
      Error

(* A match on the names, not a search of the lists, since the evaluator asks
   at every arithmetic operation. *)
let numeric_name t =
  match resolve t with
  | Con
      ( {
          home = "std.prelude";
          name =
            ( "i8" | "i16" | "i32" | "i64" | "u8" | "u16" | "u32" | "u64"
            | "f32" | "f64" ) as name;
        },
        [] ) ->
      Some name
  | _ -> None

type var_info = { id : int; kind : kind; origin : Ast.loc; tainted : bool }

let origin = function Var { origin; _ } -> Some origin | _ -> None

let unsolved t =
  match resolve t with
  | Var { id; kind; origin; solution = None; tainted } ->
      Some { id; kind; origin; tainted }
  | _ -> None

let rec row_contents r =
  match r.tail with
  | Closed | Row_params _ -> r
  | Row_var { state = Link linked; _ } -> merge_labels (row_contents linked) r
  | Row_var { state = Open added; _ } -> merge_labels (row_contents added) r

(* Adds the labels of [extra] to [r]. Where both raise, the type of [r] is
   kept: the checker unifies the two before rows meet. *)
and merge_labels r extra =
  {
    r with
    io = r.io || extra.io;
    raise = (match r.raise with Some _ -> r.raise | None -> extra.raise);
    effects =
      r.effects
      @ List.filter
          (fun (e, _) -> not (List.mem_assoc e r.effects))
          extra.effects;
  }

let find_effect e r = List.assoc_opt e (row_contents r).effects

let without_effect e r =
  { r with effects = List.filter (fun (f, _) -> f <> e) r.effects }

(* Applies [f] to each unsolved variable of [t]. *)
let rec unsolved_vars f t =
  match resolve t with
  | Var ({ solution = None; _ } as var) -> f var
  | Con (_, ts) | Tuple ts -> List.iter (unsolved_vars f) ts
  | Record fields -> List.iter (fun (_, t) -> unsolved_vars f t) fields
  | App (h, ts) -> List.iter (unsolved_vars f) (h :: ts)
  | Spread (p, t) -> List.iter (unsolved_vars f) [ p; t ]
  | Fn (params, ret, row) ->
      List.iter (fun (_, t) -> unsolved_vars f t) params;
      unsolved_vars f ret;
      row_vars f row
  | Handler h ->
      List.iter (unsolved_vars f) (h.hargs @ Option.to_list h.answer);
      row_vars f h.hrow
  | Forall p -> unsolved_vars f p.body
  | Var _ | Param _ | Value _ | Error -> ()

and row_vars f row =
  let r = row_contents row in
  List.iter (unsolved_vars f) (Option.to_list r.raise @ effect_types r)

let taint = unsolved_vars (fun var -> var.tainted <- true)

let solve v t =
  match resolve v with
  | Var ({ solution = None; tainted; level; _ } as var) ->
      var.solution <- Some t;
      if tainted then taint t;
      (* What [v] stands for is as old as [v]: the variables of [t] now stand
         for parts of a type made before them. *)
      unsolved_vars (fun w -> w.level <- min w.level level) t
  | _ -> invalid_arg "Types.solve"

let rec type_params t =
  let inside = List.concat_map type_params in
  match resolve t with
  | Param p -> [ p ]
  | Con (_, ts) | Tuple ts -> inside ts
  | Record fields -> inside (List.map snd fields)
  | App (h, ts) -> inside (h :: ts)
  | Spread (p, t) -> inside [ p; t ]
  | Fn (params, ret, row) ->
      let r = row_contents row in
      inside
        ((ret :: List.map snd params) @ Option.to_list r.raise @ effect_types r)
  | Handler h ->
      let r = row_contents h.hrow in
      inside
        (h.hargs @ Option.to_list h.answer @ Option.to_list r.raise
       @ effect_types r)
  | Forall p -> type_params p.body
  | Var _ | Value _ | Error -> []

(* polymorphism.rigid-types: each rigid type, by id, with the number of variables made
   before it, none of which may come to stand for a type that holds it. *)
let births : (int, int) Hashtbl.t = Hashtbl.create 16

let rigid (v : Hir.var) =
  Hashtbl.replace births v.id !counter;
  Param v

let is_rigid (v : Hir.var) = Hashtbl.mem births v.id

let would_escape v t =
  match resolve v with
  | Var a when Hashtbl.length births > 0 ->
      List.exists
        (fun (p : Hir.var) ->
          match Hashtbl.find_opt births p.id with
          | Some born -> a.level <= born
          | None -> false)
        (type_params t)
  | _ -> false

(* Rows *)

let row_state rv = rv.state
let set_row_state rv state = rv.state <- state
let uppers rv = rv.uppers
let least rv = rv.least

let add_upper rv bound =
  if not (List.memq bound rv.uppers) then rv.uppers <- rv.uppers @ [ bound ]

let rec is_open r =
  match r.tail with
  | Closed | Row_params _ -> false
  | Row_var { state = Open _; _ } -> true
  | Row_var { state = Link linked; _ } -> is_open linked

(* Traversals *)

let rec zonk t =
  match resolve t with
  | Con (item, args) -> Con (item, List.map zonk args)
  | Tuple ts -> Tuple (List.map zonk ts)
  | Record fields -> Record (List.map (fun (f, t) -> (f, zonk t)) fields)
  | Spread (p, t) -> Spread (zonk p, zonk t)
  | Fn (params, ret, row) ->
      Fn (List.map (fun (m, t) -> (m, zonk t)) params, zonk ret, zonk_row row)
  | Handler h ->
      Handler
        {
          h with
          hargs = List.map zonk h.hargs;
          answer = Option.map zonk h.answer;
          hrow = zonk_row h.hrow;
        }
  | App (h, args) -> App (zonk h, List.map zonk args)
  | Forall p ->
      Forall { generics = List.map zonk_generic p.generics; body = zonk p.body }
  | (Param _ | Var _ | Value _ | Error) as t -> t

and zonk_generic (v, bounds) =
  (v, List.map (fun b -> { b with args = List.map zonk b.args }) bounds)

and zonk_row r =
  let r = if is_open r then r else row_contents r in
  {
    r with
    raise = Option.map zonk r.raise;
    effects = map_effects zonk r.effects;
  }

let rec occurs v t =
  match resolve t with
  | Var b -> ( match resolve v with Var a -> a == b | _ -> false)
  | Con (_, ts) | Tuple ts -> List.exists (occurs v) ts
  | Record fields -> List.exists (fun (_, t) -> occurs v t) fields
  | App (h, ts) -> List.exists (occurs v) (h :: ts)
  | Spread (p, t) -> occurs v p || occurs v t
  | Fn (params, ret, row) ->
      List.exists (fun (_, t) -> occurs v t) params
      || occurs v ret
      || row_has (occurs v) row
  | Handler h ->
      List.exists (occurs v) (h.hargs @ Option.to_list h.answer)
      || row_has (occurs v) h.hrow
  | Forall p -> occurs v p.body
  | Param _ | Value _ | Error -> false

(* Whether a type of the row's labels, its raise or its effects' arguments,
   meets [p]. *)
and row_has p row =
  let r = row_contents row in
  List.exists p (Option.to_list r.raise @ effect_types r)

let rec row_occurs rv t =
  match resolve t with
  | Con (_, ts) | Tuple ts -> List.exists (row_occurs rv) ts
  | Record fields -> List.exists (fun (_, t) -> row_occurs rv t) fields
  | App (h, ts) -> List.exists (row_occurs rv) (h :: ts)
  | Spread (_, t) -> row_occurs rv t
  | Fn (params, ret, row) ->
      List.exists (fun (_, t) -> row_occurs rv t) params
      || row_occurs rv ret || row_mentions rv row
  | Handler h ->
      List.exists (row_occurs rv) (h.hargs @ Option.to_list h.answer)
      || row_mentions rv h.hrow
  | Forall p -> row_occurs rv p.body
  | Param _ | Var _ | Value _ | Error -> false

and row_mentions rv r =
  List.exists (row_occurs rv) (Option.to_list r.raise @ effect_types r)
  ||
  match r.tail with
  | Row_var v when v == rv -> true
  | Row_var { state = Link linked | Open linked; _ } -> row_mentions rv linked
  | Closed | Row_params _ -> false

let rec mentions_error t =
  match resolve t with
  | Error -> true
  | Con (_, ts) | Tuple ts -> List.exists mentions_error ts
  | Record fields -> List.exists (fun (_, t) -> mentions_error t) fields
  | App (h, ts) -> List.exists mentions_error (h :: ts)
  | Spread (p, t) -> mentions_error p || mentions_error t
  | Fn (params, ret, row) ->
      List.exists (fun (_, t) -> mentions_error t) params
      || mentions_error ret || row_has mentions_error row
  | Handler h ->
      List.exists mentions_error (h.hargs @ Option.to_list h.answer)
      || row_has mentions_error h.hrow
  | Forall p -> mentions_error p.body
  | Param _ | Var _ | Value _ -> false

(* Row parameters *)

let params r =
  match (row_contents r).tail with
  | Row_params ps -> ps
  | Closed | Row_var _ -> []

let has_param ps (p : row_param) =
  List.exists (fun (q : row_param) -> q.var.id = p.var.id) ps

let union_params ps qs = ps @ List.filter (fun q -> not (has_param ps q)) qs
let params_tail = function [] -> Closed | ps -> Row_params ps
