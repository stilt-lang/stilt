open Model_json
open Model_types
open Model_ops
open Model_forms

(* Views that write in the Lean model's calculus (formal/Stilt/Writable.lean). A writable
   binding and the rest of its block are the call that the binding is, a form of the
   calculus, [["writes", call]]: the rest is the body of a closure literal whose first
   parameter takes the binding's source [inout], and the closure is called with the
   source's place. The binding stands for that parameter and its part's start and end, so
   [v[i]] is a place of the parameter, at the index that [["through", j, start, end, i]]
   gives. The closure's further parameters take the variables the rest modifies, [inout]
   under their own names, since a closure captures by copy (expressions.capture). So
   copy-in, copy-out writes the part back into the source when the scope ends, however it
   ends, and in place the binding writes the source's storage at once
   (projections.writable-views and projections.what-view-writes). *)

type callbacks = {
  expr : Tast.expr -> Model_json.t;
  block : Tast.block -> Model_json.t;
}

let owns (i : Hir.item) =
  i.home = "std.view" && List.mem i.name [ "into"; "part"; "split" ]

let i64 = prelude_ty "i64"
let list_op name operands = op (tag "list" [ Str name ]) operands
let add a b = op (tag "arith" [ Str "add"; Str "i64" ]) [ a; b ]
let int n = tag "int" [ Str (string_of_int n) ]

let bound lets body =
  List.fold_right
    (fun (n, t, init) b -> tag "letIn" [ Str n; t; init; b ])
    lets body

(* The source of a view made through [inout]: its type, a list's, its index expressions'
   temporaries, how a value is stored into it, and the expression that reads it. *)
let source cb cx (src : Tast.expr) =
  let t = match Model_views.viewed src.ty with Some t -> t | None -> src.ty in
  let lets, store, read = Model_places.receiver ~expr:cb.expr cx src in
  (t, lets, store, read)

(* What a writable binding reads: the view of its part. *)
let part_of (w : writable) =
  Model_views.view [ var_e w.src; var_e w.start; var_e w.stop ]

(* Each part, a variable and its offset, written back into the source, which is then
   stored. *)
let written_back cx loc t store read parts =
  let w = temp "written" loc in
  let copy (p, at) rest =
    let j = temp "element" loc in
    let range = tag "list" [ tag "range" [ Bool false ] ] in
    let each = op range [ int 0; list_op "len" [ var_e p ] ] in
    let target = Arr [ Str w; Arr [ tag "index" [ add at (var_e j) ] ] ] in
    let put = tag "assign" [ target; tag "index" [ var_e p; var_e j ] ] in
    tag "seq" [ tag "for" [ Str j; ty cx i64; each; put ]; rest ]
  in
  tag "varIn"
    [
      Str w;
      ty cx t;
      read;
      List.fold_right copy parts (Model_places.write store (var_e w));
    ]

(* The error types that code may raise, outside its closure literals: those of its
   [raise]s and of the rows of its calls. *)
let rec raised (e : Tast.expr) =
  let row (r : Types.row) = Option.to_list (Types.row_contents r).raise in
  let own =
    match e.desc with
    | Raise x -> [ x.ty ]
    | Call (_, _, _, r) -> row r
    | Call_value (f, _) -> (
        match norm f.ty with Fn (_, _, r) -> row r | _ -> [])
    | _ -> []
  in
  match e.desc with
  | Closure _ | Handler _ -> []
  | _ -> own @ List.concat_map raised (Walk.children e)

(* The one error type that code may raise, if any. *)
let raise_of cx (es : Tast.expr list) =
  match List.concat_map raised es with
  | [] -> None
  | t :: ts ->
      let key t = Model_json.to_string (ty cx t) in
      if List.for_all (fun u -> key u = key t) ts then Some t
      else outside "a writable view's scope that raises errors of two types"

(* [body], of type [rt], then [back], which a raise of [err] in [body] runs before it
   leaves. *)
let around cx loc rt err body back =
  let r = temp "scope" loc in
  let ended =
    tag "letIn" [ Str r; ty cx rt; body; tag "seq" [ back; var_e r ] ]
  in
  match err with
  | None -> ended
  | Some err ->
      let x = temp "raised" loc in
      let again = tag "seq" [ back; tag "raise" [ var_e x ] ] in
      tag "tryCatch" [ ended; ty cx err; Str x; again; ty cx rt ]

(* Whether code jumps out of a block: a [return], or a [break] or a [continue] of a loop
   outside it. *)
let rec jumps_out ~in_loop (e : Tast.expr) =
  match e.desc with
  | Return _ -> true
  | Break | Continue -> not in_loop
  | Closure _ | Handler _ -> false
  | Loop _ | While _ | For _ ->
      List.exists (jumps_out ~in_loop:true) (Walk.children e)
  | _ -> List.exists (jumps_out ~in_loop) (Walk.children e)

let no_jumps (b : Tast.block) =
  if List.exists (jumps_out ~in_loop:false) (Walk.block_exprs b) then
    outside "a jump out of a writable view's scope"

(* The variable a place is rooted in, by its name in the calculus, with its type: a
   writable binding's is its source's parameter. *)
let rec root cx (e : Tast.expr) =
  match e.desc with
  | Local v -> (
      match writable_of cx v with
      | Some w -> Some (w.src, w.part)
      | None -> Some (var_name v, e.ty))
  | Field (b, _) | Tuple_field (b, _) | Index (b, _) -> root cx b
  | _ -> None

(* The variables that a block modifies and doesn't bind, each once with its type: the
   roots of the places it assigns to and passes [inout]. A [yield] or a [resume] in it
   would leave the closure that the scope is. *)
let modified cx (b : Tast.block) =
  let bound = ref [] and changed = ref [] in
  let bind p = List.iter (fun (v, _) -> bound := var_name v :: !bound) p in
  let change (e : Tast.expr) =
    match root cx e with
    | Some (n, t) when not (List.mem_assoc n !changed) ->
        changed := !changed @ [ (n, t) ]
    | _ -> ()
  in
  let inouts args =
    List.iter (fun (a : Tast.arg) -> if a.mode = Inout then change a.value) args
  in
  let stmt (s : Tast.stmt) =
    match s.stmt with
    | Let b | Var b -> bind (typed_binders b.pattern)
    | Assign (_, p, _) -> change p
    | Yield _ -> outside "a yield in a writable view's scope"
    | _ -> ()
  in
  let one (e : Tast.expr) =
    match e.desc with
    | Call (_, _, args, _) | Project (_, _, args, _) | Call_value (_, args) ->
        inouts args
    | Closure (ps, _, _) -> List.iter (fun p -> bind (typed_binders p)) ps
    | For (p, _, _) | If_let (p, _, _, _) -> bind (typed_binders p)
    | Match (_, arms) | Try (_, Some { arms; _ }) ->
        List.iter (fun (a : Tast.arm) -> bind (typed_binders a.pattern)) arms
    | When (pairs, _) ->
        List.iter (fun (_, v) -> bound := var_name v :: !bound) pairs
    | Resume _ -> outside "a resume in a writable view's scope"
    | _ -> ()
  in
  Walk.iter_block ~stmt one b;
  List.filter (fun (n, _) -> not (List.mem n !bound)) !changed

(* The scope of the writable binding [v], [rest], as the call it is: the closure literal
   that takes the source [inout] as [w.src] and the variables [rest] modifies, called
   with the source's place [place], rooted in [src_root], and those variables, marked
   when the row the code may perform raises (effects.marking). *)
let scope cb cx (v : Hir.var) (w : writable) ~src_root place rest =
  no_jumps rest;
  let threaded =
    List.filter (fun (n, _) -> n <> var_name v) (modified cx rest)
  in
  if List.mem_assoc src_root threaded then
    outside "a writable view's scope that writes the root of its source";
  let saved = cx.writable in
  bind_writable cx v w;
  let body =
    Fun.protect
      ~finally:(fun () -> cx.writable <- saved)
      (fun () -> cb.block rest)
  in
  let param (n, t) = Arr [ Str "inout"; Str n; ty cx t; Null ] in
  let params = param (w.src, w.part) :: List.map param threaded in
  let rt = block_ty rest in
  let closure =
    tag "closure" [ Arr params; ty cx rt; row cx cx.allowed; body ]
  in
  let pass (n, _) = tag "inout" [ Arr [ Str n; Arr [] ] ] in
  let args = tag "inout" [ place ] :: List.map pass threaded in
  let call = tag "writes" [ call_e cx closure args rt ] in
  if snd (flat cx.allowed) <> None then tag "try" [ call ] else call

(* Whether a parameter's type gives a call's result of a view type a source: a viewable
   type or a view type, a function type among them (views.across-calls). *)
let gives_source t =
  match norm t with
  | Types.Con ({ home = "std.prelude"; name = "List" | "str" }, _) -> true
  | Types.Con ({ home = "std.prelude"; name = "Option" }, [ u ]) ->
      viewed u <> None
  | Fn _ -> true
  | t -> viewed t <> None

(* The position of the one parameter whose argument a function's result writes, when the
   result is a view of a list and that parameter is the one source passed [inout]: the
   calculus writes such a function as one that gives the part's start and end in that
   argument, and its result must be a view of that parameter made through [inout]
   (projections.results-that-write). *)
let result_writes (params : (Ast.mode * Types.ty) list) ret =
  match Option.map norm (viewed ret) with
  | Some (Types.Con ({ home = "std.prelude"; name = "List" }, [ _ ])) -> (
      let sources =
        List.filter
          (fun (_, (m, t)) -> m = Ast.Inout && gives_source t)
          (List.mapi (fun i p -> (i, p)) params)
      in
      match sources with [ (i, _) ] -> Some i | _ -> None)
  | _ -> None

let target_writes cx target =
  let s = Model_fns.signature cx target in
  result_writes s.params s.ret

let offsets_ty = Types.Tuple [ i64; i64 ]

(* A view made through [inout], which a writable binding or a [yield] takes: [wrap]
   evaluates its operands and checks its offsets around the code it is given, [place] is
   its source's place, rooted in [root], [read] reads the source, and [start] and [stop]
   hold its part's start and end in it, of the viewed type [part]. *)
type made = {
  wrap : Model_json.t -> Model_json.t;
  place : Model_json.t;
  root : string;
  read : Model_json.t;
  start : string;
  stop : string;
  part : Types.ty;
}

(* The source of a view made through [inout], as a place: a writable binding's is its
   source's parameter, whole. *)
let inout_source cb cx (src : Tast.expr) =
  match src.desc with
  | Local u when writable_of cx u <> None ->
      let o = Option.get (writable_of cx u) in
      ([], Arr [ Str o.src; Arr [] ], o.src, part_of o, o.part)
  | _ -> (
      let t, lets, store, read = source cb cx src in
      let root = match root cx src with Some (n, _) -> n | None -> "" in
      match store with
      | Model_places.Path p -> (lets, p, root, read, t)
      | Model_places.Through _ -> outside "a writable view of a map's element")

(* [view.into(inout src, a, b)] and [view.part(inout src, a, b)]: the offsets evaluated,
   then the source read as the call starts and checked as [View.of] checks it, a view of a
   writable binding counting its offsets from the binding's start
   (projections.writable-views and values.inout-argument-order). *)
let made_through cb cx (init : Tast.expr) (src : Tast.expr) (a : Tast.arg)
    (b : Tast.arg) =
  let start = temp "start" a.value.loc and stop = temp "end" b.value.loc in
  let offsets =
    [ (start, ty cx i64, cb.expr a.value); (stop, ty cx i64, cb.expr b.value) ]
  in
  let lets, place, root, read, part = inout_source cb cx src in
  match src.desc with
  | Local u when writable_of cx u <> None ->
      let o = Option.get (writable_of cx u) in
      let s = temp "part-start" init.loc and e = temp "part-end" init.loc in
      let check = Model_views.view [ read; var_e start; var_e stop ] in
      let ends =
        [
          (s, ty cx i64, add (var_e o.start) (var_e start));
          (e, ty cx i64, add (var_e o.start) (var_e stop));
        ]
      in
      let wrap body = bound offsets (tag "seq" [ check; bound ends body ]) in
      { wrap; place; root; read = var_e o.src; start = s; stop = e; part }
  | _ ->
      let check = Model_views.view [ read; var_e start; var_e stop ] in
      let wrap body = bound (lets @ offsets) (tag "seq" [ check; body ]) in
      { wrap; place; root; read; start; stop; part }

(* A call of a function whose result writes its [k]th argument: the arguments evaluated in
   their turn into temporaries, the call, which gives the part's start and end in that
   argument's place, and those. *)
let made_by_call cb cx (e : Tast.expr) target targs (args : Tast.arg list) k =
  let one j (lets, passed, src) (a : Tast.arg) =
    match (a.mode, a.value.desc) with
    | Inout, Local u when writable_of cx u <> None ->
        let w = Option.get (writable_of cx u) in
        let here =
          [
            tag "inout" [ Arr [ Str w.src; Arr [] ] ];
            tag "value" [ var_e w.start ];
            tag "value" [ var_e w.stop ];
          ]
        in
        let mine = (Arr [ Str w.src; Arr [] ], w.src, var_e w.src, w.part) in
        (lets, passed @ here, if j = k then Some mine else src)
    | Inout, _ ->
        let ls, place, root, read, part = inout_source cb cx a.value in
        let mine = (place, root, read, part) in
        ( lets @ ls,
          passed @ [ tag "inout" [ place ] ],
          if j = k then Some mine else src )
    | Let, _ ->
        let n = Printf.sprintf "%s/%d" (temp "argument" e.loc) j in
        let lets = lets @ [ (n, ty cx a.value.ty, cb.expr a.value) ] in
        (lets, passed @ [ tag "value" [ var_e n ] ], src)
  in
  let lets, passed, src =
    List.fold_left
      (fun acc (j, a) -> one j acc a)
      ([], [], None)
      (List.mapi (fun j a -> (j, a)) args)
  in
  let place, root, read, part = Option.get src in
  let types = List.map (fun (a : Tast.arg) -> a.value.ty) args in
  let inst = Model_fns.instance cx target targs types in
  let f = tag "fnRef" [ Str inst.fkey; Arr []; Arr [] ] in
  let o = temp "offsets" e.loc in
  let start = o ^ "/start" and stop = o ^ "/end" in
  let ends =
    [
      (o, ty cx offsets_ty, call_e cx f passed offsets_ty);
      (start, ty cx i64, tag "field" [ var_e o; Str "0" ]);
      (stop, ty cx i64, tag "field" [ var_e o; Str "1" ]);
    ]
  in
  let wrap body = bound (lets @ ends) body in
  { wrap; place; root; read; start; stop; part }

(* A view that writes its source, made through [inout] or by a call whose result writes. *)
let made cb cx (init : Tast.expr) =
  match init.desc with
  | Call (Function i, _, [ ({ mode = Inout; value = src } : Tast.arg); a; b ], _)
    when owns i && i.name <> "split" ->
      made_through cb cx init src a b
  | Call (Function i, targs, args, _) -> (
      match target_writes cx (Function i) with
      | Some k -> made_by_call cb cx init (Function i) targs args k
      | None -> outside "a writable view whose view reads a source")
  | _ -> outside "a writable view that view.into or view.part doesn't make"

(* Whether an expression makes a view that writes its source: [view.into], [view.part], or
   a call of a function whose result writes. *)
let makes cx (e : Tast.expr) =
  match e.desc with
  | Call (Function i, _, _, _) when owns i -> i.name <> "split"
  | Call (Function i, _, _, _) ->
      Model_fns.code cx (Function i) <> None
      && target_writes cx (Function i) <> None
  | _ -> false

(* [var v = init] for a view that writes its source, and the rest of its block
   (projections.writable-bindings). *)
let binding cb cx (v : Hir.var) (init : Tast.expr) (rest : Tast.block) =
  let m = made cb cx init in
  let src = temp "source" init.loc in
  let w = { src; start = m.start; stop = m.stop; part = m.part } in
  m.wrap (scope cb cx v w ~src_root:m.root m.place rest)

(* A call of a function whose result writes, read: the view of its part in the argument it
   writes, which the caller reads after the call (projections.what-view-writes). *)
let call_result cb cx (e : Tast.expr) =
  let m = made cb cx e in
  m.wrap (Model_views.view [ m.read; var_e m.start; var_e m.stop ])

(* The result of a function whose result writes its parameter [p], at the end of its body:
   a view made through [inout] of [p], or of a writable binding of [p], given as its
   part's start and end (projections.results-that-write). *)
let offsets cb cx p (e : Tast.expr) =
  let m = made cb cx e in
  match m.place with
  | Arr [ Str r; Arr [] ] when r = p ->
      m.wrap (op (Str "tuple") [ var_e m.start; var_e m.stop ])
  | _ -> outside "a result that writes a view of other than its parameter"

(* [yield init] of a view that writes its source: the access called with the source's place
   and the part's start and end, as a writable parameter takes them, by [call]. *)
let yielded cb cx (init : Tast.expr) call =
  let m = made cb cx init in
  m.wrap
    (call
       [
         tag "inout" [ m.place ];
         tag "value" [ var_e m.start ];
         tag "value" [ var_e m.stop ];
       ])

let fresh = ref (-500000)

let local name (t : Types.ty) (loc : Ast.loc) =
  decr fresh;
  let v = { Hir.id = !fresh; name; loc } in
  (v, { Tast.desc = Local v; ty = t; loc })

(* [view.split(inout src, at, f)]: the parts before and from [at] copied into two
   variables, each a writable binding from its start, which [f] takes [inout], and written
   back when it returns or raises: two writable bindings of one source would be two
   [inout] arguments of one place. *)
let split cb cx (e : Tast.expr) (src : Tast.expr) (at : Tast.expr)
    (f : Tast.expr) =
  let t, lets, store, read = source cb cx src in
  let at_n = temp "at" at.loc in
  let fv, fl = local "split-f" f.ty f.loc in
  let lets =
    lets
    @ [ (at_n, ty cx i64, cb.expr at); (var_name fv, ty cx f.ty, cb.expr f) ]
  in
  let view = Types.Con (Model_views.view_item, [ t ]) in
  let lv, ll = local "before" view e.loc and rv, rl = local "from" view e.loc in
  let l = var_name lv and r = var_name rv in
  let zero = temp "split-zero" e.loc in
  let l_end = temp "before-end" e.loc and r_end = temp "from-end" e.loc in
  bind_writable cx lv { src = l; start = zero; stop = l_end; part = t };
  bind_writable cx rv { src = r; start = zero; stop = r_end; part = t };
  let args = List.map (fun value -> { Tast.mode = Inout; value }) [ ll; rl ] in
  let call_e = { e with desc = Call_value (fl, args) } in
  let call = cb.expr call_e in
  let err = raise_of cx [ call_e ] in
  let back =
    written_back cx e.loc t store read [ (l, int 0); (r, var_e at_n) ]
  in
  let after = list_op "slice" [ read; var_e at_n; list_op "len" [ read ] ] in
  let ends =
    [
      (zero, ty cx i64, int 0);
      (l_end, ty cx i64, list_op "len" [ var_e l ]);
      (r_end, ty cx i64, list_op "len" [ var_e r ]);
    ]
  in
  bound lets
    (tag "varIn"
       [
         Str l;
         ty cx t;
         list_op "slice" [ read; int 0; var_e at_n ];
         tag "varIn"
           [
             Str r;
             ty cx t;
             after;
             bound ends (around cx e.loc (Types.Tuple []) err call back);
           ];
       ])

(* A call of [view.into] or [view.part] that no writable binding holds, which reads
   (projections.what-view-writes): a view of the part, as [View.of] gives, of the source
   read when the call starts, after the offsets (values.inout-argument-order); and
   [view.split]. *)
let call cb cx (e : Tast.expr) (i : Hir.item) (args : Tast.arg list) =
  match (i.name, args) with
  | ("into" | "part"), [ src; a; b ] ->
      let lets, read =
        match src.value.desc with
        | Local u when writable_of cx u <> None ->
            ([], part_of (Option.get (writable_of cx u)))
        | _ ->
            let _, lets, _, read = source cb cx src.value in
            (lets, read)
      in
      let start = temp "start" a.value.loc and stop = temp "end" b.value.loc in
      bound
        (lets
        @ [
            (start, ty cx i64, cb.expr a.value);
            (stop, ty cx i64, cb.expr b.value);
          ])
        (Model_views.view [ read; var_e start; var_e stop ])
  | "split", [ src; at; f ] -> split cb cx e src.value at.value f.value
  | _ -> outside "the function std.view.%s" i.name
