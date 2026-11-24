(* Closure literals, branches and loops in the walk of a body's flow. *)

open Tast
open Modes_flow

type walker = state -> expr -> into -> unit
type block_walker = ?id:int -> state -> block -> into -> unit

(* The bindings that a closure literal captures, each once with the type it
   has there: those its body names but doesn't bind itself. *)
let captures ps body =
  let bound = ref (List.concat_map binders ps) and named = ref [] in
  let bind p = bound := binders p @ !bound in
  Walk.iter
    ~stmt:(fun s ->
      match s.stmt with Let b | Var b -> bind b.pattern | _ -> ())
    (fun e ->
      match e.desc with
      | Local v
        when not (List.exists (fun ((w : Hir.var), _) -> w.id = v.id) !named) ->
          named := (v, e.ty) :: !named
      | Closure (qs, _, _) -> List.iter bind qs
      | If_let (p, _, _, _) | For (p, _, _) -> bind p
      | Match (_, arms) -> List.iter (fun (a : arm) -> bind a.pattern) arms
      | Try (_, catch) ->
          List.iter (fun (a : arm) -> bind a.pattern) (Walk.catch_arms catch)
      | _ -> ())
    body;
  List.filter
    (fun ((v : Hir.var), _) ->
      not (List.exists (fun (w : Hir.var) -> w.id = v.id) !bound))
    (List.rev !named)

(* A closure literal copies the bindings it captures, and what holds the
   closure holds the copies (modes.copies). It escapes, with what it captures,
   where it leaves the function, and where what holds it does (modes.escaping and modes.not-escaping). Its body is a function of its own, whose parameters have the modes
   its type gives them; the paths of the function around it go through the body,
   as if a call ran it where it is written, and around it (modes.shared-writes). *)
let closure ~(expr : walker) st (e : expr) ps body into =
  let keep = keeper into in
  let made = point st in
  let held = ref [] in
  List.iter
    (fun ((v : Hir.var), ty) ->
      match own st v with
      | Some d when st.calls.cow ty -> (
          copy st v.id [] made keep true;
          match (d.kind, into.leaves) with
          | Param _, Some _ -> st.flow.kept <- v.id :: st.flow.kept
          | Param _, None -> ()
          | _, Some _ -> st.flow.escapes <- v.id :: st.flow.escapes
          | _, None -> held := v.id :: !held)
      | _ -> ())
    (captures ps body);
  (match keep with
  | Bound (hs, _) when !held <> [] ->
      st.flow.held <-
        (List.map (fun (v : Hir.var) -> v.id) hs, !held) :: st.flow.held
  | _ -> ());
  let outer = (st.frame, st.targets) in
  st.frames <- st.frames + 1;
  st.frame <- st.frames;
  st.targets <- [];
  let modes =
    match Types.resolve e.ty with
    | Fn (fps, _, _) when List.length fps = List.length ps -> List.map fst fps
    | _ -> List.map (fun _ : Ast.mode -> Let) ps
  in
  List.iter2
    (fun p mode ->
      List.iter (fun v -> declare st v (Param mode) Rest) (binders p))
    ps modes;
  let before = st.tick in
  ignore (meet st [ before ]);
  expr st body (leaving Out);
  ignore (meet st [ before; st.tick ]);
  let frame, targets = outer in
  st.frame <- frame;
  st.targets <- targets

(* The parts of a value that patterns bind, each binding until its scope ends,
   bound anew where they are bound. When the value is a place of a binding,
   each part a pattern binds is a copy, held by the variable that binds it
   (modes.copies); with [element], the patterns bind its elements. *)
let bind_parts st (scrutinee : expr) patterns ~element =
  bind_at st (List.concat_map (fun (p, _) -> binders p) patterns);
  List.iter
    (fun (p, scope) ->
      List.iter (fun v -> declare st v Pattern scope) (binders p))
    patterns;
  match Modes_places.place scrutinee with
  | Some { root; path } when own st root <> None && st.calls.cow scrutinee.ty ->
      let path = if element then path @ [ Modes_places.Index ] else path in
      let made = point st in
      List.iter
        (fun (p, scope) ->
          List.iter
            (fun (part, v, ty) ->
              if st.calls.cow ty then
                copy ~at:(Some []) st root.id part made
                  (Bound ([ v ], scope))
                  false)
            (pattern_parts p path))
        patterns
  | _ -> ()

let matched ~(expr : walker) st (scrutinee : expr) patterns =
  expr st scrutinee (read Here);
  bind_parts st scrutinee patterns ~element:false

(* An arm, whose bindings last until it ends: where its guard ends, if it has
   one, and where it ends. *)
let arm ~(expr : walker) st (a : arm) id into =
  let outer = st.blocks in
  st.blocks <- id :: outer;
  let guard =
    spanning st id (fun () ->
        Option.iter (fun g -> expr st g (read Here)) a.guard;
        let guard = st.tick in
        expr st a.body into;
        guard)
  in
  st.blocks <- outer;
  (Option.map (fun _ -> guard) a.guard, st.tick)

(* Two alternatives, after the tick where control chooses: each path goes
   through one of them, and they meet after (modes.shared-writes). *)
let either st first second =
  let choice = st.tick in
  ignore (meet st [ choice ]);
  first ();
  let ended = st.tick in
  ignore (meet st [ choice ]);
  second ();
  ignore (meet st [ ended; st.tick ])

(* Arms, each with the number of its block, entered from [entries] and from
   the guards of the arms before it, after which control meets the ends in
   [ends]. [enter] walks what each arm binds before it. *)
let arms ~expr st entries cases ~enter ends into =
  let guards = ref [] and ends = ref ends in
  List.iter
    (fun ((a : arm), id) ->
      enter (meet st (entries @ !guards)) a id;
      let guard, ended = arm ~expr st a id into in
      guards := Option.to_list guard @ !guards;
      ends := ended :: !ends)
    cases;
  ignore (meet st !ends)

(* A [break] goes to what follows its loop, and a [continue] to its loop's
   head (modes.shared-writes). *)
let leave st (e : expr) =
  let j = jump st in
  match (st.targets, e.desc) with
  | t :: _, Break -> t.breaks <- j :: t.breaks
  | t :: _, _ -> t.continues <- j :: t.continues
  | [], _ -> ()

(* Code that may run any number of times, none among them. *)
let again st f =
  let head = meet st [ st.tick ] in
  f ();
  step st st.tick head;
  ignore (meet st [ head ])

(* Code from any point of which control may go on to what follows it, as a
   performance in a [with]'s block that the handler doesn't resume does. *)
let handled st f =
  let first = st.tick in
  f ();
  let last = st.tick in
  let out = meet st [ last ] in
  st.flow.ranges <- (first, last, out) :: st.flow.ranges

(* [if let], [match] and [try], whose branches' values go where the whole's
   goes. A raise, or a call that may raise, anywhere in a [try]'s operand goes
   to its arms (modes.shared-writes). *)
let branches ~(block : block_walker) ~(expr : walker) st (e : expr) into =
  match e.desc with
  | If_let (p, scrutinee, b, alt) ->
      let id = fresh_block st in
      matched ~expr st scrutinee [ (p, Scope id) ];
      either st
        (fun () -> block ~id st b into)
        (fun () -> Option.iter (fun x -> expr st x into) alt)
  | Match (scrutinee, cases) ->
      let ids = List.map (fun _ -> fresh_block st) cases in
      matched ~expr st scrutinee
        (List.map2 (fun (a : arm) id -> (a.pattern, Scope id)) cases ids);
      arms ~expr st [ st.tick ] (List.combine cases ids)
        ~enter:(fun _ _ _ -> ())
        [] into
  | Try (operand, catch) ->
      let first = st.tick in
      expr st operand into;
      let last = st.tick in
      arms ~expr st []
        (List.map (fun a -> (a, fresh_block st)) (Walk.catch_arms catch))
        ~enter:(fun entry (a : arm) id ->
          st.flow.ranges <- (first, last, entry) :: st.flow.ranges;
          let bound = binders a.pattern in
          bind_at st bound;
          List.iter (fun v -> declare st v Pattern (Scope id)) bound)
        [ last ] into
  | _ -> ()

(* A loop's turns: its head is reached from before the loop, from the end of
   each turn and from each [continue], and what follows the loop from where
   [start], which walks what runs at the head, says, and from each [break]
   (modes.shared-writes). *)
let turns st ~start body =
  let head = meet st [ st.tick ] in
  let t = { head; breaks = []; continues = [] } in
  st.targets <- t :: st.targets;
  let exits = start head in
  body ();
  step st st.tick head;
  List.iter (fun c -> st.flow.steps <- (c, head) :: st.flow.steps) t.continues;
  st.targets <- List.tl st.targets;
  ignore (meet ~jumps:t.breaks st exits)

(* A loop, whose body runs again after any code of it. A [while]'s condition
   runs at its head, where the loop may end. A [for] loop's iterable is
   evaluated once, before; a place it is is read for the whole body
   (modes.durations), and its pattern binds each element anew at the head,
   where the loop may end. *)
let looping ~(block : block_walker) ~(expr : walker) st (e : expr) =
  let read = read Here in
  match e.desc with
  | Loop b -> turns st ~start:(fun _ -> []) (fun () -> block st b read)
  | While (c, b) ->
      turns st
        ~start:(fun _ ->
          expr st c read;
          let tested = st.tick in
          ignore (meet st [ tested ]);
          [ tested ])
        (fun () -> block st b read)
  | For (p, Iter source, b) ->
      let id = fresh_block st in
      expr st source read;
      turns st
        ~start:(fun head ->
          (match Modes_places.place source with
          | Some { root; _ } ->
              st.flow.reads <- (root.id, point st) :: st.flow.reads
          | None -> ());
          bind_parts st source [ (p, Scope id) ] ~element:true;
          [ head ])
        (fun () -> block ~id st b read)
  | For (p, Range (a, z, _), b) ->
      let id = fresh_block st in
      expr st a read;
      expr st z read;
      List.iter (fun v -> declare st v Pattern (Scope id)) (binders p);
      turns st
        ~start:(fun head ->
          bind_at st (binders p);
          [ head ])
        (fun () -> block ~id st b read)
  | _ -> ()
