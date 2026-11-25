(* User-defined effects and their handlers (handlers.declaring-effect and
   handlers.with) in a csmith program, made from a stream of their own, so
   that the rest of the program is the one the same seed makes without them.
   The program declares one to three effects, of one to three operations each,
   and functions that perform them, directly, through the closure given to
   [map] (handlers.rows-pass-effects-on) and through the functions declared
   before them, some with [inout] parameters that they write before and after
   a performance. [main] installs handlers around blocks that perform them,
   some nested in others, which handle some effects and leave the rest to the
   handlers outside, some in loops, some inside a [when] on a [Shared<i64>].
   A handler answers with a value, or takes control (handlers.resuming) and
   resumes once, never, or on one path of an [if] only, since a body resumes
   at most once on each path (handlers.resume-at-most-once), then may print
   and transform the rest of the block's value. Its bodies may perform its own
   effect on the handler outside it. Every step prints, so differential
   testing compares the order of the events, the values that a handler ends a
   [with] with (handlers.call-that-handler-ends), and what [inout] arguments
   and variables hold after a [with] that a handler ends. Nothing it makes
   writes a variable of the rest of [main], whose lines come after it. *)

open Code
open Context

(* How likely a program is to use effects, and, when it does, to install some
   handlers inside a [when]. *)
let using = 0.3
let sharing = 0.5
let stream seed what = Pick.make (Hashtbl.hash (seed, what))
let wanted seed = Pick.chance (stream seed "uses effects") using

let shares seed =
  wanted seed && Pick.chance (stream seed "effects share") sharing

(* An operation, with its parameters' names and types, and its result, which
   may be [()]. *)
type op = { oname : string; params : (string * Ty.t) list; result : Ty.t }
type effect_ = { ename : string; ops : op list }

(* A function that performs effects: whether each parameter is [inout], and
   its type, its result, and the effects of its row beside [io]. *)
type fn_ = {
  fname : string;
  fparams : (bool * Ty.t) list;
  ret : Ty.t;
  row : string list;
}

(* The body the effects are made in, the program's mark, which its prints
   show, so that the programs that [just differential] runs as one declare no
   equal bodies (docs.duplicate-bodies), its effects, and the functions
   declared so far. *)
type state = {
  b : body;
  k : int;
  effects : effect_ list;
  mutable fns : fn_ list;
}

let typed = Ty.to_string
let rnd st = st.b.p.r
let fresh_in st prefix = fresh st.b.p prefix
let value st sc t = (Expr.expr st.b sc ~depth:2 ~known:false t).text
let known st sc t = (Expr.expr st.b sc ~depth:2 ~known:true t).text

(* A type of at most one level, with no map, that isn't [()]. *)
let rec value_ty p =
  match random_ty p ~maps:false 1 with Ty.Unit -> value_ty p | t -> t

(* The lines that print [what], and the values of [names]. *)
let said st what names =
  let shown = List.map (fun n -> " {" ^ n ^ "}") names in
  line
    (Printf.sprintf "print(\"ef%d %s%s\")" st.k what (String.concat "" shown))

let distinct r n xs =
  let rec go n xs =
    if n <= 0 || xs = [] then []
    else
      let x = Pick.one r xs in
      x :: go (n - 1) (List.filter (( <> ) x) xs)
  in
  go n xs

(* Declarations *)

let op_decl p =
  let r = p.r in
  let oname = fresh p "eo" in
  let params =
    Pick.times (Pick.between r 0 3) (fun () -> (fresh p "ea", value_ty p))
  in
  let result = if Pick.chance r 0.25 then Ty.Unit else value_ty p in
  { oname; params; result }

let op_head o =
  let params = List.map (fun (n, t) -> n ^ ": " ^ typed t) o.params in
  let result = if o.result = Ty.Unit then "" else " -> " ^ typed o.result in
  "fn " ^ o.oname ^ "(" ^ String.concat ", " params ^ ")" ^ result

let effect_decl p =
  let ename = fresh p "Ef" in
  let ops = Pick.times (Pick.between p.r 1 3) (fun () -> op_decl p) in
  ( { ename; ops },
    block_lines
      ("effect " ^ ename ^ " {")
      (List.concat_map (fun o -> line (op_head o)) ops)
      "}" )

(* Events: the steps of a function's body or a [with]'s block *)

let find st name = List.find (fun e -> e.ename = name) st.effects

let params_scope o =
  List.map (fun (n, t) -> { name = n; ty = t; mutable_ = false }) o.params

let perform st sc e o =
  call_text
    (e.ename ^ "." ^ o.oname)
    (List.map (fun (_, t) -> value st sc t) o.params)

(* A performance of [e.o] for each of one to three integers, in the closure
   given to [map], which performs the caller's effects. *)
let mapped st sc e o =
  let x = fresh_in st "ex" in
  let inner =
    closure_scope sc [ { name = x; ty = Int I64; mutable_ = false } ]
  in
  let xs = List.init (Pick.between (rnd st) 1 3) string_of_int in
  Printf.sprintf "[%s].map(|%s| %s)" (String.concat ", " xs) x
    (perform st inner e o)

(* [call] as a statement of its own when [t] is [()], or bound to a new
   variable, whose value it prints after [what]. *)
let bound st sc t call what =
  if t = Ty.Unit then (sc, line call)
  else
    let v = fresh_in st "ev" in
    ( declare sc v t ~mutable_:false,
      line (Printf.sprintf "let %s: %s = %s" v (typed t) call)
      @ said st what [ v ] )

let performs st sc names =
  let r = rnd st in
  let e = find st (Pick.one r names) in
  let o = Pick.one r e.ops in
  if o.result <> Ty.Unit && Pick.chance r 0.25 then
    bound st sc (List o.result) (mapped st sc e o) (o.oname ^ " mapped")
  else bound st sc o.result (perform st sc e o) o.oname

(* The arguments of a call of [f]: a variable that the code can change for
   each [inout] parameter, a new one when no other of its type is free, and
   the lines that declare the new ones and those that print them all. *)
let arguments st sc f =
  List.fold_left
    (fun (sc, setup, args, after) (inout, t) ->
      if not inout then (sc, setup, args @ [ value st sc t ], after)
      else
        let taken v = List.mem ("inout " ^ v.name) args in
        let free =
          List.filter (fun v -> not (taken v)) (Context.typed (changeable sc) t)
        in
        let given, sc, setup =
          if free <> [] && Pick.chance (rnd st) 0.7 then
            ((Pick.one (rnd st) free).name, sc, setup)
          else
            let a = fresh_in st "ei" in
            ( a,
              declare sc a t ~mutable_:true,
              setup
              @ line
                  (Printf.sprintf "var %s: %s = %s" a (typed t) (value st sc t))
            )
        in
        (sc, setup, args @ [ "inout " ^ given ], after @ said st given [ given ]))
    (sc, [], [], []) f.fparams

let call st sc f =
  let sc, setup, args, after = arguments st sc f in
  let sc, lines = bound st sc f.ret (call_text f.fname args) f.fname in
  (sc, setup @ lines @ after)

(* A write of a variable that the code can change, of the function's [inout]
   parameters or of those declared around a [with]. *)
let write st sc =
  let v = Pick.one (rnd st) (changeable sc) in
  (sc, line (Printf.sprintf "%s = %s" v.name (value st sc v.ty)))

(* A step of code where the effects [names] are handled: a performance, a
   call of a function whose row they cover, a print, a write, a [break] or a
   [continue] when a condition holds, or, while [depth] allows, a [with] of
   its own, alone or in a loop. The first step performs. *)
let rec event st sc names ~first ~depth =
  let r = rnd st in
  let callable =
    List.filter (fun f -> List.for_all (fun e -> List.mem e names) f.row) st.fns
  in
  let later w = if first then 0 else w in
  let guarded word =
    let c = Expr.cond st.b sc ~depth:2 in
    line ("if " ^ head c.text ^ " { " ^ word ^ " }")
  in
  Pick.run r
    [
      (5, fun () -> performs st sc names);
      ( (if callable = [] then 0 else 4),
        fun () -> call st sc (Pick.one r callable) );
      (later 1, fun () -> (sc, said st (fresh_in st "step") []));
      ((if changeable sc = [] then 0 else later 2), fun () -> write st sc);
      ( (if sc.loop then later 1 else 0),
        fun () -> (sc, guarded (Pick.one r [ "break"; "continue" ])) );
      ( (if depth > 0 then 2 else 0),
        fun () -> (sc, scene st sc names ~depth:(depth - 1)) );
      ( (if depth > 0 then later 1 else 0),
        fun () -> (sc, looped st sc names ~depth:(depth - 1)) );
    ]

and events st sc names ~depth n =
  let rec go sc i =
    if i >= n then (sc, [])
    else
      let sc, first = event st sc names ~first:(i = 0) ~depth in
      let sc, rest = go sc (i + 1) in
      (sc, first @ rest)
  in
  go sc 0

(* A [with] of handlers of one or two of the effects, around a block that
   performs them and those that [installed] holds, the effects handled
   around it. It has one type, which every handler that takes control gives,
   so that [with a, b] is [with a { with b { … } }] (handlers.with). Up to two
   variables declared before it are written in the block and printed after
   it, so that a handler that ends the [with] shows which writes were made. *)
and scene st sc installed ~depth =
  let r = rnd st in
  let p = st.b.p in
  let rt = value_ty p in
  let handled = distinct r (Pick.between r 1 2) st.effects in
  let sc, before, kept =
    List.fold_left
      (fun (sc, before, kept) () ->
        let t = value_ty p and c = fresh_in st "ec" in
        ( declare sc c t ~mutable_:true,
          before
          @ line (Printf.sprintf "var %s: %s = %s" c (typed t) (value st sc t)),
          kept @ [ c ] ))
      (sc, [], [])
      (List.init (Pick.between r 0 2) (fun _ -> ()))
  in
  let handlers =
    List.map
      (fun e ->
        handler st sc e ~takes:(Pick.chance r 0.6)
          ~forwards:(List.mem e.ename installed)
          rt)
      handled
  in
  let names = List.map fst handlers in
  let inside =
    installed
    @ List.filter_map
        (fun e -> if List.mem e.ename installed then None else Some e.ename)
        handled
  in
  let inner, block = events st sc inside ~depth (Pick.between r 1 4) in
  let w = fresh_in st "ew" in
  before
  @ List.concat_map snd handlers
  @ block_lines
      (Printf.sprintf "let %s: %s = with %s {" w (typed rt)
         (String.concat ", " names))
      (block @ line (known st inner rt))
      "}"
  @ said st w [ w ]
  @ if kept = [] then [] else said st (w ^ " kept") kept

(* A [for] of one to three turns around a [scene]. *)
and looped st sc installed ~depth =
  let r = rnd st in
  let n = fresh_in st "en" and limit = Pick.between r 1 3 in
  let inner =
    {
      (declare sc n (Int I64) ~mutable_:false) with
      loop = true;
      weight = sc.weight * limit;
    }
  in
  block_lines
    (Printf.sprintf "for %s in 0..%d {" n limit)
    (scene st inner installed ~depth)
    "}"

(* Handlers *)

(* A handler of [e], which takes control with the type [rt] when [takes], and
   whose bodies may perform [e] on the handler outside it when [forwards]. *)
and handler st sc e ~takes ~forwards rt =
  let h = fresh_in st "eh" in
  let ops = List.concat_map (op_body st sc e ~takes ~forwards rt h) e.ops in
  let arrow = if takes then " -> " ^ typed rt else "" in
  ( h,
    block_lines
      (Printf.sprintf "let %s = handler %s%s {" h e.ename arrow)
      ops "}" )

and op_body st sc e ~takes ~forwards rt h o =
  let r = rnd st in
  let inner = closure_scope sc (params_scope o) in
  let start = said st (h ^ "." ^ o.oname) (List.map fst o.params) in
  let inner, forwarded =
    if forwards && Pick.chance r 0.6 then
      let o' = Pick.one r e.ops in
      bound st inner o'.result (perform st inner e o') (h ^ " outer " ^ o'.oname)
    else (inner, [])
  in
  let rest =
    if takes then taking st inner o rt h
    else if o.result = Ty.Unit then []
    else line (value st inner o.result)
  in
  block_lines (op_head o ^ " {") (start @ forwarded @ rest) "}"

(* The rest of the body of a handler that takes control: it resumes and
   prints and transforms the value of the rest of the block, or ends the
   [with] with a value of its own, or does one or the other as a condition
   holds. *)
and taking st sc o rt h =
  let r = rnd st in
  let resumed () =
    let given = if o.result = Ty.Unit then "" else known st sc o.result in
    let er = fresh_in st "er" in
    let sc' = declare sc er rt ~mutable_:false in
    line (Printf.sprintf "let %s: %s = resume(%s)" er (typed rt) given)
    @ said st (h ^ " resumed") [ er ]
    @ line (known st sc' rt)
  in
  let ended () = said st (h ^ " ends") [] @ line (known st sc rt) in
  let branches first second =
    let c = Expr.cond st.b sc ~depth:2 in
    ((0, "if " ^ head c.text ^ " {") :: nest (first ()))
    @ ((0, "} else {") :: nest (second ()))
    @ [ (0, "}") ]
  in
  Pick.run r
    [
      (4, resumed);
      (2, ended);
      (2, fun () -> branches resumed ended);
      (1, fun () -> branches ended resumed);
    ]

(* Functions *)

let signature f names =
  let params =
    List.map2
      (fun (inout, t) n ->
        (if inout then "inout " else "") ^ n ^ ": " ^ typed t)
      f.fparams names
  in
  let ret = if f.ret = Ty.Unit then "" else " -> " ^ typed f.ret in
  Printf.sprintf "fn %s(%s)%s / {%s} {" f.fname
    (String.concat ", " params)
    ret
    (String.concat ", " ("io" :: f.row))

(* A function that performs one or two of the effects, through the functions
   declared before it too, and writes each of its [inout] parameters before
   its steps and after them, so after the performances that resume. *)
let function_ st =
  let p = st.b.p in
  let r = p.r in
  let fname = fresh p "ef" in
  let fparams =
    Pick.times (Pick.between r 0 3) (fun () -> (Pick.chance r 0.35, value_ty p))
  in
  let names = List.map (fun _ -> fresh p "ep") fparams in
  let ret = if Pick.chance r 0.3 then Ty.Unit else value_ty p in
  let row =
    List.map (fun e -> e.ename) (distinct r (Pick.between r 1 2) st.effects)
  in
  let f = { fname; fparams; ret; row } in
  let vars =
    List.rev_map2
      (fun (inout, ty) name -> { name; ty; mutable_ = inout })
      fparams names
  in
  let sc =
    {
      vars;
      frozen = [];
      loop = false;
      may_raise = false;
      io = true;
      returns = Some ret;
      weight = 1;
    }
  in
  let writes sc =
    List.concat_map
      (fun v ->
        if v.mutable_ then
          line (Printf.sprintf "%s = %s" v.name (value st sc v.ty))
        else [])
      vars
  in
  let before = writes sc in
  let sc', steps = events st sc row ~depth:0 (Pick.between r 1 3) in
  let after = writes sc' in
  let result = if ret = Ty.Unit then [] else line (value st sc' ret) in
  st.fns <- st.fns @ [ f ];
  block_lines (signature f names)
    (said st (fname ^ " in") [] @ before @ steps @ after @ result)
    "}"

(* [main] *)

(* A loop of one to three turns, each holding a [Shared<i64>] in a [when]
   around a [scene] that may write it, before adding to it, and the line that
   prints what it holds after the loop (shared.when). *)
let held st sc =
  let r = rnd st in
  let s = fresh_in st "es" and n = fresh_in st "en" in
  let limit = Pick.between r 1 3 in
  let inner =
    {
      (declare
         (declare sc n (Int I64) ~mutable_:false)
         s (Int I64) ~mutable_:true)
      with
      loop = true;
      weight = sc.weight * limit;
    }
  in
  let added = operand (Expr.expr st.b inner ~depth:2 ~known:false (Int I64)) in
  let added = Printf.sprintf "%s = %s +%% %s" s s added in
  line (Printf.sprintf "let %s = sync.Shared.new(0)" s)
  @ block_lines
      (Printf.sprintf "for %s in 0..%d {" n limit)
      (block_lines
         (Printf.sprintf "when %s {" s)
         (scene st inner [] ~depth:1 @ line added)
         "}")
      "}"
  @ line (Printf.sprintf "when %s { print(\"ef%d %s {%s}\") }" s st.k s s)

let uses p sc seed =
  let p = { p with r = stream seed "effects" } in
  let b = { p; budget = 4_000; spent = 0 } in
  let sc =
    {
      sc with
      vars = List.map (fun v -> { v with mutable_ = false }) sc.vars;
      loop = false;
      weight = 1;
    }
  in
  let effects, decls =
    List.split (Pick.times (Pick.between p.r 1 3) (fun () -> effect_decl p))
  in
  let st = { b; k = Pick.mark p.r seed; effects; fns = [] } in
  let fns = Pick.times (Pick.between p.r 1 4) (fun () -> function_ st) in
  let share = shares seed in
  let scenes =
    Pick.times (Pick.between p.r 1 3) (fun () ->
        Pick.run p.r
          [
            (4, fun () -> scene st sc [] ~depth:2);
            (2, fun () -> looped st sc [] ~depth:1);
            ((if share then 3 else 0), fun () -> held st sc);
          ])
  in
  (decls @ fns, List.concat scenes)
