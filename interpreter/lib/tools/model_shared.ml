(* Shared values, tasks, scopes and the parallel calls of std.par as the calculus writes
   them. A program's meaning is its sequential run (tasks.sequential-run), in which a
   shared value is a cell of the world, which every task reaches, and a handle names it;
   a [when] holds the cells it names, binds each name to its cell's value, runs its block
   and puts the values back however the block ends (shared.when). Tasks, scopes and
   [std.par] are calls in that run. *)

open Model_json
open Model_types
open Model_ops
open Model_forms

type callbacks = {
  expr : Tast.expr -> Model_json.t;
  block : Tast.block -> Model_json.t;
  place : Tast.expr -> Model_json.t;
}

let i64 = prelude_ty "i64"
let zero = tag "int" [ Str "0" ]
let list_op name operands = op (tag "list" [ Str name ]) operands

(* The payload [T] of a [Shared<T>]. *)
let payload t =
  match norm t with
  | Types.Con (_, [ p ]) -> p
  | _ -> outside "a when on something that isn't shared"

(* A call of the function value [f], of the function type [t]. *)
let call_with cx f t args = call_e cx f args (fn_result t)

(* [Shared.new(v)]: a new cell of the world holding [v], and its handle
   (shared.std-sync). *)
let shared_new cx (e : Tast.expr) v =
  on_world "sharedNew" [ ty cx (payload e.ty) ] [ v ]

(* A name of a [when]: the temporary that holds its handle, the binding that stands for
   its value's place, and its value's type. *)
type name = { handle : string; var : Hir.var; t : Types.ty }

(* The block of a [when] that holds [held], with each binding of [same] written as the
   one it shares a value with (shared.when). *)
let holding (cb : callbacks) cx (b : Tast.block) held same =
  let saved = !aliases in
  aliases := List.map (fun ((v : Hir.var), w) -> (v.id, w)) same @ saved;
  let block =
    Fun.protect ~finally:(fun () -> aliases := saved) (fun () -> cb.block b)
  in
  let names =
    List.map (fun n -> Arr [ Str (var_name n.var); ty cx n.t ]) held
  in
  tag "held" [ Arr names; Arr (List.map (fun n -> var_e n.handle) held); block ]

(* [when a, b { block }]: each handle evaluated, in order; then, for each way the handles of
   names of one type may be equal, the block holding one value for each set of names whose
   handles are, the others written as the first of them (shared.when and
   shared.names-that-may-be-one-place). *)
let when_ (cb : callbacks) cx (e : Tast.expr) pairs (b : Tast.block) =
  cx.when_met <- true;
  let name i ((h : Tast.expr), var) =
    let handle = temp (Printf.sprintf "when-handle-%d" i) e.loc in
    ({ handle; var; t = payload h.ty }, (h, cb.expr h))
  in
  let names = List.mapi name pairs in
  let same_type n h = to_string (ty cx n.t) = to_string (ty cx h.t) in
  let rec split held same = function
    | [] -> holding cb cx b (List.rev held) same
    | n :: rest ->
        let rec against = function
          | [] -> split (n :: held) same rest
          | h :: more ->
              let equal =
                op (Str "sameCell") [ var_e n.handle; var_e h.handle ]
              in
              let one = split held ((n.var, h.var) :: same) rest in
              tag "if" [ equal; ty cx e.ty; one; against more ]
        in
        against (List.filter (same_type n) (List.rev held))
  in
  let bind (n, ((h : Tast.expr), j)) rest =
    tag "letIn" [ Str n.handle; ty cx h.ty; j; rest ]
  in
  List.fold_right bind names (split [] [] (List.map fst names))

(* tasks.sequential-run and tasks.scope-failure: [spawn(f)] runs [f] to its end and a
   task's handle is its value, so [t.await()] is [t]; a scope is [()], and [s.spawn(f)]
   runs [f], whose raise leaves as any raise. [Shared.new] makes a handle
   (shared.std-sync). *)
let member_call (cb : callbacks) cx (e : Tast.expr) (owner : Hir.item) name
    (args : Tast.arg list) =
  match (owner.home, owner.name, name, args) with
  | "std.sync", "Shared", "new", [ v ] -> shared_new cx e (cb.expr v.value)
  | "std.task", "Task", "await", [ t ] -> cb.expr t.value
  | "std.task", "Scope", "spawn", [ s; f ] ->
      let run = call_with cx (cb.expr f.value) f.value.ty [] in
      tag "seq" [ cb.expr s.value; run ]
  | _ -> outside "the function %s.%s" (item_name owner) name

(* Whether a type's functions are of std.sync or std.task. *)
let owns (owner : Hir.item) = owner.home = "std.sync" || owner.home = "std.task"

(* par.sequential-meaning: [par.map(xs, f)] calls [f] on the elements from the first to the
   last, and gives the list of their values. *)
let par_map cx (e : Tast.expr) (xs : Tast.expr) (f : Tast.expr) xs_e f_e =
  let n = temp "par-list" e.loc and g = temp "par-function" e.loc in
  let acc = temp "par-values" e.loc and x = temp "par-element" e.loc in
  let call = call_with cx (var_e g) f.ty [ tag "value" [ var_e x ] ] in
  let push =
    tag "assign" [ Arr [ Str acc; Arr [] ]; list_op "push" [ var_e acc; call ] ]
  in
  let loop = tag "for" [ Str x; ty cx (elem xs.ty); var_e n; push ] in
  let collect =
    tag "varIn"
      [
        Str acc;
        ty cx e.ty;
        tag "list" [ ty cx (elem e.ty); Arr [] ];
        tag "seq" [ loop; var_e acc ];
      ]
  in
  tag "letIn"
    [
      Str n; ty cx xs.ty; xs_e; tag "letIn" [ Str g; ty cx f.ty; f_e; collect ];
    ]

(* Whether a place is a variable followed by fields, whose evaluation reads nothing. *)
let rec plain (e : Tast.expr) =
  match e.desc with
  | Local _ -> true
  | Field (b, _) | Tuple_field (b, _) -> plain b
  | _ -> false

(* [par.each(inout xs, f)]: [f] called on each element of [xs] in place, from the first to
   the last (par.sequential-meaning). *)
let par_each (cb : callbacks) cx (e : Tast.expr) (xs : Tast.expr)
    (f : Tast.expr) =
  if not (plain xs) then outside "a par.each over a place with an index";
  let g = temp "par-function" e.loc and i = temp "par-index" e.loc in
  let root, steps =
    match cb.place xs with
    | Arr [ root; Arr steps ] -> (root, steps)
    | _ -> outside "a place the model lacks"
  in
  let elem = Arr [ root; Arr (steps @ [ tag "index" [ var_e i ] ]) ] in
  let call = call_with cx (var_e g) f.ty [ tag "inout" [ elem ] ] in
  let range =
    op
      (tag "list" [ tag "range" [ Bool false ] ])
      [ zero; list_op "len" [ cb.expr xs ] ]
  in
  tag "letIn"
    [
      Str g; ty cx f.ty; cb.expr f; tag "for" [ Str i; ty cx i64; range; call ];
    ]

(* [par.both(f, g)]: [f] called, then [g], and the pair of their values
   (par.sequential-meaning). *)
let par_both cx (e : Tast.expr) (f : Tast.expr) (g : Tast.expr) f_e g_e =
  let a = temp "par-first" e.loc and b = temp "par-second" e.loc in
  let pair =
    op (Str "tuple")
      [ call_with cx (var_e a) f.ty []; call_with cx (var_e b) g.ty [] ]
  in
  tag "letIn"
    [ Str a; ty cx f.ty; f_e; tag "letIn" [ Str b; ty cx g.ty; g_e; pair ] ]

(* The body of the [par.fold] helper [key] at [t]: [xs] itself when it has one element,
   and otherwise its halves folded by calls of [key], combined by [f] (par.fold-tree). *)
let fold_body cx key (t : Types.ty) (fty : Types.ty) =
  let self xs =
    call_e cx
      (tag "fnRef" [ Str key; Arr []; Arr [] ])
      [ tag "value" [ xs ]; tag "value" [ var_e "f" ] ]
      t
  in
  let len = list_op "len" [ var_e "xs" ] and one = tag "int" [ Str "1" ] in
  let half = binary Div i64 i64 (var_e "n") (tag "int" [ Str "2" ]) in
  let combined =
    tag "letIn"
      [
        Str "h";
        ty cx i64;
        half;
        tag "letIn"
          [
            Str "l";
            ty cx t;
            self (list_op "slice" [ var_e "xs"; zero; var_e "h" ]);
            tag "letIn"
              [
                Str "r";
                ty cx t;
                self (list_op "slice" [ var_e "xs"; var_e "h"; var_e "n" ]);
                call_with cx (var_e "f") fty
                  [ tag "value" [ var_e "l" ]; tag "value" [ var_e "r" ] ];
              ];
          ];
      ]
  in
  let first = tag "index" [ var_e "xs"; zero ] in
  let body =
    tag "letIn"
      [
        Str "n";
        ty cx i64;
        len;
        tag "if" [ binary Eq i64 i64 (var_e "n") one; ty cx t; first; combined ];
      ]
  in
  body

(* The function the export writes for [par.fold] at a type: a list of one element is it,
   and a longer one its first [n / 2] elements folded, combined by [f] with the rest
   folded (par.fold-tree). *)
let fold_helper cx (t : Types.ty) (fty : Types.ty) =
  let key =
    "std.par.fold<" ^ to_string (ty cx t) ^ ", " ^ to_string (ty cx fty) ^ ">"
  in
  (if not (List.mem_assoc key cx.helpers) then
     let frow =
       match norm fty with Types.Fn (_, _, r) -> r | _ -> Types.empty_row
     in
     let body = fold_body cx key t fty in
     let param name t = Arr [ Str "let"; Str name; ty cx t; Null ] in
     let list = Types.Con (list_item, [ t ]) in
     let decl =
       Arr
         [
           Str key;
           Arr [];
           Arr [];
           Arr [ param "xs" list; param "f" fty ];
           ty cx t;
           row cx frow;
           body;
         ]
     in
     cx.helpers <- (key, decl) :: cx.helpers);
  key

(* [par.fold(xs, empty, f)]: [empty] for an empty list, and the tree of par.fold-tree
   otherwise, its arguments evaluated in order first. *)
let par_fold cx (e : Tast.expr) (f : Tast.expr) xs_e empty_e f_e =
  let key = fold_helper cx e.ty f.ty in
  let n = temp "fold-list" e.loc
  and d = temp "fold-empty" e.loc
  and g = temp "fold-function" e.loc in
  let fold =
    call_e cx
      (tag "fnRef" [ Str key; Arr []; Arr [] ])
      [ tag "value" [ var_e n ]; tag "value" [ var_e g ] ]
      e.ty
  in
  let empty = binary Eq i64 i64 (list_op "len" [ var_e n ]) zero in
  let list = Types.Con (list_item, [ e.ty ]) in
  tag "letIn"
    [
      Str n;
      ty cx list;
      xs_e;
      tag "letIn"
        [
          Str d;
          ty cx e.ty;
          empty_e;
          tag "letIn"
            [
              Str g;
              ty cx f.ty;
              f_e;
              tag "if" [ empty; ty cx e.ty; var_e d; fold ];
            ];
        ];
    ]

(* A call of a function of std.task or std.par by its name. *)
let std_call (cb : callbacks) cx (e : Tast.expr) (i : Hir.item)
    (args : Tast.arg list) =
  let v (a : Tast.arg) = cb.expr a.value in
  match (i.home, i.name, args) with
  | "std.task", "spawn", [ f ] -> call_with cx (v f) f.value.ty []
  | "std.task", ("threads" | "sequential"), [] -> unit_e
  | "std.task", "scope", [ f ] ->
      call_with cx (v f) f.value.ty [ tag "value" [ unit_e ] ]
  | "std.par", "map", [ xs; f ] -> par_map cx e xs.value f.value (v xs) (v f)
  | "std.par", "each", [ xs; f ] -> par_each cb cx e xs.value f.value
  | "std.par", "both", [ f; g ] -> par_both cx e f.value g.value (v f) (v g)
  | "std.par", "fold", [ xs; d; f ] -> par_fold cx e f.value (v xs) (v d) (v f)
  | _ -> outside "the function %s" (item_name i)
