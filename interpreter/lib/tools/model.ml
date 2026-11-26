open Model_json
open Model_types

let main_item = { Hir.home = "main"; name = "main" }

(* A projection written for an access keeps the access's value in a one-element list,
   which its body ends with (projections.when-projection-runs). *)
let yielding cx access body =
  let saved = cx.yielding in
  cx.yielding <- access;
  Fun.protect
    ~finally:(fun () -> cx.yielding <- saved)
    (fun () ->
      match access with
      | None -> body ()
      | Some a ->
          let list = Types.Con (Model_forms.list_item, [ a.result ]) in
          tag "varIn"
            [
              Str a.res;
              ty cx list;
              tag "list" [ ty cx a.result; Arr [] ];
              tag "seq"
                [
                  body ();
                  tag "index" [ Model_forms.var_e a.res; tag "int" [ Str "0" ] ];
                ];
            ])

(* A function at one instantiation: [name, typeParams, rowParams, params,
   result, row, body]. *)
let fn_decl cx (inst : fn_instance) =
  let s = Model_fns.signature cx inst.target in
  let d, body =
    match Model_fns.code cx inst.target with
    | Some code -> code
    | None ->
        outside "the function %s, which has no code"
          (Model_fns.target_name inst.target)
  in
  let at t = ty cx (Model_fns.instantiated inst t) in
  let param (m, (v : Hir.var)) (_, t) =
    let t = Model_fns.instantiated inst t in
    writes cx m v t;
    Arr [ mode m; Str (var_name v); param_ty cx (m, t); Null ]
  in
  let params = List.map2 param d.params s.params in
  let access =
    match inst.target with
    | Function i ->
        Option.map (fun (_, _, a) -> a) (List.assoc_opt i cx.projections)
    | _ -> None
  in
  let body =
    raises_in cx (Model_fns.instantiated_row inst s.row) (fun () ->
        yielding cx access (fun () ->
            Model_exprs.block cx (Model_fns.body inst d s body)))
  in
  Arr
    [
      Str inst.fkey;
      Arr [];
      Arr [];
      Arr params;
      at s.ret;
      row cx (Model_fns.instantiated_row inst s.row);
      body;
    ]

(* Every function reached from [main], each once, in the order reached. *)
let functions cx =
  let rec go done_ =
    match
      List.find_opt
        (fun inst -> not (List.mem_assoc inst.fkey done_))
        (List.rev cx.fns)
    with
    | None -> List.rev_map snd done_
    | Some inst -> go ((inst.fkey, fn_decl cx inst) :: done_)
  in
  go []

(* A record or a variant type: [name, fields] or [name, ctors], and, for a generic
   one, its type parameters' names. *)
let type_decl cx inst =
  let params = if inst.generic then [ type_params cx inst ] else [] in
  let ty t = ty cx (instantiated cx inst t) in
  match (inst.args, Env.type_info cx.env inst.item) with
  | [ Record fields ], _ when inst.item = Types.anonymous ->
      let field (f, t) = Arr [ Str f; Model_types.ty cx t ] in
      `Record (Arr [ Str inst.key; Arr (List.map field fields) ])
  | _, info -> (
      match info with
      | Some { Env.def = Env.Record fields; _ } ->
          let field (f, t) = Arr [ Str f; ty t ] in
          `Record (Arr (Str inst.key :: Arr (List.map field fields) :: params))
      | Some { Env.def = Env.Variants ctors; _ } ->
          let ctor (c, ts) = Arr [ Str c; Arr (List.map ty ts) ] in
          `Variant (Arr (Str inst.key :: Arr (List.map ctor ctors) :: params))
      | _ -> outside "the type %s" inst.key)

(* Every type met, each once: declaring one may name another. *)
let type_decls cx =
  let rec go done_ =
    match
      List.find_opt
        (fun inst -> not (List.mem_assoc inst.key done_))
        (List.rev cx.types)
    with
    | None -> List.rev_map snd done_
    | Some inst -> go ((inst.key, type_decl cx inst) :: done_)
  in
  let decls = go [] in
  ( List.filter_map (function `Record r -> Some r | `Variant _ -> None) decls,
    List.filter_map (function `Variant v -> Some v | `Record _ -> None) decls )

(* The program's stdin, each maximal invalid UTF-8 subsequence one U+FFFD as the program
   reads it (std.read-line and std.io). *)
let stdin () = Strings.repair (In_channel.input_all In_channel.stdin)

(* [main]'s call, and [main]'s row. What it writes to the output and standard error is in the world it ends
   in, however it ends (program.exit-statuses). *)
let main_expr cx (main : fn_instance) =
  let s =
    match Env.function_sig cx.env main_item with
    | Some s -> s
    | None -> outside "a program without main"
  in
  let call =
    Model_forms.call_e cx
      (tag "fnRef" [ Str main.fkey; Arr []; Arr [] ])
      [] s.ret
  in
  let io, raise = flat s.row in
  let raise = match raise with None -> Null | Some e -> ty cx e in
  (Arr [ Bool io; raise; Arr [] ], call)

(* program.missing-main: a program without [main] runs nothing and ends with status 2,
   as one whose [main] writes nothing and that has errors does. *)
let nothing_to_run =
  let main = Model_forms.unit_e in
  let decls =
    Obj
      (List.map
         (fun k -> (k, Arr []))
         [ "records"; "variants"; "functions"; "impls"; "traits"; "traitImpls" ])
  in
  to_string
    (Obj
       [
         ("decls", decls);
         ("main", main);
         ("row", Arr [ Bool true; Null; Arr [] ]);
         ("erroneous", Bool true);
       ])

(* The program as the calculus writes it. *)
let written env program =
  let cx =
    {
      env;
      program;
      types = [];
      fns = [];
      reads_input = false;
      effects = [];
      handlers = [];
      lazy_met = false;
      when_met = false;
      raises = None;
      helpers = [];
      projections = [];
      yielding = None;
      writable = [];
    }
  in
  let main = Model_fns.instance cx (Function main_item) [] [] in
  let fns = functions cx in
  let main_row, main = main_expr cx main in
  let records, variants = type_decls cx in
  if cx.lazy_met && cx.when_met then
    outside "a lazy value in a program with a when";
  (cx, fns, records, variants, main_row, main)

let export ?(erroneous = false) env (program : Tast.program) =
  if Env.function_sig env main_item = None then Ok nothing_to_run
  else
    try
      let cx, fns, records, variants, main_row, main = written env program in
      let fns = fns @ List.rev_map snd cx.helpers in
      let decls =
        Obj
          [
            ("records", Arr (List.rev records @ List.rev_map snd cx.handlers));
            ("variants", Arr (List.rev variants));
            ("functions", Arr fns);
            ("impls", Arr []);
            ("traits", Arr []);
            ("traitImpls", Arr []);
            ("effects", Arr (List.rev_map snd cx.effects));
          ]
      in
      (* The input the run reads, which the model's world starts with (std.io). *)
      let input = if cx.reads_input then stdin () else "" in
      let fields =
        [
          ("decls", decls);
          ("main", main);
          ("row", main_row);
          ("input", Str input);
        ]
      in
      Ok
        (to_string
           (Obj (fields @ if erroneous then [ ("erroneous", Bool true) ] else [])))
    with Outside why -> Error why
