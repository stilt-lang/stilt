(* The bodies the export writes of closures, of [for] loops and of functions whose result
   writes, given the export of expressions and blocks. *)

open Model_json
open Model_types
open Model_ops
open Model_forms

type callbacks = {
  expr : Tast.expr -> Model_json.t;
  block : Tast.block -> Model_json.t;
  assign : Ast.binary option -> Tast.expr -> Tast.expr -> Model_json.t;
  writing : Model_writes.callbacks;
}

(* A [for] over a list, or over the list of the integers a range yields
   (expressions.range-iteration), each element matched against the loop's
   pattern. *)
let for_loop cb cx (e : Tast.expr) (p : Tast.pattern) (it : Tast.iterable) b =
  let iterable, elem_ty =
    match it with
    | Tast.Iter it when is_map it.ty -> (
        (* expressions.for-iterables: a map yields its pairs in insertion
           order, which are its entries (std.maps). *)
        match (norm it.ty, Model_keys.keyed cx it.ty) with
        | _, Some (k, v) ->
            (Model_keys.entries cx k v (cb.expr it), Types.Tuple [ k; v ])
        | Con (_, [ k; v ]), None ->
            (map_op "entries" [ cb.expr it ], Types.Tuple [ k; v ])
        | _ -> outside "an iteration over something other than a list")
    | Iter it when is_array it.ty ->
        (* generics.array-iteration: the elements of the array's list, in order. *)
        (tag "field" [ cb.expr it; Str array_field ], elem it.ty)
    | Iter it -> (cb.expr it, elem it.ty)
    | Range (a, z, fin) ->
        let incl = fin = Ast.Inclusive in
        let range = tag "list" [ tag "range" [ Bool incl ] ] in
        (op range [ cb.expr a; cb.expr z ], p.pty)
  in
  let body = cb.block b in
  let name, body =
    match p.pat with
    | P_bind v -> (var_name v, body)
    | _ ->
        let n = temp "for" e.loc in
        (n, tag "match" [ var_e n; ty cx (block_ty b); Arr [ arm cx p body ] ])
  in
  tag "for" [ Str name; ty cx elem_ty; iterable; body ]

let closure cb cx (e : Tast.expr) ps body =
  match norm e.ty with
  | Fn (sig_ps, result, r) ->
      (* expressions.closures: a parameter written as a pattern binds a fresh name, which
         the body matches against the pattern, irrefutable there
         (patterns.irrefutable-positions). *)
      let named i (p : Tast.pattern) =
        match p.pat with
        | P_bind v -> (var_name v, None)
        | _ -> (Printf.sprintf "%s/%d" (temp "closure-param" e.loc) i, Some p)
      in
      let names = List.mapi named ps in
      let param (n, p) (m, t) =
        if p <> None && viewed t <> None then
          outside "a closure's parameter of a view type written as a pattern";
        param_decls cx (m, n, t)
      in
      List.iter2
        (fun (p : Tast.pattern) (m, t) ->
          match p.pat with P_bind v -> writes cx m v t | _ -> ())
        ps sig_ps;
      let bound acc (n, p) =
        match p with
        | Some p -> tag "match" [ var_e n; ty cx result; Arr [ arm cx p acc ] ]
        | None -> acc
      in
      let saved = cx.yielding in
      cx.yielding <- None;
      let body =
        Fun.protect
          ~finally:(fun () -> cx.yielding <- saved)
          (fun () ->
            List.fold_left bound
              (raises_in cx r (fun () -> cb.expr body))
              (List.rev names))
      in
      tag "closure"
        [
          Arr (List.concat (List.map2 param names sig_ps));
          ty cx result;
          row cx r;
          body;
        ]
  | _ -> outside "a closure of a type the model lacks"

(* The body of a function whose result writes its parameter [p], its result given as its
   part's start and end (projections.results-that-write). *)
let rec result_block cb cx p (stmts : Tast.block) =
  match stmts with
  | [ { stmt = Expr e; _ } ] -> Model_writes.offsets cb.writing cx p e
  | { stmt = Expr e; _ } :: rest ->
      tag "seq" [ cb.expr e; result_block cb cx p rest ]
  | {
      stmt =
        Let { pattern = { pat = P_bind v; pty; _ }; value; otherwise = None; _ };
      _;
    }
    :: rest ->
      tag "letIn"
        [
          Str (var_name v); ty cx pty; cb.expr value; result_block cb cx p rest;
        ]
  | { stmt = Assign (o, t, v); _ } :: rest when not (Model_projections.rooted t)
    ->
      tag "seq" [ cb.assign o t v; result_block cb cx p rest ]
  | _ -> outside "a result that writes after a statement the model lacks there"
