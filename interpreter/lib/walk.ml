open Tast

type part = Expr of expr | Block of block

let arm_parts (a : arm) =
  List.map (fun e -> Expr e) (Option.to_list a.guard @ [ a.body ])

let catch_arms = function Some (c : catch) -> c.arms | None -> []

let parts (e : expr) =
  let exprs = List.map (fun e -> Expr e) in
  match e.desc with
  | Int _ | Float _ | Str _ | Bool _ | Local _ | Value_param _ | Constant _
  | Member_constant _ | Trait_constant _ | Callee _ | Constructor _ | Break
  | Continue | Hole | Error | Reflect _ ->
      []
  | Interpolated segments ->
      List.filter_map
        (function Text _ -> None | Splice (e, _) -> Some (Expr e))
        segments
  | Construct (_, _, es) | Tuple es | List es -> exprs es
  | Record (_, _, fields) -> exprs (List.map snd fields)
  | Update (base, fields) -> exprs (base :: List.map snd fields)
  | Spread s -> [ Expr s.body ]
  | Field (e, _)
  | Tuple_field (e, _)
  | Unary (_, e)
  | Raise e
  | Generalize (_, e)
  | Instantiate (e, _) ->
      [ Expr e ]
  | Call (_, _, args, _) | Project (_, _, args, _) ->
      exprs (List.map (fun (a : arg) -> a.value) args)
  | Call_value (f, args) ->
      Expr f :: exprs (List.map (fun (a : arg) -> a.value) args)
  | Index (a, b) | Binary (_, a, b) | Else (a, b) -> [ Expr a; Expr b ]
  | Try (operand, catch) ->
      Expr operand :: List.concat_map arm_parts (catch_arms catch)
  | Return e -> exprs (Option.to_list e)
  | Closure (_, _, body) -> [ Expr body ]
  | Block b | Loop b -> [ Block b ]
  | If (c, b, alt) | If_let (_, c, b, alt) ->
      Expr c :: Block b :: exprs (Option.to_list alt)
  | Match (scrutinee, arms) -> Expr scrutinee :: List.concat_map arm_parts arms
  | While (c, b) -> [ Expr c; Block b ]
  | For (_, Iter source, b) -> [ Expr source; Block b ]
  | For (_, Range (a, z, _), b) -> [ Expr a; Expr z; Block b ]
  (* handlers.handler-literals: a handler's operations are closure literals. *)
  | Handler h -> exprs (List.map snd h.ops)
  | With (h, _, _, b) -> [ Expr h; Block b ]
  | Resume e -> exprs (Option.to_list e)
  (* shared.when *)
  | When (names, b) -> exprs (List.map fst names) @ [ Block b ]
  (* meta.staging-annotations *)
  | Comptime e -> [ Expr e ]
  (* macros.outside-run: a quote's splices are evaluated where it is. *)
  | Quote q -> exprs (List.map (fun (s : splice) -> s.value) q.splices)

let stmt_exprs (s : stmt) =
  match s.stmt with
  | Let b | Var b -> b.value :: Option.to_list b.otherwise
  | Assign (_, place, value) -> [ place; value ]
  | Assert e | Yield e | Expr e -> [ e ]

let block_exprs b = List.concat_map stmt_exprs b

let children e =
  List.concat_map
    (function Expr e -> [ e ] | Block b -> block_exprs b)
    (parts e)

let rec iter ?(stmt = ignore) f e =
  f e;
  List.iter
    (function Expr e -> iter ~stmt f e | Block b -> iter_block ~stmt f b)
    (parts e)

and iter_block ?(stmt = ignore) f b =
  List.iter
    (fun s ->
      stmt s;
      List.iter (iter ~stmt f) (stmt_exprs s))
    b

let exists p e =
  let exception Found in
  try
    iter (fun e -> if p e then raise Found) e;
    false
  with Found -> true
