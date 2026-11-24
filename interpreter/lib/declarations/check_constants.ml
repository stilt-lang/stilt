(* Constants: their values, and the cycles among them (declarations.constant-expressions and declarations.constant-cycles). *)

module T = Types
module A = Tast
open Check_state
open Check_expect
open Check_finish
open Check_zonk
open Check_bodies

(* declarations.constant-expressions: the first part of a constant's value, in evaluation
   order, that a constant expression can't hold. *)
let rec non_constant (e : A.expr) =
  let first = List.find_map non_constant in
  match e.desc with
  | Int _ | Float _ | Str _ | Bool _ | Constant _ | Member_constant _
  | Trait_constant _ | Error ->
      None
  | Unary (Neg, operand) -> non_constant operand
  | Tuple es | List es | Construct (_, _, es) -> first es
  | Record (_, _, fields) -> first (List.map snd fields)
  | _ -> Some e

(* A constant's value [value], checked against its type, and the constants it
   names. In the standard library, a hole marks a native constant (declarations.native-items). A
   trait's default value has the trait's [self] and [bounds] (traits.trait-constants). *)
let check_constant ?(bounds = []) ?self env m (c : Hir.const_decl)
    (value : Hir.expr) =
  let st = new_state env m ~bounds ~self in
  let value : A.expr A.definition =
    match value.desc with
    | Hole when m.std -> Native
    | _ ->
        let ty = Env.of_hir ?self c.ty in
        let v =
          check
            {
              st;
              ret = ty;
              yields = None;
              effects = ref [];
              infer = Check_exprs.infer;
              known = [];
              resume = None;
            }
            ty value
        in
        finish st;
        (match non_constant v with
        | None -> ()
        | Some part ->
            error st Code.e0326 part.loc
              "a constant's value is built only from literals, constants, \
               tuples, lists, records and variants");
        outcome st ~at:c.name.loc (fun () -> zonk_expr v)
  in
  (value, st.constants, st.errors)

(* declarations.constant-cycles: constants that refer to each other in a cycle. Each
   cycle is reported once, at the name of its last constant (errors.primary-spans). [constants] holds every constant that has a value, with its
   module, the position of its name and the constants its value names. *)
let constant_cycles constants =
  (* Of two constants with the same name, only the first is the one names
     refer to. *)
  let constants =
    List.fold_left
      (fun kept ((key, _, _, _) as c) ->
        if List.exists (fun (k, _, _, _) -> k = key) kept then kept
        else kept @ [ c ])
      [] constants
  in
  let refers = List.map (fun (key, _, _, named) -> (key, named)) constants in
  let reach key =
    let rec go seen = function
      | [] -> seen
      | k :: rest when List.mem k seen -> go seen rest
      | k :: rest ->
          go (k :: seen)
            (Option.value (List.assoc_opt k refers) ~default:[] @ rest)
    in
    go [] (Option.value (List.assoc_opt key refers) ~default:[])
  in
  let reaches = List.map (fun (key, _, _, _) -> (key, reach key)) constants in
  let in_cycle (key, _, _, _) = List.mem key (List.assoc key reaches) in
  let together (a, _, _, _) (b, _, _, _) =
    List.mem b (List.assoc a reaches) && List.mem a (List.assoc b reaches)
  in
  let rec groups = function
    | [] -> []
    | c :: rest ->
        let group, others = List.partition (together c) rest in
        (c :: group) :: groups others
  in
  List.map
    (fun group ->
      let last (_, (m : Hir.module_), (loc : Ast.loc), _) =
        (m.file, loc.line, loc.col)
      in
      let _, (m : Hir.module_), (loc : Ast.loc), _ =
        List.fold_left
          (fun a b -> if compare (last b) (last a) > 0 then b else a)
          (List.hd group) group
      in
      ( m,
        {
          Diagnostic.code = Code.e0327;
          file = m.file;
          line = loc.line;
          col = loc.col;
          message = "these constants refer to each other in a cycle";
        } ))
    (groups (List.filter in_cycle constants))
