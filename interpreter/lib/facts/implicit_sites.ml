(* The sites of a body (facts.inference and facts.allocation; effects.panic-kinds and effects.panicking-operations;
   facts.writes-in-place). *)

open Tast
module T = Types
module N = Implicit_names

type site = {
  loc : Ast.loc;
  facts : (Ast.limit * string) list;
  names : N.key list;
  notes : (Ast.limit * string) list;
}

let prelude = T.prelude_item

let is_map ty =
  match T.resolve ty with Con (item, _) -> item = prelude "Map" | _ -> false

(* effects.panicking-operations: a divisor written as an integer literal other than zero
   can't make a division panic. *)
let nonzero_literal (e : expr) =
  match e.desc with
  | Int text | Unary (Neg, { desc = Int text; _ }) ->
      Literal.int_canonical text <> ""
  | _ -> false

let divides = Accept_code.divides

(* std.integers: a call of [div_euclid] or [rem_euclid] whose divisor is
   written as an integer literal other than zero can't panic, as [/] and [%]
   can't, so its site doesn't name the native. *)
let euclidean_by_literal (c : callee) (args : arg list) =
  match (c, args) with
  | Member (owner, ("div_euclid" | "rem_euclid")), [ _; b ] ->
      owner.home = "std.prelude"
      && Option.is_some (Ints.of_name owner.name)
      && nonzero_literal b.value
  | _ -> false

(* Whether the variant [item] has a payload and a recursive type. *)
let recursive_variant env item =
  match Env.variant env item with
  | Some (owner, _, _ :: _) -> Modes_cow.recursive env owner
  | Some (_, _, []) | None -> false

let is_array ty = Option.is_some (Check_arrays.parts ty)

(* facts.allocation: a place that goes through an index, whose list or map a
   write may copy. An index into a view goes through storage that a writable
   binding holds unique (projections.places-through-views), and one into an array through
   storage held inline (generics.array-effects), so neither copies anything. *)
let rec through_index (p : expr) =
  match p.desc with
  | Index (base, _) ->
      (not (Views_types.is_view base.ty || is_array base.ty))
      || through_index base
  | Field (e, _) | Tuple_field (e, _) -> through_index e
  | _ -> false

let site ?(facts = []) ?(names = []) ?(notes = []) loc =
  { loc; facts; names; notes }

(* facts.range-loops, facts.guards, facts.divisors and facts.keys: what a rule of acceptance leaves of an operation's
   [panic], with what the closest rule needs. *)
let proved proofs verdict e =
  match proofs with
  | None -> `Unproved None
  | Some p -> (
      match verdict p e with
      | Accept.Proved _ -> `Proved
      | Unproved "" -> `Unproved None
      | Unproved note -> `Unproved (Some note))

let panic_site what ~names loc = function
  | `Proved -> if names = [] then [] else [ site ~names loc ]
  | `Unproved note ->
      [
        site
          ~facts:[ (Ast.Panic, what) ]
          ~names
          ~notes:(Option.fold ~none:[] ~some:(fun n -> [ (Ast.Panic, n) ]) note)
          loc;
      ]

let panics what loc = site ~facts:[ (Ast.Panic, what) ] loc
let allocates what loc = site ~facts:[ (Ast.Alloc, what) ] loc

(* facts.allocation: the [inout] arguments, receivers included, whose places go
   through an index. *)
let inout_sites args =
  List.filter_map
    (fun (a : arg) ->
      if a.mode = Inout && through_index a.value then
        Some
          (allocates
             "this `inout` argument hands on an element through an index, \
              which copies the list or map when it is shared"
             a.value.loc)
      else None)
    args

(* facts.writes-in-place: a write through an index that isn't in place, with why. *)
let index_write (ip : Implicit_in_place.result) (p : expr) =
  match List.assq_opt p ip.reasons with
  | Some why ->
      allocates
        ("this write through an index copies the list when it is shared: " ^ why)
        p.loc
  | None ->
      allocates
        "this write reaches an element that other elements may share, which \
         copies it"
        p.loc

(* The sites of a statement itself, apart from those of its expressions. A
   store into a map, [m[k] = v], inserts its key and can't panic, so its
   place is recorded in [stores]. *)
let stmt_sites env ip proofs stores (s : stmt) =
  match s.stmt with
  | Assert _ -> [ panics "this `assert` can panic" s.at ]
  | Assign (op, p, v) -> (
      let division =
        match op with
        | Some (Div | Rem) when divides p v ->
            panic_site "this division can panic" ~names:[] s.at
              (proved proofs Accept.division p)
        | _ -> []
      in
      match (op, p.desc) with
      | None, Index (m, _) when is_map m.ty ->
          stores := p :: !stores;
          [
            site
              ~facts:
                [
                  ( Alloc,
                    "this store into a map may insert a key, which allocates" );
                ]
              ~names:(N.key_names env m.ty) p.loc;
          ]
      | _ when through_index p && not (List.memq p ip.Implicit_in_place.writes)
        ->
          division @ [ index_write ip p ]
      | _ -> division)
  (* projections.yield: a yield whose place goes through an index allocates, as
     an [inout] argument's does. *)
  | Yield p when through_index p ->
      [
        allocates
          "this `yield` hands on an element through an index, which copies the \
           list or map when it is shared"
          p.loc;
      ]
  | Let _ | Var _ | Yield _ | Expr _ -> []

let show env (s : expr) =
  site ~names:(N.method_names env (prelude "Show") "show" s.ty) s.loc

(* projections.writable-views: [view.into] and [view.split] make the storage of their
   [inout] argument unique, which allocates unless it is in place (facts.writes-in-place). *)
let view_write (ip : Implicit_in_place.result) (e : expr) =
  match e.desc with
  | Call (Function { home = "std.view"; name = "into" | "split" }, _, _, _)
    when not (List.memq e ip.writes) ->
      let why =
        Option.fold ~none:"" ~some:(( ^ ) ": ") (List.assq_opt e ip.reasons)
      in
      [
        allocates
          ("this makes the storage it writes unique, which copies it when it \
            is shared" ^ why)
          e.loc;
      ]
  | _ -> []

let is_iterator ty =
  match Types.resolve ty with
  | Con ({ home = "std.view"; name = "Iter" }, _) -> true
  | _ -> false

(* The sites of an expression itself, apart from those inside it. *)
let expr_sites env ip proofs stores (e : expr) =
  let alloc what = [ allocates what e.loc ] in
  match e.desc with
  | Index (m, _) when not (List.memq e stores) ->
      let names = if is_map m.ty then N.key_names env m.ty else [] in
      panic_site "this index can panic" ~names e.loc
        (proved proofs Accept.access e)
  | Binary ((Div | Rem), a, b) when divides a b ->
      panic_site "this division can panic" ~names:[] e.loc
        (proved proofs Accept.division e)
  | Hole -> [ panics "this hole panics when it runs" e.loc ]
  | Call (c, _, args, _) when euclidean_by_literal c args -> inout_sites args
  (* handlers.implicit-effects-and-capabilities: a performance is a call through a stored function
     value, which allocates the rest of the performance, that a handler may keep
     to resume. *)
  | Call (Operation _, _, args, _) ->
      alloc "this performance allocates" @ inout_sites args
  (* facts.allocation: a [with] installs its handler, and a [for] over an [Iter]
     keeps the state it pulls elements through. *)
  | With _ -> alloc "this `with` allocates its handler"
  | For (_, Iter { ty; _ }, _) when is_iterator ty ->
      alloc "this `for` over an iterator allocates its state"
  | Call (c, targs, args, _) ->
      (site ~names:(N.callee_names env c targs) e.loc :: inout_sites args)
      @ view_write ip e
  | Callee (c, targs) -> [ site ~names:(N.callee_names env c targs) e.loc ]
  | Call_value (_, args) -> inout_sites args
  | Binary ((Eq | Ne), a, _) ->
      [ site ~names:(N.method_names env (prelude "Eq") "eq" a.ty) e.loc ]
  | Binary ((Lt | Le | Gt | Ge), a, _) ->
      [ site ~names:(N.method_names env (prelude "Ord") "compare" a.ty) e.loc ]
  | Interpolated segments ->
      allocates "this interpolation allocates a string" e.loc
      :: List.filter_map
           (function Splice (s, _) -> Some (show env s) | Text _ -> None)
           segments
  (* generics.array-effects: an array's literal makes a value held inline. *)
  | List _ when not (is_array e.ty) -> alloc "this list literal allocates"
  (* shared.locks *)
  | When _ ->
      [ site ~facts:[ (Locks, "this `when` holds shared values") ] e.loc ]
  | Closure _ -> alloc "this closure literal allocates"
  | Record (item, _, _) when Modes_cow.recursive env item ->
      alloc "this record of a recursive type allocates"
  | (Constructor (item, _) | Construct (item, _, _ :: _))
    when recursive_variant env item ->
      alloc "this variant of a recursive type allocates"
  | _ -> []

let sites ?proofs env ip block =
  let found = ref [] and stores = ref [] in
  let add ss = found := List.rev_append ss !found in
  let overflows =
    List.map (fun (what, loc) -> site ~facts:[ (Ast.Overflow, what) ] loc)
  in
  Walk.iter_block
    ~stmt:(fun s ->
      add (overflows (Implicit_overflow.stmt s));
      add (stmt_sites env ip proofs stores s))
    (fun e ->
      add (overflows (Implicit_overflow.expr e));
      add (expr_sites env ip proofs !stores e))
    block;
  List.rev !found

let no_in_place =
  { Implicit_in_place.writes = []; copies = []; reasons = []; reached = [] }

let names env block =
  List.concat_map (fun s -> s.names) (sites env no_in_place block)
