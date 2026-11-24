(* [when] (shared.when). *)

module T = Types
module A = Tast
open Check_state
open Check_expect

let shared_item = { Hir.home = "std.sync"; name = "Shared" }

(* The type [T] of a handle's value, when the handle is a [Shared<T>], and
   E0433 for one of another type. A name that resolution reported, or whose
   type has an error, holds a value of the error type. *)
let held ctx ((outer : Hir.expr), (inner : Hir.var)) =
  let st = ctx.st in
  let h = infer ctx None outer in
  let ty =
    match (outer.desc, known st outer.loc h.ty) with
    | Local _, Some (Con (item, [ t ])) when item = shared_item -> t
    | Local _, Some t ->
        error st Code.e0433 outer.loc
          "`%s` has type `%s`, so `when` can't hold it; only a `Shared<T>` can \
           be held"
          inner.name (show t);
        T.Error
    | _ ->
        st.broken <- true;
        T.Error
  in
  Hashtbl.replace st.locals inner.id ty;
  (h, inner)

(* Each name stands, in the block, for the place of its value, of type [T],
   and the [when]'s value is the block's. *)
let when_expr ctx expected loc names (block : Hir.block) =
  let names = List.map (held ctx) names in
  let b, ty = Check_blocks.block_expr ctx ~at:loc expected block in
  node (A.When (names, b)) ty loc
