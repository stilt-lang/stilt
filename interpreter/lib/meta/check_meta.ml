(* Reflection (meta.shape-and-name and meta.fresh-types): [T.shape()] and [T.name()], the fresh types of the
   arms and loops that read a shape, and bound tests. *)

module T = Types
module A = Tast
open Check_state

(* meta.shape-and-name: in [std.meta] and in a module that names it with [use], a type's
   [shape] and [name], when the type has no member of that name. *)
let reflection st ty (name : Hir.name) =
  let here =
    st.module_.name = Meta.home || List.mem Meta.home st.module_.imports
  in
  match name.desc with
  | "shape" when here -> Some (A.Shape_of ty, Meta.ty "Shape" [ ty ])
  | "name" when here -> Some (A.Name_of ty, T.str)
  | _ -> None

(* meta.shapes and meta.fresh-types: the payload of a case of [Shape<t>] in a pattern, with a
   fresh type of its own for each of [E], [K] and [V]. *)
let payload owner args payload =
  match args with
  | [ t ] when owner = Meta.shape -> List.map (Meta.freshen ~of_:t) payload
  | _ -> payload

(* meta.fields and meta.variant-cases: what [for] binds for each field of a [meta.Fields<T>], or
   for each case of a [meta.Cases<T>], with a fresh type of the loop's
   body. *)
let element ty =
  match T.resolve ty with
  | Con (item, [ t ]) when item = Meta.item "Fields" ->
      Some (Meta.ty "Field" [ t; Meta.fresh ~of_:t "F" ])
  | Con (item, [ t ]) when item = Meta.item "Cases" ->
      Some (Meta.ty "Case" [ t; Meta.fresh ~of_:t "P" ])
  | _ -> None

(* meta.bound-tests: the bounds of a bound test on the type parameter [v], with
   their arguments. *)
let tested (v : Hir.var) (bounds : Hir.bound list) =
  let param : Hir.type_param =
    {
      var = v;
      bounds;
      fields = [];
      pack = false;
      implied = false;
      value = None;
    }
  in
  match Env.bounds_of [ param ] with [ (_, bs) ] -> bs | _ -> []

(* meta.bound-tests: checks [k] with the bounds of a bound test added to [v]'s, as
   its branch does. *)
let within st (v : Hir.var) bounds k =
  let saved = st.bounds in
  st.bounds <- (v, bounds) :: st.bounds;
  Fun.protect ~finally:(fun () -> st.bounds <- saved) k
