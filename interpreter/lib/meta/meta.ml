(* The types of reflection (meta.std-meta, meta.shapes and meta.fresh-types): the native types of [std.meta], the
   cases of [Shape], and the fresh types of the arms and loops that read
   them. *)

module T = Types

let home = "std.meta"
let item name = { Hir.home; name }
let ty name args = T.Con (item name, args)
let shape = item "Shape"
let is_meta (i : Hir.item) = i.home = home
let element = Env_signatures.synthetic "E"
let key = Env_signatures.synthetic "K"
let value = Env_signatures.synthetic "V"
let placeholders = [ element; key; value ]

(* meta.shapes, in its order. *)
let cases t =
  let convert u = ty "Convert" [ t; u ] in
  let e = T.Param element in
  [
    ("Int", ty "Integer" [ t ]);
    ("Float", convert T.f64);
    ("Bool", convert T.bool);
    ("Str", convert T.str);
    ("Unit", convert T.unit);
    ("Option", convert (T.option e));
    ("List", convert (T.list e));
    ("Set", convert (T.list e));
    ("Map", convert (T.list (T.Tuple [ T.Param key; T.Param value ])));
    ("Array", ty "Sized" [ t; e ]);
    ("Tuple", ty "Fields" [ t ]);
    ("Record", ty "Fields" [ t ]);
    ("Variants", ty "Cases" [ t ]);
  ]

(* meta.fresh-types: each fresh type, by id, with the type whose shape it is part of
   and the order in which it was made. *)
let made : (int, T.ty * int) Hashtbl.t = Hashtbl.create 16
let count = ref 0

let fresh ~of_ name =
  let v = Env_signatures.synthetic name in
  incr count;
  Hashtbl.replace made v.id (of_, !count);
  T.rigid v

let freshen ~of_ t =
  let used = List.filter (fun v -> T.mentions_param [ v ] t) placeholders in
  T.subst (List.map (fun (v : Hir.var) -> (v, fresh ~of_ v.name)) used) [] t

let is_fresh (v : Hir.var) = Hashtbl.mem made v.id
let origin (v : Hir.var) = Option.map fst (Hashtbl.find_opt made v.id)
let mark () = !count

let since m (v : Hir.var) =
  match Hashtbl.find_opt made v.id with Some (_, n) -> n > m | None -> false

let fresh_in m t = List.find_opt (since m) (T.type_params t)
