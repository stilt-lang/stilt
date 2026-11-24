(* The types of views (views.viewable-types and views.view-types): which types can be viewed,
   which are view types, and where a view type may stand. *)

module T = Types

let is_view_con (item : Hir.item) =
  item.home = "std.view" && (item.name = "View" || item.name = "Iter")

let is_prelude (item : Hir.item) name = item = T.prelude_item name

(* views.viewable-types *)
let viewable ty =
  match T.resolve ty with
  | Con (item, []) -> is_prelude item "str"
  | Con (item, [ _ ]) -> is_prelude item "List"
  | Error | Var _ | Param _ | Con _ | Tuple _ | Record _ | Spread _ | Fn _
  | Forall _ | App _ | Handler _ | Value _ ->
      false

(* views.view-types: [View<T>], [Iter<T>] and [Option<V>] for a view type [V]. A
   closure that captures a view is a view type too, which its type doesn't
   show (views.fixed). *)
let rec is_view ty =
  match T.resolve ty with
  | Con (item, _) when is_view_con item -> true
  | Con (item, [ t ]) when is_prelude item "Option" -> is_view t
  | _ -> false

(* Whether a type holds a view type where views.view-types allows none, its whole
   standing where a value is [stored]. A function's parameters and result
   may be views, so its type holds none. *)
let rec stores_in ~stored ty =
  match T.resolve ty with
  | Con (item, args) when is_view_con item ->
      stored || List.exists (stores_in ~stored:false) args
  | Con (item, [ t ]) when is_prelude item "Option" -> stores_in ~stored t
  | Con (_, ts) | Tuple ts | App (_, ts) ->
      List.exists (stores_in ~stored:true) ts
  | Record fields -> List.exists (fun (_, t) -> stores_in ~stored:true t) fields
  | Spread (_, t) -> stores_in ~stored t
  | Fn _ | Forall _ | Handler _ | Param _ | Var _ | Value _ | Error -> false

let stores ty = stores_in ~stored:false ty

(* projections.writable-bindings and projections.places-through-views: [View<T>] itself, the type of a binding that a
   program writes through. *)
let is_window ty =
  match T.resolve ty with
  | Con ({ home = "std.view"; name = "View" }, _) -> true
  | _ -> false

(* Written types *)

let shown (t : Hir.ty) = Types_show.to_string (Env.of_hir t)

let viewable_written (t : Hir.ty) =
  match t.desc with
  | Ty_con (item, []) -> is_prelude item "str"
  | Ty_con (item, [ _ ]) -> is_prelude item "List"
  | Ty_error -> true
  | Ty_con _ | Ty_param _ | Ty_self | Ty_tuple _ | Ty_record _ | Ty_spread _
  | Ty_fn _ | Ty_app _ | Ty_self_app _ | Ty_handler _ | Ty_value _ ->
      false

(* Whether a written type is a view type: [View<T>], [Iter<T>], or an
   [Option] of one (views.view-types). *)
let rec view_written (t : Hir.ty) =
  match t.desc with
  | Ty_con (item, _) when is_view_con item -> true
  | Ty_con (item, [ a ]) when is_prelude item "Option" -> view_written a
  | _ -> false

(* E0421 at a view type [t] that stands where a value is stored. *)
let report_stored report (t : Hir.ty) =
  report Code.e0421 t.loc
    (Printf.sprintf
       "`%s` is a view, which can't be stored here: a view lives only in a \
        local, a parameter, a result or a closure"
       (shown t))

(* E0420 and E0421 at a written type, which stands where a value is
   [stored] (views.viewable-types and views.view-types). A stored [Option]
   of a view is the view type there, so the error is at the [Option]. *)
let rec written report ~stored (t : Hir.ty) =
  match t.desc with
  | Ty_con (item, args) when is_view_con item ->
      if stored then report_stored report t;
      (match (item.name, args) with
      | "View", [ a ] when not (viewable_written a) ->
          report Code.e0420 a.loc
            (Printf.sprintf
               "`%s` can't be viewed: a view is of a `str` or a `List`"
               (shown a))
      | _ -> ());
      List.iter (written report ~stored:false) args
  | Ty_con (item, [ a ]) when is_prelude item "Option" ->
      if stored && view_written a then (
        report_stored report t;
        written report ~stored:false a)
      else written report ~stored a
  | Ty_con (_, ts) | Ty_tuple ts | Ty_app (_, ts) | Ty_self_app ts ->
      List.iter (written report ~stored:true) ts
  | Ty_record fields ->
      List.iter
        (fun (f : Hir.field_decl) -> written report ~stored:true f.ty)
        fields
  | Ty_spread (_, t) -> written report ~stored t
  | Ty_fn (_, params, ret, row) ->
      List.iter (fun (_, p) -> written report ~stored:false p) params;
      Option.iter (written report ~stored:false) ret;
      Option.iter (written report ~stored:true) row.raise
  | Ty_handler (e, answer, row) ->
      List.iter (written report ~stored:true) e.args;
      Option.iter (written report ~stored:false) answer;
      Option.iter (written report ~stored:true) row.raise
  | Ty_param _ | Ty_self | Ty_value _ | Ty_error -> ()

(* The types a function's signature writes: its parameters, result and row,
   whose error type a view can't be (Required tests, "Stored"). *)
let signature report (f : Hir.fn_decl) =
  List.iter
    (function
      | Hir.Param (_, _, t, _) -> written report ~stored:false t
      | Self_param _ -> ())
    f.params;
  Option.iter (written report ~stored:false) f.ret;
  Option.iter (written report ~stored:true) f.row.raise

let rec decl report (d : Hir.decl Hir.node) =
  match d.desc.kind with
  | Type { def = Record fields; _ } ->
      List.iter
        (fun (f : Hir.field_decl) -> written report ~stored:true f.ty)
        fields
  | Type { def = Variants vs; _ } ->
      List.iter
        (fun (v : Hir.variant_decl) ->
          List.iter (written report ~stored:true) v.payload)
        vs
  | Type { def = Native; _ } | Test _ -> ()
  | Fn f -> signature report f
  | Const c -> written report ~stored:true c.ty
  | Trait t -> List.iter (decl report) t.members
  | Effect e ->
      List.iter
        (fun (o : Hir.operation) ->
          List.iter (fun (_, _, t) -> written report ~stored:false t) o.params;
          Option.iter (written report ~stored:false) o.ret;
          Option.iter (written report ~stored:true) o.row.raise)
        e.ops

(* The written types of the declarations of the program's modules, outside
   the bodies: the standard library's are the natives that views.std-view defines. *)
let declarations (program : Hir.program) =
  List.concat_map
    (fun (m : Hir.module_) ->
      if m.std then []
      else
        let found = ref [] in
        let report code loc message =
          found := Diagnostic.at ~file:m.file code loc message :: !found
        in
        List.iter (decl report) m.decls;
        List.iter
          (fun (i : Hir.impl_decl Hir.node) ->
            List.iter (decl report) i.desc.members)
          m.impls;
        List.rev !found)
    program

(* errors.declarations-with-errors: a type that a declaration writes with an error of views.viewable-types
   or 4 becomes the error type, as the part of a signature with an error
   does, so that no use of it reports more. *)
let erased ~stored (t : Hir.ty) =
  let found = ref false in
  written (fun _ _ _ -> found := true) ~stored t;
  if !found then { t with desc = Hir.Ty_error } else t

let erased_row (r : Hir.row) =
  { r with raise = Option.map (erased ~stored:true) r.raise }

let erased_fn (f : Hir.fn_decl) =
  let param : Hir.param -> Hir.param = function
    | Param (mode, v, t, escaping) ->
        Param (mode, v, erased ~stored:false t, escaping)
    | Self_param _ as p -> p
  in
  {
    f with
    params = List.map param f.params;
    ret = Option.map (erased ~stored:false) f.ret;
    row = erased_row f.row;
  }

let rec erased_decl (d : Hir.decl Hir.node) =
  let stored = erased ~stored:true in
  let kind : Hir.decl_kind =
    match d.desc.kind with
    | Type ({ def = Record fields; _ } as t) ->
        let field (f : Hir.field_decl) = { f with ty = stored f.ty } in
        Type { t with def = Record (List.map field fields) }
    | Type ({ def = Variants vs; _ } as t) ->
        let variant (v : Hir.variant_decl) =
          { v with payload = List.map stored v.payload }
        in
        Type { t with def = Variants (List.map variant vs) }
    | Fn f -> Fn (erased_fn f)
    | Const c -> Const { c with ty = stored c.ty }
    | Trait t -> Trait { t with members = List.map erased_decl t.members }
    | Effect e ->
        let op (o : Hir.operation) =
          {
            o with
            params =
              List.map
                (fun (m, v, t) -> (m, v, erased ~stored:false t))
                o.params;
            ret = Option.map (erased ~stored:false) o.ret;
            row = erased_row o.row;
          }
        in
        Effect { e with ops = List.map op e.ops }
    | (Type { def = Native; _ } | Test _) as k -> k
  in
  { d with desc = { d.desc with kind } }

let erase (program : Hir.program) =
  List.map
    (fun (m : Hir.module_) ->
      if m.std then m
      else
        let impl (i : Hir.impl_decl Hir.node) =
          {
            i with
            desc = { i.desc with members = List.map erased_decl i.desc.members };
          }
        in
        {
          m with
          decls = List.map erased_decl m.decls;
          impls = List.map impl m.impls;
        })
    program
