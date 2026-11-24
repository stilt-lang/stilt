(* Views that must write (projections.writable-bindings): the view given to a [var]
   binding of [View<T>], assigned to the whole of one, or yielded by a
   projection, writes every source it has, since the binding writes through
   it. Each view that reads a source is E0428, at the view. *)

open Tast
module V = Views_types
module S = Views_sources

(* The first source of [value] that it reads rather than writes. *)
let read_source t (value : expr) = List.find_opt S.reads (S.sources t value)

let must_write t report ~what (value : expr) =
  match read_source t value with
  | Some s ->
      report Code.e0428 value.loc
        (Printf.sprintf
           "this view reads %s, which %s must write: make it with \
            `view.into(inout %s, …)`, or bind it with `let`"
           (S.describe s) what (S.describe_bare s))
  | None -> ()

(* projections.writable-bindings: a [var] binding of [View<T>], and a view assigned to one. Rule
   2: the [var] of a [yield] whose operand isn't a place. *)
let stmt t report (s : stmt) =
  match s.stmt with
  | Var { pattern = { pat = P_bind v; pty; _ }; value; _ } when V.is_window pty
    ->
      must_write t report ~what:(Printf.sprintf "`%s`" v.name) value
  | Assign (None, { desc = Local v; _ }, value) -> (
      match Hashtbl.find_opt t v.id with
      | Some { writable = true; _ } ->
          must_write t report ~what:(Printf.sprintf "`%s`" v.name) value
      | Some _ | None -> ())
  | Yield value
    when V.is_view value.ty
         && Option.is_none (Modes_places.place value)
         && not (Check_fields.rooted_in_projection value) ->
      must_write t report ~what:"a yielded view" value
  | Var _ | Assign _ | Yield _ | Let _ | Assert _ | Expr _ -> ()
