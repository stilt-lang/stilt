(* Quotes and their splices (macros.quote and macros.splices). *)

module T = Types
module A = Tast
open Check_state

let code_type : Hir.code -> T.ty = function
  | Code_expr -> Meta.ty "Expr" []
  | Code_type -> Meta.ty "Type" []
  | Code_pattern -> Meta.ty "Pattern" []
  | Code_field -> Meta.ty "FieldInit" []

let quote ctx loc (q : Hir.quote) =
  let splice (s : Hir.splice) : A.splice =
    let value = ctx.infer ctx None s.value in
    ctx.st.splices <- (value.ty, s.place, s.at) :: ctx.st.splices;
    { place = s.place; spread = s.spread; at = s.at; value }
  in
  let splices = List.map splice q.splices in
  node
    (Quote
       {
         home = q.home;
         form = q.form;
         tokens = q.tokens;
         splices;
         names = q.names;
       })
    (code_type q.form) loc

(* What a value of a type writes where a splice stands: code, a name, or a
   literal, a float only as an expression. *)
let one (place : Hir.place) ty =
  let meta name = ty = Meta.ty name [] in
  let literal ~float =
    match ty with
    | T.Con ({ home = "std.prelude"; name }, []) ->
        name = "str" || name = "bool"
        || List.mem name T.integer_types
        || (float && List.mem name T.float_types)
    | _ -> false
  in
  match place with
  | In_expr -> meta "Expr" || meta "Name" || literal ~float:true
  | In_pattern -> meta "Pattern" || meta "Name" || literal ~float:false
  | In_type -> meta "Type"
  | In_name -> meta "Name"
  | In_elements | In_fields -> false

(* A type still open, or with an error, fits: inference or another
   diagnostic decides it. *)
let fits (place : Hir.place) ty =
  let ty = T.zonk ty in
  let unknown t = Option.is_some (T.unsolved t) || T.mentions_error t in
  unknown ty
  ||
  match (place, ty) with
  | In_elements, T.Con (item, [ e ]) when item = T.prelude_item "List" ->
      unknown e || one In_expr e
  | In_fields, T.Con (item, [ e ]) when item = T.prelude_item "List" ->
      unknown e || e = Meta.ty "FieldInit" []
  | _ -> one place ty

let fit st =
  List.iter
    (fun (ty, place, loc) ->
      if not (fits place ty) then
        error st Code.e0311 loc
          "a value of type `%s` can't be spliced here (macros.splices)"
          (show (T.zonk ty)))
    (List.rev st.splices)
