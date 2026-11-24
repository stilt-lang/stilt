(* The state of checking one body: what checking it has found so far, and
   where in it an expression is. *)

module T = Types
module A = Tast

let by_value : Ast.mode = Let
let by_inout : Ast.mode = Inout

type rule = Numeric | Integer | Negatable | Bool_or_integer

(* Where a value must have type [()] or [Never] (expressions.statements and expressions.if). An
   [if] without [else] carries its own type, which is [()] unless its block
   has another. *)
type unit_site = Statement | If_without_else of T.ty

type literal = {
  lty : T.ty;
  text : string;
  negative : bool;
  float : bool;
  lloc : Ast.loc;
}

(* A constant, by its name: a module's, or a type's ([Type.NAME]). *)
type constant =
  | Global of Hir.item
  | Assoc of Hir.item * string
  | Of_impl of Hir.item * Hir.item * string

(* What a name that a pattern writes without a module names, once the pattern
   is checked (patterns.variants-by-type). *)
type named = Named_variant of Hir.item | Named_const | Named_error

(* traits.trait-arguments and traits.bound-arguments: the arguments [args] that the impl of [trait] for
   [ty] must give the trait's parameters, which inference makes them once
   [ty] is known. *)
type fix = {
  fty : T.ty;
  ftrait : Hir.item;
  fargs : T.ty list;
  floc : Ast.loc;
  mutable fixed : bool;
}

(* records.record-bounds: a type that must have [fields], with their types, which a
   record bound names, decided once the type is known. *)
type need = {
  nty : T.ty;
  nfields : (string * T.ty) list;
  nloc : Ast.loc;
  mutable met : bool;
}

(* variadics.spread-checks: inside a spread expression, the pack tuples it names so
   far, with their packs, where the first of another pack than the first
   is named, and how many closures inside it the expression
   being checked is. *)
type spreading = {
  mutable named : (Hir.var * T.ty) list;
  mutable mixed_at : Ast.loc option;
  mutable closures : int;
  mutable names_broken : bool;
}

(* What checking one body has found so far. *)
type state = {
  env : Env.t;
  module_ : Hir.module_;
  traits : Hir.item list; (* The traits visible to method calls. *)
  mutable bounds : Env.bounds;
  self : T.ty option; (* What [Self] means in a trait. *)
  locals : (int, T.ty) Hashtbl.t;
  mutable errors : Diagnostic.t list;
  mutable broken : bool;
      (* Whether the body holds an error that resolution reported. *)
  mutable vars : T.ty list;
  mutable unknown : int list; (* Variables already reported as unknown. *)
  mutable obligations : (T.ty * Hir.item * Ast.loc * Env.bounds) list;
  mutable fixes : fix list;
  mutable operators : (T.ty * rule * Ast.loc) list;
  mutable amounts : (T.ty * Ast.loc) list;
      (* Shift amounts whose type was open where they were checked. *)
  mutable int_patterns : (T.ty * Ast.loc) list;
  mutable literals : literal list;
  mutable units : (T.ty * unit_site * Ast.loc) list;
  mutable specs : (T.ty * string * Ast.loc) list;
  mutable constants : constant list; (* The constants the body names. *)
  mutable catch_errors : T.ty list;
      (* The error types of [catch]es whose operands may still raise. *)
  mutable passed : (Ast.loc * T.row * A.label) list;
      (* What uses give the row variables their callees pair (effects.passing-to-paired-variables). *)
  bare : (Ast.loc, named) Hashtbl.t;
      (* What each name that a pattern writes without a module names, by the
         pattern's place. *)
  arrays : (Ast.loc, unit) Hashtbl.t;
      (* The list patterns that match arrays, by place, which, once they fit
         their sizes, can't fail when their elements can't (generics.array-patterns). *)
  mutable unknown_names : (string * Diagnostic.t) list;
      (* The E0211 of those that name nothing, among [errors]. *)
  mutable needs : need list;
  mutable spreading : spreading option;
  mutable splices : (T.ty * Hir.place * Ast.loc) list;
  mutable unsafe_depth : int;
      (* How many [unsafe] blocks hold the expression being checked (c.unsafe-operations). *)
  mutable unsafe_blocks : Ast.loc list;
      (* The [unsafe] blocks of the body, its closures' included, latest
         first. *)
  mutable c_elements : (T.ty * Ast.loc) list;
      (* The [T] of each call that reads, writes or lends C memory, which C
         must hold, decided at the end of the body (c.element-types). *)
}

(* Where in a body an expression is. *)
type ctx = {
  st : state;
  ret : T.ty; (* The type that [return] returns. *)
  yields : T.ty option;
      (* The type of the place that [yield] hands the caller, in a
         projection's body (projections.yield). *)
  effects : (T.row * Ast.loc) list ref; (* Latest first. *)
  known : (Hir.item * T.ty list) list;
      (* The effects that the rows around the expression hold, those of the
         innermost [with] first, which give a performance its type arguments
         (handlers.performing-operation). *)
  resume : (T.ty * T.ty) option;
      (* In an operation's body of a handler that takes control, the
         operation's result type, which [resume] takes, and the handler's [R],
         which it gives (handlers.resuming). *)
  infer : ctx -> T.ty option -> Hir.expr -> A.expr;
      (* [Check_exprs.infer], through which the checks of an expression's
         parts, in the modules before it, check their own parts. *)
}

let error st code (loc : Ast.loc) fmt =
  Printf.ksprintf
    (fun message ->
      st.errors <-
        {
          Diagnostic.code;
          file = st.module_.file;
          line = loc.line;
          col = loc.col;
          message;
        }
        :: st.errors)
    fmt

let fresh st ?kind loc =
  let v = T.fresh ?kind loc in
  st.vars <- v :: st.vars;
  v

let show t = Types_show.to_string (T.zonk t)
let is_never t = T.resolve t = T.never
let node desc ty (loc : Ast.loc) : A.expr = { desc; ty; loc }
let error_node (loc : Ast.loc) : A.expr = { desc = Error; ty = T.Error; loc }

let literal st ~text ~negative ~float loc =
  let ty = fresh st ~kind:(if float then Float_literal else Int_literal) loc in
  st.literals <- { lty = ty; text; negative; float; lloc = loc } :: st.literals;
  ty

let obligation st ty trait loc =
  st.obligations <- (ty, trait, loc, st.bounds) :: st.obligations

let shown_bound (trait : Hir.item) args =
  match args with
  | [] -> trait.name
  | args -> trait.name ^ "<" ^ String.concat ", " (List.map show args) ^ ">"

(* Makes the arguments of a fix those that the impl gives, once its type is
   known, and reports E0318 when they differ (traits.bound-arguments). *)
let improve_one st (f : fix) =
  match Env.trait_args st.env st.bounds f.fty f.ftrait with
  | Some actual when List.length actual = List.length f.fargs ->
      f.fixed <- true;
      let expected = List.map T.zonk f.fargs in
      if not (List.for_all2 Check_unify.unify f.fargs actual) then
        error st Code.e0318 f.floc
          "`%s` doesn't implement `%s`: its impl is `%s`" (show f.fty)
          (shown_bound f.ftrait expected)
          (shown_bound f.ftrait actual)
  | Some _ -> f.fixed <- true
  | None -> ()

(* records.bound-fields: a record bound is met by a declared or anonymous record
   with each field it names, of exactly its type, and E0318 names the first
   field that isn't. *)
let rec meet st (n : need) =
  match T.unsolved n.nty with
  | Some { kind = Any; _ } -> ()
  | _ -> (
      match T.resolve n.nty with
      (* variadics.packs: a pack's record bound holds for each element. *)
      | Spread (pack, body) -> (
          match T.resolve pack with
          | Tuple es ->
              n.met <- true;
              List.iter
                (fun e -> meet st { n with nty = T.element pack body e })
                es
          | Var _ -> ()
          | _ ->
              n.met <- true;
              meet st { n with nty = body })
      | ty ->
          n.met <- true;
          meet_record st n ty)

and meet_record st n ty =
  let unmet fmt = error st Code.e0318 n.nloc fmt in
  match (ty, Env.record_fields st.env ty) with
  | Error, _ -> ()
  | _, None ->
      unmet
        "`%s` isn't a record, so it has no field `%s`, which the bound needs"
        (show ty)
        (fst (List.hd n.nfields))
  | _, Some have -> (
      let wrong (name, want) =
        match List.assoc_opt name have with
        | None -> Some (name, want, None)
        | Some got when Check_unify.unify got want -> None
        | Some got -> Some (name, want, Some got)
      in
      match List.find_map wrong n.nfields with
      | None -> ()
      | Some (name, _, None) ->
          unmet "`%s` has no field `%s`, which the bound needs" (show ty) name
      | Some (name, want, Some got) ->
          unmet "the bound needs `%s`'s field `%s` to be `%s`, not `%s`"
            (show ty) name (show want) (show got))

let improve st =
  List.iter (fun f -> if not f.fixed then improve_one st f) (List.rev st.fixes);
  List.iter (fun n -> if not n.met then meet st n) (List.rev st.needs)

let require_fields st ty fields loc =
  if fields <> [] then
    st.needs <-
      { nty = ty; nfields = fields; nloc = loc; met = false } :: st.needs

(* traits.bound-arguments: requires the impl of [trait] for [ty] to give the trait's
   parameters [args]. *)
let fix st ty trait args loc =
  if args <> [] then (
    let f =
      { fty = ty; ftrait = trait; fargs = args; floc = loc; fixed = false }
    in
    st.fixes <- f :: st.fixes;
    improve_one st f)

let prelude_trait name = T.prelude_item name
