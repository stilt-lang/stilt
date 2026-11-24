(* Patterns: their types (patterns.pattern-types). *)

module T = Types
module A = Tast
open Check_state
open Check_unify
open Check_expect
open Check_types
open Check_fields
open Check_members
open Check_refutable

(* Whether a value of type [t] can hold a value of a type constructor that
   [at] picks, through its elements, fields and payloads. A type met again
   inside itself can add only what its arguments hold. *)
let holds env ~at t =
  let rec holds seen t =
    match T.resolve t with
    | Con (item, _) when at item -> true
    | Con (item, args) when List.mem item seen -> List.exists (holds seen) args
    | Con (item, args) -> (
        let inside = holds (item :: seen) in
        match Env.type_info env item with
        | Some { def = Builtin; _ } -> List.exists inside args
        | Some { params; def = Record fields; _ } ->
            let sub = T.subst (List.combine params args) [] in
            List.exists (fun (_, t) -> inside (sub t)) fields
        | Some { params; def = Variants variants; _ } ->
            let sub = T.subst (List.combine params args) [] in
            List.exists
              (fun (_, payload) ->
                List.exists (fun t -> inside (sub t)) payload)
              variants
        | None -> false)
    | Tuple ts -> List.exists (holds seen) ts
    | Record fields -> List.exists (fun (_, t) -> holds seen t) fields
    | Spread (_, t) -> holds seen t
    | Param _ | App _ | Fn _ | Forall _ | Handler _ | Var _ | Value _ | Error ->
        false
  in
  holds [] t

(* patterns.floats *)
let holds_float env t = holds env ~at:float t

(* patterns.constants-with-written-eq *)
let holds_written_eq env t =
  holds env t ~at:(fun item ->
      Option.is_some (Env.trait_impl env ~trait:(T.prelude_item "Eq") item))

(* The parts of a pattern's type, made of [parts] by [make]: the parts when
   the pattern's type [ty] is made that way, and the error type for each part
   when it is the error type or can't be (errors.error-type). The variables in
   [parts] then stand for nothing, so they are tainted. *)
let shaped st loc ty parts make =
  let unknown () =
    List.iter T.taint parts;
    List.map (fun _ -> T.Error) parts
  in
  match T.resolve ty with
  | Error -> unknown ()
  | _ -> if agrees st loc ~expected:ty (make parts) then parts else unknown ()

(* A constant that a pattern [p] matches, of type [t]. *)
let comparable st (p : Hir.pattern) t =
  if holds_float st.env t then
    error st Code.e0328 p.loc
      "this constant holds a float, which a pattern can't match"
  else if holds_written_eq st.env t then
    error st Code.e0331 p.loc
      "this constant holds a type whose `Eq` you wrote, so compare it with \
       `==` in a guard"

let const_pattern st (p : Hir.pattern) ty item : A.pattern_desc =
  match Env.constant_type st.env item with
  | Some t ->
      expect st p.loc ~expected:ty t;
      comparable st p t;
      st.constants <- Global item :: st.constants;
      P_const (node (Constant item) t p.loc)
  | None -> P_error

let assoc_const_pattern ctx (p : Hir.pattern) ty hty (name : Hir.name) :
    A.pattern_desc =
  let st = ctx.st in
  let value = member_value ctx p.loc (Of_type hty) name in
  match value.desc with
  | Member_constant _ ->
      expect st p.loc ~expected:ty value.ty;
      comparable st p value.ty;
      P_const value
  | Error -> P_error
  | _ ->
      error st Code.e0311 name.loc "`%s` is not a constant" name.desc;
      P_error

let has_variants st owner =
  match Env.type_info st.env owner with
  | Some { def = Variants _; _ } -> true
  | _ -> false

(* The error of a name that a pattern writes without a module, which the body
   keeps one of per name when it is E0211 (errors.unknown-names). *)
let report_failure st (n : Hir.name) (d : Diagnostic.t) =
  st.errors <- d :: st.errors;
  if d.code = Code.e0211 then
    st.unknown_names <- (n.desc, d) :: st.unknown_names

(* The error of such a name that names no variant or constant, matched against
   [ty]. A type with variants is named in an E0211, since its variants are the
   names it could have meant. *)
let failed st ty n (d : Diagnostic.t) =
  match T.resolve ty with
  | Con (owner, _) as t when d.code = Code.e0211 && has_variants st owner ->
      let message =
        Printf.sprintf "`%s` has no variant `%s`" (show t) n.Hir.desc
      in
      report_failure st n { d with message }
  | _ -> report_failure st n d

(* The parts of a pattern with an error, which aren't checked: their types are
   unknown, so each name in them written without a module means what it means
   in scope, and an error there is reported (patterns.variants-by-type). *)
let rec unchecked st (p : Hir.pattern) =
  match p.desc with
  | P_bare (n, ps, fallback) ->
      (match fallback with Scope_failure d -> report_failure st n d | _ -> ());
      List.iter (unchecked st) ps
  | P_tuple ps | P_variant (_, ps) | P_list (ps, _) | P_or ps ->
      List.iter (unchecked st) ps
  | P_record (_, fields, _) | P_fields (fields, _) ->
      List.iter (fun (f : Hir.field_pattern) -> unchecked st f.pattern) fields
  | P_wild | P_bind _ | P_int _ | P_str _ | P_bool _ | P_const _
  | P_assoc_const _ | P_error ->
      ()

let rec pattern ctx (p : Hir.pattern) ty : A.pattern =
  let st = ctx.st in
  let at pat = { A.pat; pty = ty; ploc = p.loc } in
  match p.desc with
  | P_wild -> at P_wild
  | P_bind v -> (
      match Hashtbl.find_opt st.locals v.id with
      | Some earlier ->
          (* The same variable in another alternative of an or-pattern. *)
          expect st p.loc ~expected:earlier ty;
          at (P_bind v)
      | None ->
          Hashtbl.replace st.locals v.id ty;
          at (P_bind v))
  | P_int text ->
      let negative = String.length text > 0 && text.[0] = '-' in
      let digits =
        if negative then String.sub text 1 (String.length text - 1) else text
      in
      let lit = literal st ~text:digits ~negative ~float:false p.loc in
      expect st p.loc ~expected:ty lit;
      st.int_patterns <- (ty, p.loc) :: st.int_patterns;
      at (P_int text)
  | P_str s ->
      expect st p.loc ~expected:ty T.str;
      at (P_str s)
  | P_bool b ->
      expect st p.loc ~expected:ty T.bool;
      at (P_bool b)
  (* variadics.pack-tuples: a pack tuple's arity isn't known. *)
  | P_tuple ps when Packs.has_spread ty ->
      error st Code.e0342 p.loc
        "`%s` has as many elements as its pack, which this body doesn't know, \
         so no pattern takes it apart; map over it with a spread, as `(..e)`"
        (show ty);
      List.iter (unchecked st) ps;
      at P_error
  | P_tuple ps ->
      let items =
        shaped st p.loc ty
          (List.map (fun (q : Hir.pattern) -> fresh st q.loc) ps)
          (fun items -> T.Tuple items)
      in
      at (P_tuple (List.map2 (pattern ctx) ps items))
  | P_const item -> at (const_pattern st p ty item)
  | P_assoc_const (hty, name) -> at (assoc_const_pattern ctx p ty hty name)
  | P_variant (item, ps) -> at (variant_pattern ctx p ty item ps)
  | P_bare (n, ps, fallback) -> at (bare_pattern ctx p ty n ps fallback)
  | P_record (hty, fields, rest) -> at (record_pattern ctx p ty hty fields rest)
  | P_fields (fields, rest) -> at (fields_pattern ctx p ty fields rest)
  | P_list (ps, rest) -> at (list_pattern ctx p ty ps rest)
  | P_or alternatives ->
      at (P_or (List.map (fun q -> pattern ctx q ty) alternatives))
  | P_error ->
      st.broken <- true;
      at P_error

and variant_pattern ctx (p : Hir.pattern) ty (item : Hir.item) ps :
    A.pattern_desc =
  let st = ctx.st in
  match Env.variant st.env item with
  | Some (owner, _, payload) ->
      let _, args, info = instantiate_type st p.loc owner in
      let args = shaped st p.loc ty args (fun args -> T.Con (owner, args)) in
      let payload =
        List.map (T.subst (List.combine info.params args) []) payload
        |> Check_meta.payload owner args
      in
      if List.length payload <> List.length ps then (
        error st Code.e0315 p.loc
          "`%s` has %d payload field%s, but the pattern has %d" item.name
          (List.length payload)
          (if List.length payload = 1 then "" else "s")
          (List.length ps);
        List.iter (fun q -> ignore (pattern ctx q T.Error)) ps;
        P_error)
      else P_variant (item, List.map2 (pattern ctx) ps payload)
  | None -> P_error

(* patterns.variants-by-type: a name without a module names the variant of the type
   matched, before any other meaning, and otherwise what it names in scope. *)
and bare_pattern ctx (p : Hir.pattern) ty (n : Hir.name) ps fallback =
  let st = ctx.st in
  let named = Hashtbl.replace st.bare p.loc in
  match (matched_variant st ty n.desc, fallback) with
  | Some item, _ | None, Scope_variant item ->
      named (Named_variant item);
      variant_pattern ctx p ty item ps
  | None, Scope_const item ->
      named Named_const;
      const_pattern st p ty item
  | None, (Scope_error | Scope_failure _) ->
      named Named_error;
      (match fallback with Scope_failure d -> failed st ty n d | _ -> ());
      st.broken <- true;
      List.iter (unchecked st) ps;
      P_error

and record_pattern ctx (p : Hir.pattern) ty (hty : Hir.ty) fields rest :
    A.pattern_desc =
  let st = ctx.st in
  let rty = named_type st hty in
  expect st p.loc ~expected:ty rty;
  match record_fields st rty with
  | Some declared -> field_patterns ctx hty.loc rty declared fields rest
  | None ->
      if T.resolve rty <> Error then
        error st Code.e0311 hty.loc "`%s` is not a record type" (show rty);
      List.iter
        (fun (f : Hir.field_pattern) -> ignore (pattern ctx f.pattern T.Error))
        fields;
      P_error

(* records.anonymous-patterns: [{ f, .. }] matches a value of a type known to have the
   field [f], and without [..] it names every field of an anonymous record,
   which a type parameter's bound never says it names. *)
and fields_pattern ctx (p : Hir.pattern) ty fields rest : A.pattern_desc =
  let st = ctx.st in
  let unchecked () =
    List.iter
      (fun (f : Hir.field_pattern) -> ignore (pattern ctx f.pattern T.Error))
      fields;
    A.P_error
  in
  match known st p.loc ty with
  | None -> unchecked ()
  | Some t -> (
      match Env.record_fields st.env t with
      | Some declared ->
          let bounded = match T.resolve t with Param _ -> true | _ -> false in
          if bounded && not rest then
            error st Code.e0316 p.loc
              "`%s` may have fields that its bound doesn't name, so this \
               pattern ends with `..`"
              (show t);
          field_patterns ctx p.loc t declared fields (rest || bounded)
      | None ->
          error st Code.e0311 p.loc "`%s` is not a record type" (show t);
          unchecked ())

(* The fields of a pattern, matched against a record of type [rty] that has
   the fields [declared]: each once (E0316), each the type's (E0313), and
   every one unless [rest] (E0316, at [loc]). *)
and field_patterns ctx loc rty declared fields rest : A.pattern_desc =
  let st = ctx.st in
  let seen = ref [] in
  let fs =
    List.map
      (fun (f : Hir.field_pattern) ->
        match List.assoc_opt f.field.desc declared with
        | Some t ->
            if List.mem f.field.desc !seen then
              error st Code.e0316 f.field.loc "the field `%s` is matched twice"
                f.field.desc;
            seen := f.field.desc :: !seen;
            (f.field.desc, pattern ctx f.pattern t)
        | None ->
            error st Code.e0313 f.field.loc "`%s` has no field `%s`" (show rty)
              f.field.desc;
            (f.field.desc, pattern ctx f.pattern T.Error))
      fields
  in
  (if not rest then
     match List.filter (fun (n, _) -> not (List.mem n !seen)) declared with
     | [] -> ()
     | missing ->
         error st Code.e0316 loc
           "this pattern lacks the field%s %s; end it with `..` to ignore them"
           (if List.length missing = 1 then "" else "s")
           (String.concat ", " (List.map (fun (n, _) -> "`" ^ n ^ "`") missing)));
  P_record fs

and list_pattern ctx (p : Hir.pattern) ty ps (rest : Hir.list_rest) :
    A.pattern_desc =
  match Check_arrays.parts ty with
  | Some (elem, size) -> array_pattern ctx p ty elem size ps rest
  | None -> plain_list_pattern ctx p ty ps rest

(* generics.array-patterns: a list pattern matched against an array, whose length
   fits the array's size, checked here, so that it can't fail when its
   elements can't (E0311). *)
and array_pattern ctx (p : Hir.pattern) ty elem size ps rest =
  let st = ctx.st in
  let items = List.map (fun q -> pattern ctx q elem) ps in
  let n = List.length ps in
  Hashtbl.replace st.arrays p.loc ();
  (if not (Check_arrays.pattern_fits size n rest) then
     match rest with
     | Rest_bind v ->
         Hashtbl.replace st.locals v.id T.Error;
         error st Code.e0311 p.loc
           "a rest that binds a name would be an array whose size is \
            arithmetic; write `..` without a name"
     | Exact | Rest ->
         error st Code.e0311 p.loc
           "this pattern matches arrays of %s%d element%s, which `%s` isn't"
           (if rest = Rest then "at least " else "")
           n
           (if n = 1 then "" else "s")
           (show ty));
  let rest : A.list_rest =
    match rest with Exact -> Exact | Rest -> Rest | Rest_bind v -> Rest_bind v
  in
  P_list (items, rest)

and plain_list_pattern ctx (p : Hir.pattern) ty ps (rest : Hir.list_rest) :
    A.pattern_desc =
  let st = ctx.st in
  let elem =
    match
      shaped st p.loc ty
        [ fresh st p.loc ]
        (function [ elem ] -> T.list elem | _ -> T.Error)
    with
    | [ elem ] -> elem
    | _ -> T.Error
  in
  let items = List.map (fun q -> pattern ctx q elem) ps in
  let rest : A.list_rest =
    match rest with
    | Exact -> Exact
    | Rest -> Rest
    | Rest_bind v ->
        Hashtbl.replace st.locals v.id (T.list elem);
        Rest_bind v
  in
  P_list (items, rest)
