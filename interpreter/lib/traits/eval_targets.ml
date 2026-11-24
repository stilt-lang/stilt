(* What a call runs: the body of a function or a method, native code, a
   structural impl, a closure, or a variant's constructor. *)

open Tast
open Value
open Eval_state
module T = Types

(* Binds the parameters in a type, such as an impl's type, to the parts of a
   type that it matches. *)
let rec matching (pattern : T.ty) ty bound =
  match (pattern, T.resolve ty) with
  | Param v, ty -> (v, ty) :: bound
  | Con (_, ps), Con (_, ts) | Tuple ps, Tuple ts ->
      List.fold_left2 (fun bound p t -> matching p t bound) bound ps ts
  | Fn (ps, p, _), Fn (ts, t, _) ->
      List.fold_left2
        (fun bound (_, p) (_, t) -> matching p t bound)
        (matching p t bound) ps ts
  | _ -> bound

let bind (params : Env.bounds) targs =
  List.map2 (fun (v, _) t -> (v, t)) params targs

let drop n xs = List.filteri (fun i _ -> i >= n) xs

let member_signature t owner name =
  List.find_map
    (fun (m : Env.member) -> if m.name = name then Some m.signature else None)
    (Env.inherent_members t.env owner)

(* The type arguments of [impl] for the concrete type [ty]: those its type
   names, and those its member types imply (traits.member-types). *)
let impl_tenv t (impl : Env.impl) ty =
  match T.resolve ty with
  | Con (_, args) -> Env.impl_subst t.env [] impl args
  | _ -> matching impl.self_ty ty []

(* The type arguments of a trait's default member for the concrete type
   [ty]: its [Self], and the trait's parameters, as the impl for [ty] gives
   them (traits.trait-arguments). *)
let self_tenv t trait (info : Env.trait_info) ty =
  let args = Option.value ~default:[] (Env.trait_args t.env [] ty trait) in
  (info.self_param, ty)
  ::
  (if List.length args = List.length info.params then
     List.combine info.params args
   else [])

(* traits.trait-constants: the value of the constant [name] of [trait] for the
   concrete type [ty]: the impl's, or the trait's default with [ty] as its
   [Self]. *)
let trait_constant t trait name ty =
  let info = Option.get (Env.trait_info t.env trait) in
  let impl =
    match T.resolve ty with
    | Con (owner, _) ->
        Option.map
          (fun impl -> (owner, impl))
          (Env.trait_impl t.env ~trait owner)
    | _ -> None
  in
  let default () =
    match Hashtbl.find_opt t.default_constants (trait, name) with
    | Some (Code e) ->
        t.eval t
          (frame t ~home:trait.home
             ~tenv:(self_tenv t trait info ty)
             ~entry:None)
          e
    | Some Broken | Some Native | None ->
        invalid_arg "Eval_targets.trait_constant"
  in
  match impl with
  | Some (owner, impl)
    when List.exists (fun (m : Env.member) -> m.name = name) impl.members ->
      Lazy.force (Hashtbl.find t.impl_constants (trait, owner, name))
  | Some (_, impl) ->
      Option.iter
        (check_error t ~home:impl.module_)
        (List.assoc_opt name impl.unknown);
      let m =
        List.find
          (fun (m : Env.trait_method) -> m.method_name = name)
          info.methods
      in
      if not m.has_default then check_error t ~home:impl.module_ impl.loc;
      default ()
  | None -> default ()

(* What a call of [callee], with concrete type arguments, runs. A trait method
   runs the method of the impl for its type, the trait's default method, or the
   structural impl (traits.structural-calls). *)
let target t callee targs =
  let code (f : fn_def) params =
    match f.body with
    | Native -> Native_code (callee, targs)
    | Code _ | Broken -> Body (f, bind params targs)
  in
  match callee with
  | Operation _ -> invalid_arg "Eval_targets.target: an operation"
  | Function item ->
      let s = Option.get (Env.function_sig t.env item) in
      code (Hashtbl.find t.functions item) s.type_params
  | Member (owner, name) ->
      let s = Option.get (member_signature t owner name) in
      code (Hashtbl.find t.members (owner, name)) s.type_params
  | Trait_method (trait, name, ty) -> (
      let impl =
        match T.resolve ty with
        | Con (owner, _) ->
            Option.map
              (fun impl -> (owner, impl))
              (Env.trait_impl t.env ~trait owner)
        | _ -> None
      in
      match impl with
      | None -> Structural (name, ty)
      | Some (owner, impl) -> (
          match
            List.find_opt (fun (m : Env.member) -> m.name = name) impl.members
          with
          | Some m ->
              let own =
                drop (List.length impl.generics) m.signature.type_params
              in
              Body
                ( Hashtbl.find t.impl_methods (trait, owner, name),
                  impl_tenv t impl ty @ bind own targs )
          | None ->
              let info = Option.get (Env.trait_info t.env trait) in
              let m =
                List.find
                  (fun (m : Env.trait_method) -> m.method_name = name)
                  info.methods
              in
              (* program.check-error-report: a method that a syntax error leaves without
                 a signature panics at its name, and one the impl lacks at the
                 impl. *)
              Option.iter
                (check_error t ~home:impl.module_)
                (List.assoc_opt name impl.unknown);
              if not m.has_default then
                check_error t ~home:impl.module_ impl.loc;
              Body
                ( Hashtbl.find t.default_methods (trait, name),
                  self_tenv t trait info ty
                  @ bind m.method_sig.type_params targs )))

let target_of_fn t = function
  | Closure c -> Closure_body c
  | Function (callee, targs) -> target t callee targs
  | Constructor item -> Variant_of item
  | Poly _ -> invalid_arg "Eval_targets.target_of_fn: a polymorphic value"

(* polymorphism.instantiation: a function whose rigid types [sub] gives types. *)
let rec specialize sub = function
  | Function (callee, targs) ->
      let ty = Types.subst sub [] in
      let callee : Tast.callee =
        match callee with
        | Trait_method (trait, name, self) -> Trait_method (trait, name, ty self)
        | c -> c
      in
      Function (callee, List.map ty targs)
  | Closure c -> Closure { c with tenv = sub @ c.tenv }
  | Constructor _ as f -> f
  | Poly (vars, f) -> Poly (vars, specialize sub f)

let generalize vars = function Fn f -> Fn (Poly (vars, f)) | v -> v

let instantiate ts = function
  | Fn (Poly (vars, f)) -> Fn (specialize (List.combine vars ts) f)
  | v -> v
