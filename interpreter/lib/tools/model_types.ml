open Model_json

exception Outside of string

let outside fmt = Printf.ksprintf (fun s -> raise (Outside s)) fmt

type instance = {
  key : string;
  item : Hir.item;
  args : Types.ty list;
  generic : bool;
}

type target =
  | Function of Hir.item
  | Member of Hir.item * string
  | Impl of Hir.item * Hir.item * string

type fn_instance = {
  fkey : string;
  target : target;
  types_of : (Hir.var * Types.ty) list;
  rows_of : (Hir.var * Types.row) list;
}

(* A projection's body written for one access (projections.when-projection-runs): its
   [yield p] calls [k] with [p] and the places the access threads through it, [extras], all
   [inout], and keeps what [k] gives in the one-element list [res], which the body ends
   with. *)
type access = {
  res : string;
  result : Types.ty;
  k : Tast.expr;
  extras : Tast.expr list;
}

type cx = {
  env : Env.t;
  program : Tast.program;
  mutable types : instance list;
  mutable fns : fn_instance list;
  mutable reads_input : bool;
  mutable effects : (string * Model_json.t) list;
  mutable handlers : (string * Model_json.t) list;
  mutable lazy_met : bool;
  mutable when_met : bool;
      (* Whether the program has a lazy value, and a [when]
         (polymorphism.lazy-waits-for-nothing). *)
  mutable raises : Types.ty option;
      (* The error type of the code being written. *)
  mutable helpers : (string * Model_json.t) list;
      (* The functions the export writes of its own: [par.fold]'s tree at each type. *)
  mutable projections : (Hir.item * (Env.fn_sig * Tast.fn_def * access)) list;
      (* The projections written for an access, each a function of its own. *)
  mutable yielding : access option;
      (* The access of the projection whose body is being written. *)
  mutable writable : int list;
      (* The bindings of a view type that write their sources: [var]s and [inout]
         parameters (projections.writable-bindings). *)
}

let item_name (i : Hir.item) = i.home ^ "." ^ i.name

(* The names of a [when] written as another of its names, when their handles reach one
   value, whose place both stand for (shared.names-that-may-be-one-place). *)
let aliases : (int * Hir.var) list ref = ref []

let var_name (v : Hir.var) =
  let v = Option.value (List.assoc_opt v.id !aliases) ~default:v in
  v.name ^ "/" ^ string_of_int v.id

(* A type resolved, an array read as the list of its elements: a run can tell
   them apart by no value, index, order or text (generics.array-elements,
   generics.array-iteration and generics.array-traits), and the size an array
   type adds is checked before the run, as the interpreter runs an array as a
   list too. *)
let norm t =
  match Types.resolve t with
  | Con ({ home = "std.array"; name = "Array" }, [ e; _ ]) ->
      Types.Con ({ home = "std.prelude"; name = "List" }, [ e ])
  | t -> t

(* A record the calculus declares as the program writes it: the program's own, and the
   library's but [Set], which the calculus has as a type of its own (std.sets). *)
let declared_record (i : Hir.item) =
  not (i.home = "std.prelude" && i.name = "Set")

let int_kind t =
  match norm t with
  | Con ({ home = "std.prelude"; name }, [])
    when List.mem name Types.integer_types ->
      Some name
  | _ -> None

let float_kind t =
  match norm t with
  | Con ({ home = "std.prelude"; name = ("f32" | "f64") as name }, []) ->
      Some name
  | _ -> None

let elem t =
  match norm t with
  | Con ({ home = "std.prelude"; name = "List" }, [ e ]) -> e
  | _ -> outside "an iteration over something other than a list"

(* Whether the calculus's row holds [io], and its error type: code that performs [io], or
   an effect, whose handlers' bodies may perform [io] wherever the performance is
   (handlers.handler-types). *)
let flat (r : Types.row) =
  let r = Types.row_contents r in
  (match r.tail with Row_params _ -> outside "a row parameter" | _ -> ());
  (r.io || r.effects <> [], r.raise)

(* Runs [f] with [r]'s error type as the error type of the code it writes. *)
let raises_in cx r f =
  let saved = cx.raises in
  cx.raises <- snd (flat r);
  Fun.protect ~finally:(fun () -> cx.raises <- saved) f

let async_item = { Hir.home = "std.prelude"; name = "async" }
let mode : Ast.mode -> t = function Let -> Str "let" | Inout -> Str "inout"
let args_of t = match norm t with Types.Con (_, args) -> args | _ -> []

let params cx i =
  match Env.type_info cx.env i with Some info -> info.params | None -> []

let instantiated cx inst t =
  Types.subst (List.combine (params cx inst.item) inst.args) [] t

(* The calculus's key types (formal/Stilt/Maps.lean, [Ty.Key]), whose values a map compares
   part by part: the integer types, [bool], [str] and [()], whose [Eq] and [Hash] are built in,
   and the tuples, lists, records and variant types made of them whose impls are the
   structural ones, which the program writes for none of them (traits.structural-impls). *)
let key cx t =
  let written i name =
    Env.trait_impl cx.env ~trait:{ Hir.home = "std.prelude"; name } i <> None
  in
  let rec go seen t =
    match norm t with
    | Con ({ home = "std.prelude"; name }, []) ->
        List.mem name Types.integer_types || name = "bool" || name = "str"
    | Con ({ home = "std.prelude"; name = "List" }, [ e ]) -> go seen e
    | Tuple ts -> List.for_all (go seen) ts
    | Record fields -> List.for_all (fun (_, t) -> go seen t) fields
    | Con (i, _) when List.mem i seen -> true
    | Con (i, args) when not (written i "Eq" || written i "Hash") -> (
        let sub t =
          instantiated cx { key = ""; item = i; args; generic = false } t
        in
        let parts ts = List.for_all (fun t -> go (i :: seen) (sub t)) ts in
        match Env.type_info cx.env i with
        | Some { Env.def = Env.Record fields; _ } when declared_record i ->
            parts (List.map snd fields)
        | Some { Env.def = Env.Variants ctors; _ } ->
            List.for_all (fun (_, ts) -> parts ts) ctors
        | _ -> false)
    | _ -> false
  in
  go [] t

(* Records an [inout] binding of a view type as writable (projections.writable-bindings). *)
let writes cx (m : Ast.mode) (v : Hir.var) t =
  match (m, norm t) with
  | Ast.Inout, Types.Con ({ home = "std.view"; name = "View" }, [ _ ]) ->
      cx.writable <- v.id :: cx.writable
  | _ -> ()

let rec ty cx (t : Types.ty) =
  match norm t with
  | Con ({ home = "std.prelude"; name }, [])
    when List.mem name Types.integer_types ->
      tag "int" [ Str name ]
  | Con ({ home = "std.prelude"; name = ("bool" | "str") as name }, []) ->
      Str name
  | Con ({ home = "std.prelude"; name = ("f32" | "f64") as name }, []) ->
      tag "float" [ Str name ]
  | Con ({ home = "std.prelude"; name = "Never" }, []) -> Str "never"
  | Con ({ home = "std.prelude"; name = "List" }, [ e ]) ->
      tag "list" [ ty cx e ]
  | Con ({ home = "std.prelude"; name = "Map" }, [ k; v ]) when key cx k ->
      tag "map" [ ty cx k; ty cx v ]
  | Con ({ home = "std.prelude"; name = "Map" }, _) ->
      outside
        "a map whose keys the calculus may not compare as the program does"
  | Con ({ home = "std.prelude"; name = "Set" }, [ e ]) when key cx e ->
      tag "set" [ ty cx e ]
  (* views.what-view-is: a view of a viewable type (views.viewable-types). *)
  | Con ({ home = "std.view"; name = "View" }, [ t ]) -> tag "view" [ ty cx t ]
  | Con ({ home = "std.prelude"; name = "Set" }, _) ->
      outside
        "a set whose elements the calculus may not compare as the program does"
  (* polymorphism.lazy-unobservable: no program can tell when a lazy value's function
     runs, or how often, and its row is empty, so a [Lazy<T>] is its [fn() -> T]. *)
  | Con ({ home = "std.lazy"; name = "Lazy" }, [ t ]) ->
      (* polymorphism.lazy-waits-for-nothing: a [when] that runs while a lazy value is
         computed panics, which a call of its function doesn't show. *)
      cx.lazy_met <- true;
      ty cx (Fn ([], t, Types.empty_row))
  | Tuple [] -> Str "unit"
  | Tuple ts -> tag "tuple" [ Arr (List.map (ty cx) ts) ]
  | Fn (ps, r, rw) -> fn_ty cx ps r rw
  (* shared.std-sync: a handle names a cell of the world; tasks.sequential-run: a task's
     handle is the value it ended with, and a scope and the handlers of [async] hold
     nothing a run reads. *)
  | Con ({ home = "std.sync"; name = "Shared" }, [ t ]) ->
      tag "shared" [ ty cx t ]
  | Con ({ home = "std.task"; name = "Task" }, [ t ]) -> ty cx t
  | Con ({ home = "std.task"; name = "Scope" }, [ _ ]) -> Str "unit"
  | Handler h when h.eff = async_item -> Str "unit"
  | Record fields -> tag "record" [ Str (anonymous cx fields) ]
  | Handler h -> tag "record" [ Str (handler_record cx h) ]
  | Con (i, args) -> (
      let named kind =
        match declared_args cx i args with
        | name, [] -> tag kind [ Str name ]
        | name, args -> tag kind [ Str name; Arr args ]
      in
      match Env.type_info cx.env i with
      | Some { Env.def = Env.Record _; _ } when declared_record i ->
          named "record"
      | Some { Env.def = Env.Variants _; _ } -> named "variant"
      | _ -> outside "a type the model lacks")
  (* A type parameter of a generic type, in its declaration. *)
  | Param v -> tag "param" [ Str v.name ]
  | _ -> outside "a type the model lacks"

(* A function type. *)
and fn_ty cx ps r rw =
  let params = List.map (fun (m, t) -> Arr [ mode m; param_ty cx (m, t) ]) ps in
  tag "fn" [ Arr params; ty cx r; row cx rw ]

(* The type of a parameter: an [inout] one of a view type is writable, which the calculus
   holds as the copy of its part (projections.writable-bindings). *)
and param_ty cx (m, t) =
  match (m, norm t) with
  | Ast.Inout, Con ({ home = "std.view"; name = "View" }, [ u ]) -> ty cx u
  | _ -> ty cx t

(* A type the calculus declares: a record or a variant type, at its arguments. *)
and declared cx (i : Hir.item) args = fst (declared_args cx i args)

(* A record or a variant type, at its arguments: declared once, with its type
   parameters, which each use gives its arguments (declarations.type-parameters
   and declarations.type-arguments), when every part of its declaration is a form
   of the calculus there; and otherwise, as for a type with value parameters, once
   for each list of arguments, named by them. *)
and declared_args cx (i : Hir.item) args =
  if generic cx i args then (item_name i, List.map (ty cx) args)
  else (declared_at cx i args, [])

(* Whether the calculus declares [i] once, with its type parameters: decided at
   the first use, by writing its declaration's types at its parameters. *)
and generic cx (i : Hir.item) args =
  let value a = match norm a with Types.Value _ -> true | _ -> false in
  match List.find_opt (fun inst -> inst.item = i) cx.types with
  | Some inst -> inst.generic && not (List.exists value args)
  | None -> (
      let ps = params cx i in
      let parts =
        match Env.type_info cx.env i with
        | Some { Env.def = Env.Record fields; _ } when declared_record i ->
            Some (List.map snd fields)
        | Some { Env.def = Env.Variants ctors; _ } ->
            Some (List.concat_map snd ctors)
        | _ -> None
      in
      match parts with
      | Some parts
        when ps <> []
             && List.length ps = List.length args
             && not (List.exists value args) -> (
          let inst =
            {
              key = item_name i;
              item = i;
              args = List.map (fun v -> Types.Param v) ps;
              generic = true;
            }
          in
          cx.types <- inst :: cx.types;
          try
            List.iter (fun t -> ignore (ty cx t)) parts;
            true
          with Outside _ ->
            cx.types <- List.filter (fun j -> j != inst) cx.types;
            false)
      | _ -> false)

(* A type the calculus declares once for each list of arguments, named by them. *)
and declared_at cx (i : Hir.item) args =
  (match Env.type_info cx.env i with
  | Some { Env.params; def = Env.Variants _; _ }
    when List.length params = List.length args ->
      ()
  | Some { Env.params; def = Env.Record _; _ }
    when List.length params = List.length args && declared_record i ->
      ()
  | Some { Env.def = Env.Record _; _ } -> outside "a record of the library"
  | Some { Env.def = Env.Variants _; _ } ->
      outside "a variant type with arguments of another number"
  | _ -> outside "the type %s" (item_name i));
  if List.exists has_param args then
    outside "a type at a parameter of a type declared at its arguments";
  let key =
    match args with
    | [] -> item_name i
    | _ ->
        item_name i ^ "<"
        ^ String.concat ", " (List.map (type_arg cx) args)
        ^ ">"
  in
  if not (List.exists (fun inst -> inst.key = key) cx.types) then
    cx.types <- { key; item = i; args; generic = false } :: cx.types;
  key

(* An anonymous record type, which the calculus declares as a record named by the type's
   own text, [{ f: T, … }], with its fields in the alphabetical order of their names
   (records.anonymous-types and records.field-order), a name no declaration can have. *)
and anonymous cx fields =
  let field (f, t) = f ^ ": " ^ Model_json.to_string (ty cx t) in
  let key = "{ " ^ String.concat ", " (List.map field fields) ^ " }" in
  if not (List.exists (fun inst -> inst.key = key) cx.types) then
    cx.types <-
      { key; item = Types.anonymous; args = [ Record fields ]; generic = false }
      :: cx.types;
  key

(* The record the calculus declares for a record type: a declared record's instance, or
   an anonymous record type's own. *)
and record_name cx t =
  match norm t with
  | Con (i, args) when declared_record i -> declared cx i args
  | Record fields -> anonymous cx fields
  | _ -> outside "a record of a type the model lacks"

(* Whether a type parameter occurs in a type. *)
and has_param t =
  match norm t with
  | Param _ -> true
  | Con (_, ts) | Tuple ts -> List.exists has_param ts
  | Record fs -> List.exists (fun (_, t) -> has_param t) fs
  | Fn (ps, r, _) -> List.exists (fun (_, t) -> has_param t) ps || has_param r
  | _ -> false

(* The type arguments the calculus writes a record type with. *)
and record_args cx t =
  match norm t with
  | Con (i, args) when declared_record i -> snd (declared_args cx i args)
  | _ -> []

(* The type parameters of a declared type, by their names. *)
and type_params cx inst =
  if inst.generic then
    Arr (List.map (fun (v : Hir.var) -> Str v.name) (params cx inst.item))
  else Arr []

(* A type argument as an instance's name writes it: a type as the calculus has it, and a
   value argument as written (generics.value-parameters). *)
and type_arg cx a =
  match norm a with Value text -> text | a -> Model_json.to_string (ty cx a)

and row cx r =
  let io, raise = flat r in
  let raise = match raise with None -> Null | Some t -> ty cx t in
  (* tasks.sequential-run: [async] performs nothing but what its tasks' calls do, so a row
     that holds it holds [io] in the calculus, as one that holds an effect does. *)
  let user (e, _) = e <> async_item in
  match List.filter user (Types.row_contents r).effects with
  | [] -> Arr [ Bool io; raise; Arr [] ]
  | effects ->
      let key (e, args) = Str (effect_key cx e args) in
      Arr [ Bool io; raise; Arr []; Arr (List.map key effects); Null ]

(* An effect's operations at its arguments: each with its parameters as one value, [()]
   for none and a tuple for several, its result and its own row
   (handlers.declaring-effect). *)
and operations cx (eff : Hir.item) args =
  match Env.effect_info cx.env eff with
  | Some info when List.length info.eparams = List.length args ->
      let sub t = Types.subst (List.combine info.eparams args) [] t in
      let param (_, t) = sub t in
      let one (name, (o : Env.operation_sig)) =
        let arg =
          match o.op_params with
          | [ p ] -> param p
          | ps -> Types.Tuple (List.map param ps)
        in
        (name, arg, sub o.op_ret)
      in
      List.map one info.ops
  | _ -> outside "the effect %s" (item_name eff)

(* An effect at its arguments, which the calculus declares once, named by them. *)
and effect_key cx (eff : Hir.item) args =
  let key =
    match args with
    | [] -> item_name eff
    | _ ->
        item_name eff ^ "<"
        ^ String.concat ", " (List.map (type_arg cx) args)
        ^ ">"
  in
  if not (List.mem_assoc key cx.effects) then (
    cx.effects <- (key, Null) :: cx.effects;
    let op (name, a, b) = Arr [ Str name; Arr [ ty cx a; ty cx b ] ] in
    let decl = Arr [ Str key; Arr (List.map op (operations cx eff args)) ] in
    cx.effects <- (key, decl) :: List.remove_assoc key cx.effects);
  key

(* A handler type, which the calculus declares as a record of closures, one for each
   operation under its name: each takes the operation's argument and gives its result, or the [with]'s for a handler that takes control, whose body's row
   then holds [resume] (handlers.handler-types and handlers.resuming). *)
and handler_record cx (h : Types.handler) =
  let eff = effect_key cx h.eff h.hargs in
  let answer = Option.map (ty cx) h.answer in
  let key =
    "handler " ^ eff
    ^ match answer with Some r -> " -> " ^ Model_json.to_string r | None -> ""
  in
  if not (List.mem_assoc key cx.handlers) then (
    cx.handlers <- (key, Null) :: cx.handlers;
    let field (name, a, b) =
      let b = ty cx b in
      let resume = match answer with Some r -> Arr [ b; r ] | None -> Null in
      let rw = Arr [ Bool true; Null; Arr []; Arr []; resume ] in
      let a = Arr [ Arr [ Str "let"; ty cx a ] ] in
      Arr [ Str name; tag "fn" [ a; Option.value answer ~default:b; rw ] ]
    in
    let fields = List.map field (operations cx h.eff h.hargs) in
    cx.handlers <-
      (key, Arr [ Str key; Arr fields ]) :: List.remove_assoc key cx.handlers);
  key

let with_args = function [] -> [] | args -> [ Arr args ]
