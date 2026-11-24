open Tast
module T = Types
open Implicit_names
open Implicit_sites

type t = {
  effects : (Ast.limit * (key, unit) Hashtbl.t) list;
  sites : (key, site list) Hashtbl.t;
}

(* program.prelude-functions, std.str and std.lists, and std.integers: the native
   functions that can panic, other than by [overflow] (effects.panicking-operations). *)
let native_panics = function
  | Function
      {
        home = "std.prelude";
        name = "panic" | "unreachable" | "unwrap_failed" | "expect_failed";
      } ->
      true
  | Member ({ home = "std.prelude"; name = "str" }, "slice") -> true
  | Member
      ({ home = "std.prelude"; name = "List" }, ("insert" | "remove" | "slice"))
    ->
      true
  | Member ({ home = "std.prelude"; name }, ("div_euclid" | "rem_euclid")) ->
      Option.is_some (Ints.of_name name)
  (* views.functions-of-views *)
  | Member ({ home = "std.view"; name = "View" }, ("of" | "view")) -> true
  (* generics.array-effects *)
  | Function { home = "std.array"; name = "fill" } -> true
  (* c.lending-buffer *)
  | Member ({ home = "std.prelude"; name = "str" }, "with_c_str") -> true
  | _ -> false

(* Whether a type names [str], [List] or [Map], at any depth. *)
let rec names_heap (ty : T.ty) =
  match T.resolve ty with
  | Con (item, args) ->
      List.mem item (List.map T.prelude_item [ "str"; "List"; "Map" ])
      || List.exists names_heap args
  | Tuple ts -> List.exists names_heap ts
  | Record fields -> List.exists (fun (_, t) -> names_heap t) fields
  | Spread (_, t) -> names_heap t
  | Fn (ps, ret, _) ->
      List.exists (fun (_, t) -> names_heap t) ps || names_heap ret
  | Forall p -> names_heap p.body
  | Handler h -> List.exists names_heap (h.hargs @ Option.to_list h.answer)
  | App (_, ts) -> List.exists names_heap ts
  | Param _ | Var _ | Value _ | Error -> false

(* facts.native-allocation: the native methods that allocate nothing. *)
let member_allocation_free (owner : Hir.item) name =
  let prelude n = owner.home = "std.prelude" && owner.name = n in
  let number =
    owner.name = "f32" || owner.name = "f64"
    || Option.is_some (Ints.of_name owner.name)
  in
  let starts p =
    String.length name >= String.length p
    && String.sub name 0 (String.length p) = p
  in
  match owner.home with
  | "std.prelude" when number -> true
  | "std.array" | "std.meta" -> true
  | "std.prelude" when prelude "str" ->
      List.mem name
        [
          "len";
          "is_empty";
          "contains";
          "starts_with";
          "ends_with";
          "find";
          "rfind";
          "count";
          "char_count";
          "to_i8";
          "to_i16";
          "to_i32";
          "to_i64";
          "to_u8";
          "to_u16";
          "to_u32";
          "to_u64";
          "to_f32";
          "to_f64";
        ]
      || starts "is_ascii"
  | "std.prelude" when prelude "List" ->
      List.mem name [ "len"; "is_empty"; "get"; "with_ptr" ]
  | "std.prelude" when prelude "Map" ->
      List.mem name [ "len"; "is_empty"; "contains"; "get" ]
  | "std.view" when owner.name = "View" ->
      List.mem name [ "of"; "all"; "len"; "is_empty"; "view" ]
  | "std.c" when owner.name = "Ptr" ->
      List.mem name [ "is_null"; "offset"; "address"; "read"; "write" ]
  | "std.c" when owner.name = "Str" -> name = "is_null"
  | _ -> false

(* facts.native-allocation: the native functions, not methods, that allocate
   nothing. *)
let function_allocation_free (item : Hir.item) =
  match item.home with
  | "std.math" | "std.array" | "std.meta" -> true
  (* projections.writable-views: [into] and [split] allocate at their calls,
     where they aren't in place, which their sites carry (facts.writes-in-place). *)
  | "std.view" -> List.mem item.name [ "get"; "part"; "into"; "split" ]
  | "std.c" -> item.name = "null"
  | "std.clock" -> List.mem item.name [ "unix_ms"; "monotonic_ns"; "sleep_ms" ]
  | "std.random" -> item.name = "entropy"
  | _ -> false

(* facts.native-allocation: every native function allocates, but for those the
   Reference lists, a native whose result type is [Never] among them, which ends
   the program. A method of a built-in impl allocates when its declared result
   type names [str], [List] or [Map]. *)
let native_allocates env key =
  let ends () =
    match signature env key with
    | Some s -> (
        match T.resolve s.ret with
        | Con ({ home = "std.prelude"; name = "Never" }, _) -> true
        | _ -> false)
    | None -> false
  in
  match key with
  | Built_in _ -> (
      match signature env key with
      | Some s ->
          names_heap s.ret
          || List.exists
               (fun (mode, t) -> mode = Ast.Inout && names_heap t)
               s.params
      | None -> false)
  | Member (owner, name) -> not (member_allocation_free owner name)
  | Function item -> not (function_allocation_free item || ends ())
  | Impl_method _ | Default_method _ -> true

let bodies (program : program) =
  List.map (fun (item, f) -> (Function item, f)) program.functions
  @ List.map
      (fun ((owner, name), f) -> (Member (owner, name), f))
      program.members
  @ List.map
      (fun ((trait, owner, name), f) -> (Impl_method (trait, owner, name), f))
      program.impl_methods
  @ List.map
      (fun ((trait, name), f) -> (Default_method (trait, name), f))
      program.default_methods

(* facts.inference: the items with an effect, as a least fixed point over the items
   that each body names. [summaries] holds each body's key, whether it has
   the effect itself, and what it names; [base] tells whether an item without
   a body of its own has the effect. *)
let fixed_point summaries ~base =
  let known = Hashtbl.create 64 in
  let rec fix () =
    let grew =
      List.fold_left
        (fun grew (key, direct, names) ->
          if
            (not (Hashtbl.mem known key))
            && (direct
               || List.exists (fun k -> base k || Hashtbl.mem known k) names)
          then (
            Hashtbl.replace known key ();
            true)
          else grew)
        false summaries
    in
    if grew then fix ()
  in
  fix ();
  known

let has_fact limit (s : site) = List.mem_assoc limit s.facts

let built_in_allocates env = function
  | Built_in _ as key -> native_allocates env key
  | _ -> false

(* c.effects: whether [key] is a foreign function, with whether its row holds
   [io]. A call of one adds [panic], [alloc] and [div], and every capability
   when its row holds [io], but what its declaration's own [without] clause
   names: no module's limit covers C code. *)
let foreign env key =
  match key with
  | Function item when Env.is_foreign env item ->
      Some
        (match Env.function_sig env item with
        | Some s -> s.row.io
        | None -> false)
  | _ -> None

let foreign_has io : Ast.limit -> bool = function
  | Panic | Alloc | Div -> true
  | Capability _ -> io
  | Overflow | Copy | Locks | Unsafe -> false

(* What an item without a body of its own has: a native's [panic] and
   [alloc] (facts.native-allocation; effects.without-panic), and its capability (facts.capability-natives).
   Only [Lazy.get] and [std.task]'s [spawn], which call a stored function
   value, have [div] (polymorphism.lazy-implicit-effects; tasks.implicit-effects-and-capabilities), and no native has
   [copy] (facts.div and facts.copy). *)
let native_of_std env (limit : Ast.limit) key =
  match limit with
  | Panic -> native_panics key
  (* effects.overflow-effect, and std.integers: an integer type's [abs], [pow],
     [div_euclid], [rem_euclid], [gcd] and [lcm]. *)
  | Overflow -> (
      match key with
      | Member
          ( { home = "std.prelude"; name },
            ("abs" | "pow" | "div_euclid" | "rem_euclid" | "gcd" | "lcm") ) ->
          Option.is_some (Ints.of_name name)
      | _ -> false)
  | Alloc -> native_allocates env key
  | Div ->
      key = Member ({ home = "std.lazy"; name = "Lazy" }, "get")
      || key = Function { home = "std.task"; name = "spawn" }
      (* tasks.implicit-effects-and-capabilities *)
      || key = Member ({ home = "std.task"; name = "Scope" }, "spawn")
  | Copy -> false
  | Capability c -> Implicit_capabilities.native key = Some c
  (* shared.locks: only a [when] holds a shared value, and no native runs
     one. *)
  | Locks -> false
  (* c.unsafe-and-foreign: only a body's own [unsafe] block, which nothing
     inherits. *)
  | Unsafe -> false

let native env limit key =
  match foreign env key with
  | Some io -> foreign_has io limit
  | None -> native_of_std env limit key

(* The items with one effect. A body limited by [limit] counts as not
   having it, since its operations that have it are errors where they are
   written (effects.without-panic; effects.marking; facts.without-div and facts.without-copy). *)
let items_with env program sites ~limited limit =
  List.filter_map
    (fun (key, (f : fn_def)) ->
      let limited =
        if Option.is_some (foreign env key) then List.mem limit f.limits
        else limited limit f
      in
      if limited then None
      else
        match f.body with
        | Code _ ->
            let ss = Option.value (Hashtbl.find_opt sites key) ~default:[] in
            Some
              ( key,
                List.exists (has_fact limit) ss,
                List.concat_map (fun (s : Implicit_sites.site) -> s.names) ss )
        | Native -> Some (key, native env limit key, [])
        | Broken -> None)
    (bodies program)
  |> fixed_point ~base:(fun k -> limit = Ast.Alloc && built_in_allocates env k)

(* facts.capabilities, facts.capability-natives and facts.calls-through-function-values: a body's capabilities follow the items it names,
   which a call through a function value doesn't add to. *)
let capabilities env program =
  let summaries =
    List.filter_map
      (fun (key, (f : fn_def)) ->
        match f.body with
        | Code block -> Some (key, [], Implicit_sites.names env block)
        | Native -> (
            match foreign env key with
            | Some io ->
                let has c = io && not (List.mem (Ast.Capability c) f.limits) in
                Some (key, List.filter has Capability.all, [])
            | None ->
                Some (key, Option.to_list (Implicit_capabilities.native key), [])
            )
        | Broken -> None)
      (bodies program)
  in
  let tables =
    List.map
      (fun c ->
        ( c,
          fixed_point
            ~base:(fun _ -> false)
            (List.map (fun (k, n, names) -> (k, List.mem c n, names)) summaries)
        ))
      Capability.all
  in
  fun key ->
    List.filter_map
      (fun (c, known) -> if Hashtbl.mem known key then Some c else None)
      tables

let infer env program ~limited =
  let sites = Hashtbl.create 64 in
  let constant = Accept.constants program in
  let verify key (f : fn_def) block =
    Accept.body env ~constant ~key:(Some key) ~params:f.params (`Block block)
  in
  List.iter
    (fun (k, ss) -> Hashtbl.replace sites k ss)
    (Implicit_bodies.sites env ~limited ~verify (bodies program));
  {
    effects =
      List.map
        (fun l -> (l, items_with env program sites ~limited l))
        ([ Ast.Panic; Overflow; Alloc; Div; Copy; Locks ]
        @ List.map (fun c -> Ast.Capability c) Capability.all);
    sites;
  }

let describe : Ast.limit -> string = function
  | Panic -> "can panic"
  | Overflow -> "can overflow"
  | Alloc -> "allocates"
  | Div -> "may never end"
  | Copy -> "copies shared data"
  | Capability c -> Printf.sprintf "has the capability `%s`" (Capability.name c)
  | Locks -> "holds shared values"
  | Unsafe -> "holds an `unsafe` block"

(* Whether [k] has the effect that [limit] limits. *)
let has env t limit k =
  (limit = Ast.Alloc && built_in_allocates env k)
  || Hashtbl.mem (List.assoc limit t.effects) k

(* The message of an operation that names [k], which has the effect that
   [limit] limits. A capability's says where [k] gets it: from the native
   that its body names first, or from the native that [k] is (facts.without). *)
let named env t limit k =
  let beyond = Capability.limit_name limit in
  match limit with
  | Capability c ->
      (* The items that pass the capability on, down to the native, each
         with where the one before names it. *)
      let rec chain seen k =
        Option.value (Hashtbl.find_opt t.sites k) ~default:[]
        |> List.find_map (fun s ->
            List.find_opt (has env t limit) s.names
            |> Option.map (fun n -> (n, s.loc)))
        |> function
        | Some (n, at) when not (List.mem n seen) ->
            (n, at) :: chain (n :: seen) n
        | _ -> []
      in
      Implicit_capabilities.named ~through:(chain [ k ] k) c k
      ^ ", beyond `without " ^ beyond ^ "`"
  | _ ->
      Printf.sprintf "this uses `%s`, which %s, beyond `without %s`"
        (show_key k) (describe limit) beyond

(* facts.closest-rule: what the rule of acceptance closest to an operation that
   goes beyond a limit needs. *)
let noted limit (s : site) message =
  match List.assoc_opt limit s.notes with
  | Some note -> message ^ ": " ^ note
  | None -> message

(* effects.without-panic, effects.marking, and facts.without-div and facts.without-copy: the errors of a body
   for one limit. An operation that has the effect itself, such as a call of
   its own recursive group, isn't reported again for the item it names. *)
let errors_for env t ~file sites limit =
  let name = Capability.limit_name limit in
  (* Only an operator overflows itself, never a call, so a call where an
     overflow starts is another operation. *)
  let direct =
    if limit = Ast.Overflow then []
    else
      List.filter_map
        (fun s -> if List.mem_assoc limit s.facts then Some s.loc else None)
        sites
  in
  List.filter_map
    (fun s ->
      match List.assoc_opt limit s.facts with
      | Some fact ->
          Some
            (Diagnostic.at ~file Code.e0204 s.loc
               (noted limit s
                  (Printf.sprintf "%s, beyond `without %s`" fact name)))
      | None when List.mem s.loc direct -> None
      | None ->
          List.find_opt (has env t limit) s.names
          |> Option.map (fun k ->
              Diagnostic.at ~file Code.e0204 s.loc
                (noted limit s (named env t limit k))))
    sites

(* facts.without: of the errors of one limit, one for each line, at the first of its
   operations, which names the others. *)
let first_of_each_line (ds : Diagnostic.t list) =
  let sorted =
    List.stable_sort
      (fun (a : Diagnostic.t) (b : Diagnostic.t) ->
        compare (a.line, a.col) (b.line, b.col))
      ds
  in
  List.fold_left
    (fun kept (d : Diagnostic.t) ->
      match kept with
      | (last : Diagnostic.t) :: _ when last.line = d.line -> kept
      | _ -> d :: kept)
    [] sorted
  |> List.rev

let limit_errors env t ~file ~limits ~key block =
  (* c.without-unsafe: [unsafe] is no implicit effect, and a body's own blocks
     are checked apart. *)
  let limits = List.filter (fun l -> l <> (Ast.Unsafe : Ast.limit)) limits in
  if limits = [] then []
  else
    let sites =
      match Option.bind key (Hashtbl.find_opt t.sites) with
      | Some ss -> ss
      | None -> Implicit_sites.sites env Implicit_sites.no_in_place block
    in
    List.concat_map
      (fun l -> first_of_each_line (errors_for env t ~file sites l))
      limits

(* The function that each call of [Lazy.new] in a block keeps, as a block of
   one expression: its argument, or the closure literal that a [let] binds to
   the local its argument names (polymorphism.lazy-values). *)
let lazy_functions block =
  let closures = Hashtbl.create 8 in
  Walk.iter_block
    ~stmt:(fun s ->
      match s.stmt with
      | Let { pattern = { pat = P_bind v; _ }; value; _ } -> (
          match value.desc with
          | Closure _ -> Hashtbl.replace closures v.id value
          | _ -> ())
      | _ -> ())
    ignore block;
  let found = ref [] in
  Walk.iter_block
    (fun (e : expr) ->
      match e.desc with
      | Call (Member ({ home = "std.lazy"; name = "Lazy" }, "new"), _, a :: _, _)
        ->
          let f =
            match a.value.desc with
            | Local v ->
                Option.value (Hashtbl.find_opt closures v.id) ~default:a.value
            | _ -> a.value
          in
          found := [ { stmt = Expr f; at = f.loc } ] :: !found
      | _ -> ())
    block;
  List.rev !found

(* shared.locks: a [when] whose block has a site of [locks], a [when] or
   a call of an item that has it, closure literals included, is E0430 at
   the site. A site inside several [when]s is reported once. polymorphism.lazy-waits-for-nothing:
   so is a site in the function that [Lazy.new] keeps, E0435, unless E0430
   reports it. *)
let lock_errors env t ~file block =
  let found = ref [] in
  let report code message (s : site) =
    let locks = has_fact Locks s || List.exists (has env t Locks) s.names in
    if locks && not (List.mem_assoc s.loc !found) then
      found := (s.loc, Diagnostic.at ~file code s.loc message) :: !found
  in
  let sites b = Implicit_sites.sites env Implicit_sites.no_in_place b in
  Walk.iter_block
    (fun (e : expr) ->
      match e.desc with
      | When (_, b) ->
          List.iter
            (report Code.e0430
               "this holds a shared value while this `when` holds others, \
                which could deadlock; name every value in one `when`")
            (sites b)
      | _ -> ())
    block;
  List.iter
    (fun f ->
      List.iter
        (report Code.e0435
           "a `Lazy`'s function must not wait, but this holds shared values; \
            read them before `Lazy.new`")
        (sites f))
    (lazy_functions block);
  List.rev_map snd !found
