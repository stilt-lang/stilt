open Tast
module T = Types

(* The constructors of patterns.algorithm. Lists have one constructor per length, and
   [At_least n] stands for every length from [n] on, once no pattern tells
   those lengths apart. *)
type ctor =
  | Variant of Hir.item
  | Bool of bool
  | Tuple of int
  | Record of Hir.item * string list  (** Its fields, in declaration order. *)
  | Int of string  (** {!Literal.int_canonical} of the literal. *)
  | Str of string
  | Len of int
  | At_least of int

type pat =
  | Wild
  | Ctor of ctor * pat list
  | Prefix of pat list  (** [[p₁, …, pₙ, ..]], lists of at least [n]. *)
  | Or of pat list

let wilds n = List.init n (fun _ -> Wild)

(* A type with an error, or one that inference left open because it met an
   error: only such variables are left in a body without errors. *)
let is_error ty = match T.resolve ty with Error | Var _ -> true | _ -> false

let is_prelude ty name =
  match T.resolve ty with
  | Con (item, _) -> item = T.prelude_item name
  | _ -> false

let subst (info : Env.type_info) args t =
  if List.length info.params = List.length args then
    T.subst (List.combine info.params args) [] t
  else T.Error

let record_fields env item =
  match Env.type_info env item with
  | Some { def = Record fields; _ } -> List.map fst fields
  | _ -> []

(* The types of a constructor's fields, for a value of type [ty]. *)
let field_types env ty ctor =
  let info item = Env.type_info env item in
  match (ctor, T.resolve ty) with
  | Variant v, Con (owner, args) -> (
      match (Env.variant env v, info owner) with
      | Some (_, _, payload), Some info -> List.map (subst info args) payload
      | _ -> [])
  | Tuple _, Tuple ts -> ts
  | Record (_, fields), (T.Record _ | Param _) ->
      let known = Option.value ~default:[] (Env.record_fields env ty) in
      List.map
        (fun f -> Option.value ~default:T.Error (List.assoc_opt f known))
        fields
  | Record (item, fields), Con (_, args) -> (
      match info item with
      | Some ({ def = Record declared; _ } as info) ->
          List.map (fun f -> subst info args (List.assoc f declared)) fields
      | _ -> [])
  | (Len n | At_least n), Con (_, [ elem ]) -> List.init n (fun _ -> elem)
  (* generics.array-patterns: an array of size [n] is matched as a tuple of [n]
     elements. *)
  | Tuple n, t when Option.is_some (Check_arrays.parts t) ->
      List.init n (fun _ -> fst (Option.get (Check_arrays.parts t)))
  | _ -> []

let arity env ty ctor = List.length (field_types env ty ctor)

(* The rule, as patterns.types-without-values states it: the types that have values are the
   smallest set such that a type has values when one of its constructors has
   fields whose types all have values. Whether a declared type has values
   depends only on which of its arguments have values, so the set is built
   over pairs of a type constructor and that choice, which are finitely
   many: each pair met is tried with its arguments standing for [()] or
   [Never], until no try adds a pair. *)
let inhabited env ty =
  let met = Hashtbl.create 16 and shown = Hashtbl.create 16 in
  let rec has_values ty =
    match T.resolve ty with
    | _ when is_prelude ty "Never" -> false
    | Tuple ts -> List.for_all has_values ts
    | Record fields -> List.for_all (fun (_, t) -> has_values t) fields
    | Con (item, args) -> (
        match Env.type_info env item with
        | Some { def = Variants _ | Record _; _ } ->
            let pair = (item, List.map has_values args) in
            Hashtbl.replace met pair ();
            Hashtbl.mem shown pair
        | Some { def = Builtin; _ } | None -> true)
    | Param _ | App _ | Spread _ | Fn _ | Forall _ | Handler _ | Var _ | Value _
    | Error ->
        true
  in
  let builds item args =
    let all info = List.for_all (fun t -> has_values (subst info args t)) in
    match Env.type_info env item with
    | Some ({ def = Variants vs; _ } as info) ->
        List.exists (fun (_, payload) -> all info payload) vs
    | Some ({ def = Record fields; _ } as info) ->
        all info (List.map snd fields)
    | Some { def = Builtin; _ } | None -> true
  in
  let rec settle () =
    let size = (Hashtbl.length met, Hashtbl.length shown) in
    let answer = has_values ty in
    Hashtbl.fold (fun pair () pairs -> pair :: pairs) met []
    |> List.iter (fun (item, has) ->
        let args = List.map (fun b -> if b then T.unit else T.never) has in
        if builds item args then Hashtbl.replace shown (item, has) ());
    if (Hashtbl.length met, Hashtbl.length shown) = size then answer
    else settle ()
  in
  settle ()

(* generics.array-exhaustiveness: the size of an array whose size is known. *)
let array_size ty =
  Option.bind (Check_arrays.parts ty) (fun (_, size) ->
      Check_arrays.known_size size)

(* The constructors that build the values of a type, when they are finitely
   many, in declaration order. Lists are split by length separately, and an
   array is a tuple of its size. *)
let all_ctors env ty =
  let live ctors =
    List.filter
      (fun c -> List.for_all (inhabited env) (field_types env ty c))
      ctors
  in
  match T.resolve ty with
  | Tuple ts -> Some (live [ Tuple (List.length ts) ])
  | t when Option.is_some (array_size t) ->
      Some (live [ Tuple (Option.get (array_size t)) ])
  | _ when is_prelude ty "bool" -> Some [ Bool false; Bool true ]
  | _ when is_prelude ty "Never" -> Some []
  | Con (item, _) -> (
      match Env.type_info env item with
      | Some { def = Variants vs; _ } ->
          Some
            (live (List.map (fun (name, _) -> Variant { item with name }) vs))
      | Some { def = Record fields; _ } ->
          Some (live [ Record (item, List.map fst fields) ])
      | Some { def = Builtin; _ } | None -> None)
  (* records.anonymous-patterns: an anonymous record's one constructor, and a bounded
     parameter's, which has the bound's fields. *)
  | (Record _ | Param _) as t -> (
      match Env.record_fields env t with
      | Some fields -> Some (live [ Record (T.anonymous, List.map fst fields) ])
      | None -> None)
  | App _ | Spread _ | Fn _ | Forall _ | Handler _ | Var _ | Value _ | Error ->
      None

(* A pattern, with every constant read as [_] (patterns.guards-and-constants and patterns.unreachable-arms). An
   or-pattern that lists every constructor of its type, each with only
   wildcards inside, matches every value, so it is read as [_] too, which
   keeps a tuple of such alternatives from splitting into every
   combination. *)
let rec of_pattern env (p : pattern) =
  match p.pat with
  | P_wild | P_bind _ | P_const _ | P_error -> Wild
  | P_int text -> Ctor (Int (Literal.int_canonical text), [])
  | P_str s -> Ctor (Str s, [])
  | P_bool b -> Ctor (Bool b, [])
  | P_tuple ps -> Ctor (Tuple (List.length ps), List.map (of_pattern env) ps)
  | P_variant (item, ps) -> Ctor (Variant item, List.map (of_pattern env) ps)
  | P_record given -> (
      let fields =
        match T.resolve p.pty with
        | Con (item, _) -> Some (item, record_fields env item)
        | t ->
            Option.map
              (fun fs -> (T.anonymous, List.map fst fs))
              (Env.record_fields env t)
      in
      match fields with
      | Some (item, fields) ->
          Ctor
            ( Record (item, fields),
              List.map
                (fun f ->
                  Option.fold ~none:Wild ~some:(of_pattern env)
                    (List.assoc_opt f given))
                fields )
      | None -> Wild)
  (* generics.array-patterns: [[p₁, …, pⱼ, ..]] against an array of size [k] is a
     tuple of its [j] patterns, then [_]. Against a size that is a value
     parameter, only [[..]] fits, which matches every array. *)
  | P_list (ps, _) when Option.is_some (Check_arrays.parts p.pty) -> (
      let items = List.map (of_pattern env) ps in
      match array_size p.pty with
      | Some k -> Ctor (Tuple k, items @ wilds (k - List.length ps))
      | None -> Wild)
  | P_list (ps, Exact) ->
      Ctor (Len (List.length ps), List.map (of_pattern env) ps)
  | P_list (ps, (Rest | Rest_bind _)) -> Prefix (List.map (of_pattern env) ps)
  | P_or ps ->
      let alts =
        List.concat_map
          (fun q -> match of_pattern env q with Or qs -> qs | q -> [ q ])
          ps
      in
      let bare c = function
        | Ctor (c', ps) -> c' = c && List.for_all (( = ) Wild) ps
        | _ -> false
      in
      let complete =
        match all_ctors env p.pty with
        | Some (_ :: _ as ctors) ->
            List.for_all (fun c -> List.exists (bare c) alts) ctors
        | Some [] | None -> false
      in
      if complete || List.mem Wild alts then Wild else Or alts

let rec holds_constant (p : pattern) =
  match p.pat with
  | P_const _ -> true
  | P_tuple ps | P_variant (_, ps) | P_list (ps, _) | P_or ps ->
      List.exists holds_constant ps
  | P_record fields -> List.exists (fun (_, q) -> holds_constant q) fields
  | P_wild | P_bind _ | P_int _ | P_str _ | P_bool _ | P_error -> false

let is_list ty = is_prelude ty "List"

(* Whether a pattern, matched against a value of type [ty], looks inside a
   part of the value whose type has an error. *)
let rec touches_error env ty = function
  | Wild -> false
  | _ when is_error ty -> true
  | Or ps -> List.exists (touches_error env ty) ps
  | Ctor (c, ps) -> inside env (field_types env ty c) ps
  | Prefix ps -> inside env (field_types env ty (At_least (List.length ps))) ps

and inside env tys ps =
  List.length tys <> List.length ps || List.exists2 (touches_error env) tys ps

(* Rows whose first pattern is an or-pattern, split into one row per
   alternative. *)
let rec expand rows =
  List.concat_map
    (function
      | Or alts :: rest -> expand (List.map (fun p -> p :: rest) alts)
      | row -> [ row ])
    rows

(* The rows that a value built with [ctor], of arity [n], can match, with
   the constructor's fields in place of the first column. *)
let specialize ctor n rows =
  List.filter_map
    (function
      | Ctor (c, ps) :: rest -> if c = ctor then Some (ps @ rest) else None
      | Prefix ps :: rest ->
          let k = List.length ps in
          if n >= k then Some (ps @ wilds (n - k) @ rest) else None
      | Wild :: rest -> Some (wilds n @ rest)
      | Or _ :: _ | [] -> assert false)
    rows

(* The rows whose first pattern matches any value. *)
let default rows =
  List.filter_map (function Wild :: rest -> Some rest | _ -> None) rows

let heads rows =
  List.filter_map (function Ctor (c, _) :: _ -> Some c | _ -> None) rows

(* The list lengths that tell the patterns of a column apart: each length
   below [n] on its own, then every length from [n] on together. *)
let list_cases rows q =
  let longest =
    List.fold_left
      (fun m -> function
        | Ctor (Len k, _) -> max m (k + 1)
        | Prefix ps -> max m (List.length ps)
        | _ -> m)
      0
      (q :: List.filter_map (function p :: _ -> Some p | [] -> None) rows)
  in
  List.init longest (fun k -> Len k) @ [ At_least longest ]

(* Whether [head], the pattern of a list column, covers one of [list_cases]. *)
let covers head = function
  | Len k -> (
      match head with
      | Ctor (Len n, _) -> n = k
      | Prefix ps -> k >= List.length ps
      | _ -> true)
  | At_least _ -> ( match head with Ctor (Len _, _) -> false | _ -> true)
  | _ -> false

(* The pattern for the values of [ty] that the constructors [seen] at the head
   of the rows miss: a missing constructor, if [ty] has constructors and the
   rows name some. *)
let missing env ty ctors seen =
  match ctors with
  | Some ctors when seen <> [] -> (
      match List.find_opt (fun c -> not (List.mem c seen)) ctors with
      | Some c -> Ctor (c, wilds (arity env ty c))
      | None -> Wild)
  | _ -> Wild

(* Whether [q] is useful with respect to [rows], all of types [tys]. If it
   is, the result is a value vector, as patterns, that [q] matches and no row
   does. A column of the error type matches anything, and tells nothing
   apart (errors.error-type). *)
let rec useful env tys rows q =
  let rows = expand rows in
  if List.exists (List.for_all (( = ) Wild)) rows then None
  else
    match (tys, q) with
    | [], [] -> Some []
    | ty :: tys, _ :: rest when is_error ty ->
        useful env tys (List.map List.tl rows) rest
        |> Option.map (fun w -> Wild :: w)
    | ty :: tys, head :: rest -> (
        let try_ctor ctor =
          let fields = field_types env ty ctor in
          let n = List.length fields in
          let q' =
            match head with
            | Ctor (_, ps) -> ps @ rest
            | Prefix ps -> ps @ wilds (n - List.length ps) @ rest
            | Wild | Or _ -> wilds n @ rest
          in
          useful env (fields @ tys) (specialize ctor n rows) q'
          |> Option.map (fun w ->
              Ctor (ctor, List.filteri (fun i _ -> i < n) w)
              :: List.filteri (fun i _ -> i >= n) w)
        in
        match head with
        | Or alts ->
            List.find_map
              (fun alt -> useful env (ty :: tys) rows (alt :: rest))
              alts
        | (Ctor _ | Prefix _ | Wild) when is_list ty ->
            List.find_map try_ctor
              (List.filter (covers head) (list_cases rows head))
        | Ctor (ctor, _) -> try_ctor ctor
        | Prefix _ -> None
        | Wild -> (
            let seen = heads rows in
            match all_ctors env ty with
            | Some ctors when List.for_all (fun c -> List.mem c seen) ctors ->
                List.find_map try_ctor ctors
            | ctors ->
                useful env tys (default rows) rest
                |> Option.map (fun w -> missing env ty ctors seen :: w)))
    | _ -> invalid_arg "Exhaustive.useful"

(* A witness, as a program would write the pattern. *)
let rec show = function
  | Wild -> "_"
  | Or ps -> String.concat " | " (List.map show ps)
  | Prefix ps -> "[" ^ String.concat ", " (List.map show ps @ [ ".." ]) ^ "]"
  | Ctor (c, ps) -> (
      let args = List.map show ps in
      match c with
      | Variant v when ps = [] -> v.name
      | Variant v -> v.name ^ "(" ^ String.concat ", " args ^ ")"
      | Bool b -> string_of_bool b
      | Tuple _ -> "(" ^ String.concat ", " args ^ ")"
      | Record (item, fields) ->
          item.name ^ " { "
          ^ String.concat ", " (List.map2 (fun f a -> f ^ ": " ^ a) fields args)
          ^ " }"
      | Int _ | Str _ -> "_"
      | Len _ -> "[" ^ String.concat ", " args ^ "]"
      | At_least _ -> "[" ^ String.concat ", " (args @ [ ".." ]) ^ "]")

(* patterns.guards-and-constants, patterns.non-exhaustive-matches and patterns.unreachable-arms over the arms of one [match] or [catch]: its error if the
   arms leave a value, and the warnings for arms that can never match. The
   rows of earlier arms count only when they have no guard and hold no
   constant. An arm that looks inside a part of the error type takes no part
   in reachability. *)
let check_arms env ~file ~at ~reachability ty (arms : arm list) =
  (* Arms matched against the error type take no part in reachability: no
     diagnostic arises from it (errors.error-type). *)
  let reachability = reachability && not (is_error ty) in
  let covering = ref [] and certain = ref [] and unreachable = ref [] in
  List.iter
    (fun (a : arm) ->
      let p = of_pattern env a.pattern in
      let unsure = touches_error env ty p in
      if
        reachability && (not unsure)
        && Option.is_none (useful env [ ty ] (List.rev !certain) [ p ])
      then
        unreachable :=
          Diagnostic.at ~file Code.w0301 a.pattern.ploc
            "the arms before this one match everything it matches"
          :: !unreachable;
      if Option.is_none a.guard && not (holds_constant a.pattern) then (
        covering := [ p ] :: !covering;
        if not unsure then certain := [ p ] :: !certain))
    arms;
  let missing =
    Option.map
      (fun w ->
        Diagnostic.at ~file Code.e0329 at
          (Printf.sprintf "these patterns don't cover `%s`" (show (List.hd w))))
      (useful env [ ty ] (List.rev !covering) [ Wild ])
  in
  (Option.to_list missing, List.rev !unreachable)

(* expressions.if-let-always: an [if let] whose pattern matches every value of
   the scrutinee's type, holds no constant and isn't matched against the error
   type. *)
let always_matches env ~file ty (pattern : pattern) =
  let p = of_pattern env pattern in
  if
    is_error ty || holds_constant pattern || touches_error env ty p
    || Option.is_some (useful env [ ty ] [ [ p ] ] [ Wild ])
  then []
  else
    [
      Diagnostic.at ~file Code.w0303 pattern.ploc
        "this pattern matches every value, so the block always runs";
    ]

(* Every [match], [catch] and [if let] of a body. The arms of a [catch] that handles
   [Never] aren't checked for reachability: the empty [try] is the mistake
   (effects.empty-try). *)
let check env ~file block =
  let found = ref [] in
  Walk.iter_block
    (fun (e : expr) ->
      match e.desc with
      | Match (scrutinee, arms) ->
          found :=
            check_arms env ~file ~at:e.loc ~reachability:true scrutinee.ty arms
            :: !found
      | Try (_, Some c) ->
          found :=
            check_arms env ~file ~at:e.loc
              ~reachability:(not (Marking.handles_never c))
              c.error c.arms
            :: !found
      | If_let (pattern, scrutinee, _, _) ->
          found := ([], always_matches env ~file scrutinee.ty pattern) :: !found
      | _ -> ())
    block;
  let results = List.rev !found in
  (List.concat_map fst results, List.concat_map snd results)
