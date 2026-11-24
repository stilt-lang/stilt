(* Indexes, divisions and keys (facts.range-loops, facts.guards, facts.divisors and facts.keys): the range loop
   around an index and the guards before it, a divisor that tests show
   non-zero, and a key that a test or a store shows present; and what the
   closest rule needs when none proves an operation (facts.closest-rule). *)

open Tast

(* The results of the rules, whose constructors [Tast]'s [Error] would hide. *)
type ('a, 'e) outcome = ('a, 'e) result = Ok of 'a | Error of 'e

module C = Accept_code
module W = Accept_walk
module S = Accept_signs
module X = Accept_text

type rule =
  | Range_loop
  | Guard
  | Divisor
  | Key
  | Counting_loop
  | Shrinking_recursion

type verdict = Proved of rule | Unproved of string
type cx = { env : Env.t; w : W.t; signs : S.t }

let reader cx = cx.w.W.reader
let done_ rule = function Ok () -> Proved rule | Error need -> Unproved need

type size = Size_num of C.num | Size_param of int

let size ty =
  match Check_arrays.parts ty with
  | Some (_, n) -> (
      match Types.resolve n with
      | Value text -> Some (Size_num (C.num_of_literal text))
      | Param v -> Some (Size_param v.id)
      | _ -> None)
  | None -> None

(* An array's element at a literal or a constant at least 0 and below its
   size (facts.range-loops). *)
let below_size cx (base : expr) key =
  match (size base.ty, C.number (reader cx) key) with
  | Some (Size_num n), Some k -> C.sign k >= 0 && C.compare_num k n < 0
  | _ -> false

let is_var var (e : expr) =
  match e.desc with Local v -> v.id = var | _ -> false

let names (e : expr) var =
  Walk.exists
    (fun (x : expr) -> match x.desc with Local v -> v.id = var | _ -> false)
    e

(* The [k] of an index [i], [i + k] or [i - k], none for [i], and whether it
   adds. *)
let offset cx (key : expr) var =
  if is_var var key then Some (None, true)
  else
    match key.desc with
    | Binary (((Add | Sub) as op), a, k)
      when is_var var a
           && Option.fold ~none:false
                ~some:(fun n -> C.sign n >= 0)
                (C.number (reader cx) k) ->
        Some (Some k, op = Add)
    | _ -> None

let is_size cx (e : expr) ty =
  match (size ty, e.desc) with
  | Some (Size_param id), Value_param v -> v.id = id
  | Some (Size_num n), _ -> (
      match C.number (reader cx) e with
      | Some m -> C.compare_num m n = 0
      | None -> false)
  | _ -> false

(* Whether the loop ends at [P.len()], where the index adds nothing, or at
   [P.len() - c] with [c] at least [k] where it adds [k], [n] standing for
   [P.len()] for an array of size [n]. *)
let ends cx (r : W.range) place (base : expr) k =
  let is_len e = C.len_of (reader cx) e = Some place || is_size cx e base.ty in
  (is_len r.rend && match k with None -> true | Some k -> C.sign k = 0)
  ||
  match (r.rend.desc, k) with
  | Binary (Sub, len, c), Some k ->
      is_len len
      && Option.fold ~none:false
           ~some:(fun c -> C.compare_num c k >= 0)
           (C.number (reader cx) c)
  | _ -> false

let range_end cx (r : W.range) (base : expr) k plus kn =
  let place =
    if C.is_sequence base.ty then C.place (reader cx) base else None
  in
  let reaches =
    Option.fold ~none:false
      ~some:(fun pl -> ends cx r pl base (if plus then Some kn else None))
      place
  in
  if r.inclusive || not reaches then
    let shown =
      match k with Some k when plus && C.sign kn > 0 -> Some k | _ -> None
    in
    Error (X.range_end cx.env base shown r.rend ~inclusive:r.inclusive)
  else
    let changed =
      match place with
      | Some pl when C.is_list base.ty ->
          W.first (W.in_span cx.w r.rbody r.rspan) (fun x -> W.changes x pl)
      | _ -> None
    in
    match changed with
    | Some line -> Error (X.range_length cx.env base line)
    | None -> Ok ()

(* facts.range-loops: whether the range loop [r] proves [base[key]], or what it needs. *)
let range cx (p : W.pending) (r : W.range) base key =
  let rd = reader cx in
  if r.rbody <> p.pbody then Error X.range_closures
  else
    match offset cx key r.var.id with
    | None -> Error (X.range_form r.var)
    | Some (k, plus) ->
        let kn = Option.value ~default:C.zero (Option.bind k (C.number rd)) in
        if plus && not (S.nonneg cx.signs r.rstart r.rbody) then
          Error X.range_start
        else if
          (not plus)
          && not
               (Option.fold ~none:false
                  ~some:(fun a -> C.compare_num a kn >= 0)
                  (C.number rd r.rstart))
        then Error (X.range_start_at cx.env (Option.value k ~default:key))
        else range_end cx r base k plus kn

let first_of cx p frames f =
  List.fold_left
    (fun acc fr ->
      match W.first (W.between cx.w fr p) f with
      | Some l -> Some (Option.fold ~none:l ~some:(min l) acc)
      | None -> acc)
    None frames

(* facts.guards: whether guards prove [base[key]], or what they need. *)
let guard cx (p : W.pending) (base : expr) key =
  let rd = reader cx in
  let term =
    match (C.name rd key, C.number rd key) with
    | Some v, _ -> Some (C.Name v.id)
    | None, Some n when C.sign n >= 0 -> Some (C.Num n)
    | _ -> None
  in
  match term with
  | None -> Error X.guard_form
  | Some term -> (
      let lower =
        if S.nonneg cx.signs key p.pbody then Ok None
        else
          match W.frame cx.w p (fun a -> C.compares a term Ge (Num C.zero)) with
          | Some f -> Ok (Some f)
          | None -> Error (X.guard_lower cx.env key)
      in
      let place = if C.is_sequence base.ty then C.place rd base else None in
      let upper =
        Option.bind place (fun pl ->
            W.frame cx.w p (fun a ->
                C.compares a term Lt (Len pl)
                || (term = Num C.zero && a = Non_empty pl)))
      in
      match (lower, upper, place) with
      | Error need, _, _ -> Error need
      | Ok lower, Some upper, Some place -> (
          let frames = Option.to_list lower @ [ upper ] in
          let writes =
            match term with
            | Name v -> first_of cx p frames (fun x -> x.root = v)
            | _ -> None
          in
          match writes with
          | Some line -> Error (X.guard_writes cx.env key line)
          | None -> (
              let list = C.is_list base.ty in
              match
                first_of cx p frames (fun x -> list && W.changes x place)
              with
              | Some line -> Error (X.guard_length cx.env base line)
              | None -> Ok ()))
      | Ok _, _, _ -> Error (X.guard_upper cx.env key base))

(* An index of a list or an array: by a range loop or a guard, or what the
   closest of the two needs. *)
let index cx (p : W.pending) base key =
  if below_size cx base key then Proved Range_loop
  else
    let ranges = List.rev_map (Dynarray.get cx.w.ranges) p.ranges in
    if List.exists (fun r -> range cx p r base key = Ok ()) ranges then
      Proved Range_loop
    else
      match guard cx p base key with
      | Ok () -> Proved Guard
      | Error need -> (
          match
            List.find_opt (fun (r : W.range) -> names key r.var.id) ranges
          with
          | Some r -> (
              match range cx p r base key with
              | Error n -> Unproved n
              | Ok () -> Unproved need)
          | None -> Unproved need)

(* facts.divisors: whether the divisor [d] is proved non-zero, or what it needs. *)
let divisor cx (p : W.pending) (d : expr) =
  let rd = reader cx in
  match C.name rd d with
  | None -> (
      match C.number rd d with
      | Some n when C.sign n <> 0 -> Ok ()
      | _ -> Error X.divisor_form)
  | Some v -> (
      if S.positive cx.signs d p.pbody then Ok ()
      else
        let name = C.Name v.id and zero = C.Num C.zero in
        let nonzero a =
          List.exists (fun op -> C.compares a name op zero) [ C.Ne; Gt; Lt ]
        in
        match W.frame cx.w p nonzero with
        | None -> Error (X.divisor_test cx.env d)
        | Some f -> (
            match W.first (W.between cx.w f p) (fun x -> x.root = v.id) with
            | Some line -> Error (X.divisor_writes cx.env d line)
            | None -> Ok ()))

(* facts.map-keys: a key type whose [Eq] and [Hash] are a primitive type's or
   structural throughout its parts. *)
let rec keyable env seen ty =
  let all = List.for_all (keyable env seen) in
  match Types.resolve ty with
  | Tuple ts -> all ts
  | Record fields -> all (List.map snd fields)
  | Con (item, args) -> (
      let written trait =
        Env.trait_impl env ~trait:(Types.prelude_item trait) item
      in
      if written "Eq" <> None || written "Hash" <> None then false
      else if List.mem item seen then true
      else
        let seen = item :: seen in
        let parts (info : Env.type_info) ts =
          let sub = List.combine info.params args in
          List.for_all (fun t -> keyable env seen (Types.subst sub [] t)) ts
        in
        match Env.type_info env item with
        | Some ({ def = Record fields; _ } as info)
          when List.length info.params = List.length args ->
            parts info (List.map snd fields)
        | Some ({ def = Variants vs; _ } as info)
          when List.length info.params = List.length args ->
            parts info (List.concat_map snd vs)
        | Some { def = Builtin; _ } ->
            item.home = "std.prelude"
            && List.mem item.name
                 ([ "str"; "bool"; "char"; "List" ] @ Types.integer_types)
            && List.for_all (keyable env seen) args
        | _ -> false)
  | _ -> false

(* facts.keys: whether the key [k] of the map [m] is proved present, or what the
   key needs. *)
let key cx (p : W.pending) (m : expr) (k : expr) =
  let rd = reader cx in
  match C.key rd k with
  | None -> Error X.key_form
  | Some _ when not (keyable cx.env [] k.ty) -> Error X.key_type
  | Some key -> (
      let test = X.key_test cx.env m k in
      let frame =
        Option.bind (C.place rd m) (fun place ->
            Option.map
              (fun f -> (place, f))
              (W.frame cx.w p (fun a -> a = C.Contains (place, key))))
      in
      match frame with
      | None -> Error test
      | Some (place, f) -> (
          let between = W.between cx.w f p in
          let writes =
            match key with
            | Key_name v -> W.first between (fun x -> x.root = v)
            | _ -> None
          in
          match writes with
          | Some line -> Error (X.key_writes cx.env k line)
          | None -> (
              match W.first between (fun x -> W.unstores x place) with
              | Some line -> Error (X.key_changes cx.env m line)
              | None -> Ok ())))

let verdict cx (p : W.pending) =
  match p.op with
  | Index (base, k) when C.is_map base.ty -> Some (done_ Key (key cx p base k))
  | Index (base, k) -> Some (index cx p base k)
  | Division d -> Some (done_ Divisor (divisor cx p d))
  | Self_call _ -> None
