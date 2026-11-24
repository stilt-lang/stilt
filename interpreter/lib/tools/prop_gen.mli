(** The values of a property's cases (tests.generated-scalars,
    tests.composite-values and tests.minimal-values): minimal values, and values
    generated from a case's draws. A map is built by inserting its entries in
    order with [insert], which calls its key type's [hash] and [eq]. *)

type insert = Types.ty -> Value.dict -> Value.value -> Value.value -> Value.dict
(** [insert kty d k v], as [m[k] = v] does on a map whose key type is [kty]. *)

val minimal : Prop_types.graph -> int -> Value.value
(** The minimal value of a node's type (tests.minimal-values). *)

val scalar : Prop_rand.t -> size:int -> Prop_types.node -> Value.value
(** A value of a scalar type at a size (tests.generated-scalars). *)

val generate :
  insert ->
  Prop_types.graph ->
  Prop_rand.t ->
  budget:int ->
  size:int ->
  int ->
  Value.value
(** A value of a node's type at a budget and a size (tests.generated-scalars and
    tests.composite-values). *)

val case :
  insert ->
  Prop_types.graph ->
  seed:int64 ->
  int list ->
  int ->
  Value.value list
(** [case insert g ~seed params i] gives the values of case [i] of a property
    whose parameters have the nodes [params] (tests.property-cases). *)

val build_map :
  insert -> Types.ty -> (Value.value * Value.value) list -> Value.value
(** A map of key type [kty] with these entries, inserted in order. *)

val key_type : Types.ty -> Types.ty
(** The key type of a map type. *)
