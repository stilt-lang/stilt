(** A map whose keys have an [Eq] and a [Hash] that the program writes, at the
    key type or at a part of it (traits.hash-follows-written-eq), as the export
    writes it: the list of its entries in insertion order, each with its key's
    hash, and each function that finds a key a function of the export's own,
    which calls the key type's [hash] once, on the key, and then its [eq] on
    each stored key of the same hash, in insertion order, until one returns
    [true] (std.finding-keys). Each function takes the code of the prelude
    traits' functions, {!Model_code.at}, the key type and the value type. *)

val keyed : Model_types.cx -> Types.ty -> (Types.ty * Types.ty) option
(** The key and value types of a map whose keys the calculus can't find, if the
    type is one. *)

val entry_ty : Types.ty -> Types.ty -> Types.ty
(** An entry of such a map: its key's hash, its key and its value. *)

val repr : Types.ty -> Types.ty -> Types.ty
(** The list such a map is. *)

val index :
  Model_code.at ->
  Model_types.cx ->
  Types.ty ->
  Types.ty ->
  Model_json.t ->
  Model_json.t ->
  Model_json.t
(** [m[k]], which panics with [missing-key] for a key without an entry
    (std.maps). *)

val insert :
  Model_code.at ->
  Model_types.cx ->
  Types.ty ->
  Types.ty ->
  Model_json.t ->
  Model_json.t ->
  Model_json.t ->
  Model_json.t
(** The map that [m.insert(k, x)] and [m[k] = x] store: a key it finds keeps the
    stored key and its position. *)

val contains :
  Model_code.at ->
  Model_types.cx ->
  Types.ty ->
  Types.ty ->
  Model_json.t ->
  Model_json.t ->
  Model_json.t

val get_or :
  Model_code.at ->
  Model_types.cx ->
  Types.ty ->
  Types.ty ->
  Model_json.t ->
  Model_json.t ->
  Model_json.t ->
  Model_json.t

val get :
  Model_code.at ->
  Model_types.cx ->
  Types.ty ->
  Types.ty ->
  Model_json.t ->
  Model_json.t ->
  Model_json.t
(** [Some] of the value of the key, or [None]. *)

val remove :
  Model_code.at ->
  Model_types.cx ->
  Types.ty ->
  Types.ty ->
  Model_json.t ->
  Model_json.t ->
  Model_json.t
(** The map without the key's entry, and [Some] of its value, or the map as it
    was and [None], as a pair. *)

val entries :
  Model_types.cx -> Types.ty -> Types.ty -> Model_json.t -> Model_json.t

val keys :
  Model_types.cx -> Types.ty -> Types.ty -> Model_json.t -> Model_json.t

val values :
  Model_types.cx -> Types.ty -> Types.ty -> Model_json.t -> Model_json.t

val equal :
  Model_code.at ->
  Model_types.cx ->
  Types.ty ->
  Types.ty ->
  Model_json.t ->
  Model_json.t ->
  Model_json.t
(** [a == b] (traits.map-equality). *)

val shown :
  Model_code.at ->
  Model_types.cx ->
  Types.ty ->
  Types.ty ->
  Model_json.t ->
  Model_json.t
(** The map's text, [{k: v, …}] (std.show-output). *)
