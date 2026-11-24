(** Packs and spreads in types (variadics.type-spreads and
    variadics.pack-tuples). *)

val is_spread : Types.ty -> bool

val mentions_pack : Types.ty -> Types.ty -> bool
(** [mentions_pack pack t] tells whether [pack] occurs in [t]. *)

val pack_tuple : Types.ty -> (Types.ty * Types.ty) option
(** The pack and the element of a pack tuple's type, a tuple whose one element
    is a spread, as [(..List<Ts>)] (variadics.pack-tuples). *)

val has_spread : Types.ty -> bool
(** Whether the type is a tuple with a spread among its elements, whose arity
    isn't known (variadics.pack-tuples). *)
