(** Arrays of [std.array] (generics.arrays, generics.array-literals and
    generics.array-patterns): their literals, their sizes and the list patterns
    that match them. *)

val parts : Types.ty -> (Types.ty * Types.ty) option
(** The element type and the size of an array type of [std.array]. *)

val known_size : Types.ty -> int option
(** generics.constant-arguments: a size known while the program is checked, in
    decimal. *)

val literal :
  Check_state.ctx ->
  Ast.loc ->
  Types.ty ->
  Types.ty ->
  Hir.expr list ->
  Tast.expr
(** generics.array-literals: a list literal where [Array<elem, size>] is
    expected. Its length is exactly the size, which a value parameter never is
    (generics.constant-arguments), and none of its elements is a spread. A size
    that inference hasn't found yet is its length. *)

val pattern_fits : Types.ty -> int -> Hir.list_rest -> bool
(** generics.array-patterns: whether a list pattern of [length] patterns, with a
    rest or not, fits an array of [size]: of exactly its length, or of at most
    its length with a rest that binds nothing. Against a value parameter, only
    [[..]] fits. *)
