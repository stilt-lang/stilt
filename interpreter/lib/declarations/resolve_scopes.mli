(** Step 1 of name resolution: the scope of each module, which holds the items
    it declares and the names its [use] declarations bind
    (declarations.namespaces), and the names modules may have
    (program.module-names). *)

open Resolve_context

type unit_ = {
  name : string;
  local : string;
      (** Its name in its package (packages.modules-of-dependencies). *)
  valid : bool;
  std : bool;
  source : Program.source;
  tree : Ast.module_;
}
(** A module of the program or of the standard library. Its [name] is the one
    [Hir.module_] gives it, and [valid] tells whether other modules can name it
    (program.module-names). *)

val build_scope :
  env -> prelude_names:Sset.t * Sset.t -> is_prelude:bool -> unit_ -> scope
(** The scope of a module, whose [use] declarations name modules of [env]. Every
    name it declares is checked against the primitive types
    (lexical.primitive-type-names), the [prelude_names] of its namespace, the
    prelude's types and traits, then its variants and functions
    (program.prelude-names), and the module's other names
    (declarations.unique-names). The prelude declares the built-in types. *)

val trait_entry : bool -> Ast.trait_decl -> Resolve_context.entry
(** [trait_entry pub t] is the entry of the trait [t]: its arity as a
    constructor trait, which the first [Self] that its members apply gives
    (traits.constructor-traits), its parameters (traits.trait-parameters), and
    whether it belongs to the advanced tier (traits.advanced-tier). *)
