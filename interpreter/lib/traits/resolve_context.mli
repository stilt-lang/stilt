(** The state of name resolution, the scopes of modules, and the contexts in
    which names are resolved (declarations.namespaces). *)

module Smap : Map.S with type key = string
module Sset : Set.S with type elt = string

val prelude : string
(** The name of [std.prelude]. *)

val primitive_types : string list
(** The names of the primitive types (lexical.primitive-type-names). *)

val is_primitive : string -> bool

val dotted : string list -> string
(** The dotted name made of segments, such as [std.prelude]. *)

val dotted_path : Hir.name list -> string

(** {1 State} *)

type reference = {
  from : string;
  target : string;
  file : string;
  loc : Hir.loc;
}
(** A place where module [from] names module [target]: a [use] declaration, or a
    path that names one of [target]'s items. *)

type unknown = {
  written : string;  (** The name, as a path written up to where it fails. *)
  diagnostic : Diagnostic.t;
  deferred : bool;
      (** Whether a pattern writes the name without a module, so that type
          checking reports it unless the type matched there has a variant of
          that name (patterns.variants-by-type). *)
}
(** An E0211 found in a body. *)

type macro = {
  decl : Ast.syntax_decl;
  home : string;  (** The module that declares it. *)
  usable : bool;
      (** Whether its declaration has no error, so that its uses expand. *)
  expr : bool;  (** Whether every template of its arms is an expression. *)
  pattern : bool;  (** Whether every template of its arms is a pattern. *)
  named : (Hir.item * Hir.loc) list;
      (** The functions its templates name, where (macros.expansion-effects). *)
}
(** A pattern macro, as the checks of its declaration leave it
    (macros.checked-templates). *)

type state = {
  mutable diagnostics : Diagnostic.t list;
  mutable unknown_names : unknown list option;
      (** Inside a body, the E0211 found so far, of which the body reports one
          per name (errors.root-causes). *)
  mutable unresolved : (string * Hir.loc) list;
      (** The bodies with errors, by file and position (see [Hir.module_]). *)
  mutable held : (string * Hir.loc * string * Diagnostic.t) list;
      (** The E0211 held back for type checking, each with its file, its body
          and its name (see [Hir.module_]). *)
  mutable references : reference list;
  mutable advanced : string list;
      (** The modules that name [View] or [Iter] of [std.view] or declare a
          projection, which are in the advanced tier (views.std-view;
          projections.declaring-projection). *)
  mutable next_id : int;
  macros : (Hir.item, macro) Hashtbl.t;
      (** The macros of the program, the first of each name in a module. *)
  expansions : (int, string) Hashtbl.t;
      (** For each expansion, the module of its macro, where the names its
          template writes resolve (macros.hygiene). *)
  mutable chain : string list;
      (** The macros whose expansions are being resolved, innermost first
          (macros.nested-expansions). *)
  mutable declaring : bool;
      (** Whether a template is being checked where its macro is declared, so
          that the uses it writes aren't expanded (macros.checked-templates). *)
  mutable named : (Hir.item * Hir.loc) list option;
      (** While a template is checked, the functions it names
          (macros.expansion-effects). *)
  mutable meta : string list;
      (** The modules that declare a value parameter or write [comptime], which
          are in the meta tier (generics.meta-tier; meta.staging-tier). *)
  mutable systems : string list;
      (** The modules that declare a foreign function, write an [unsafe] block
          or name [std.c] with [use], which are in the systems tier
          (c.systems-tier). *)
  constants : (Hir.item, Ast.const_decl * string) Hashtbl.t;
      (** Each constant's declaration, with the module whose scope its value is
          read in: a module's constants by their items, and an inherent impl's
          by an item of the impl's type's module named [Type.NAME], so that a
          value argument can name either (generics.value-argument-names). *)
  computed : (Hir.item, computed) Hashtbl.t;
      (** The constants computed so far for value arguments, each once
          (generics.constant-arguments). *)
  host : Procs.host;
      (** What runs the procedural macros that uses name (macros.running). *)
}

(** What computing a constant given as a value argument gives
    (generics.constant-arguments). *)
and computed =
  | Value of string * string
      (** The name of its type, an integer type or [bool], and its value, in
          decimal, or [true] or [false]. *)
  | Panics of string
      (** The name of its type, and a computation that panics, as a unary [-]
          that overflows. *)
  | Unknown of string option
      (** No value: a constant whose type, named when it has no error, is no
          integer type or [bool], or that has an error of its own, which its
          declaration reports. *)

val report :
  state ->
  file:string ->
  Code.t ->
  Hir.loc ->
  ('a, unit, string, unit) format4 ->
  'a
(** [report st ~file code loc fmt] adds the diagnostic [code] at [loc] in
    [file], with the message that [fmt] formats. *)

(** {1 Scopes (declarations.namespaces)} *)

type kind =
  | Type_item
  | Trait_item
  | Fn_item
  | Const_item
  | Variant_item
  | Macro_item  (** A pattern macro (macros.syntax-declarations). *)
  | Proc_item
      (** A procedural macro, named only through [meta use]
          (macros.procedural-declarations and macros.meta-use). *)
  | Effect_item
      (** An effect, in the type namespace (handlers.declaring-effect). *)

type entry = {
  kind : kind;
  pub : bool;
  arity : int;
      (** A type's number of type parameters, and a constructor trait's arity,
          which is 0 for a trait over types (traits.constructor-traits). *)
  params : string list;  (** A trait's parameters (traits.trait-parameters). *)
  pack : bool;
      (** Whether a type's last parameter is a pack, which the arguments after
          the others give (variadics.packs and variadics.pack-inference). *)
  values : (int * string option) list;
      (** The positions of a type's value parameters, each with the name of its
          type when that is an integer type or [bool]
          (generics.value-parameters). *)
  advanced : bool;
      (** Whether a trait has parameters, functions without [self], constants or
          a constructor [Self], so that declaring, implementing or naming it in
          a bound makes a module advanced (traits.advanced-tier). *)
}
(** An item: what it is, whether other modules may name it, and its shape. A
    variant has the visibility of its type (program.visibility). *)

val entry :
  ?arity:int ->
  ?params:string list ->
  ?pack:bool ->
  ?values:(int * string option) list ->
  ?advanced:bool ->
  kind ->
  bool ->
  entry
(** [entry kind pub], with no type parameters or trait parameters. *)

(** A name in a module's value namespace: one of its items, or a name that a
    [use] declaration binds to a namespace. A [use] with an error binds its name
    to nothing, and uses of that name have the error type. *)
type value = Item of entry | Import of string | Import_error

type namespace = Types | Values

type scope = {
  name : string;  (** The module's name, as in [Hir.module_]. *)
  file : string;
  types : entry Smap.t;
  values : value Smap.t;
  shadowed : Sset.t * Sset.t;
      (** The types and values whose names clash with prelude items. Uses of
          them in the module have the error type (program.prelude-names). *)
  unknown : Sset.t * Sset.t;
      (** The types and values that a part with a syntax error declares only by
          name. Every use of them, in any module, has the error type
          (errors.broken-parts). *)
  metas : string Smap.t;
      (** The modules that [meta use] declarations name, by the names they bind,
          through which the module uses their procedural macros
          (macros.meta-use). *)
}

(** What a [use] names, as a package's view of the program reads it
    (packages.modules-of-dependencies, packages.imports and
    packages.manifests-with-errors). *)
type lookup =
  | Found of string  (** The namespace of this name in the program. *)
  | Unnamed
      (** Nothing, because of an error elsewhere: no further error
          (errors.root-causes). *)
  | Foreign of string
      (** A module of the package of this name, which isn't a dependency
          (E0218). *)
  | Missing  (** No module (E0205). *)

type env = {
  st : state;
  modules : Sset.t;  (** The names of the modules that a program can name. *)
  scopes : scope Smap.t;  (** Their scopes, once built. *)
  namespaces : Sset.t;  (** Their names, and every prefix of one. *)
  unnamed : Sset.t;
      (** The names, and their prefixes, of the modules whose names are invalid
          and that aren't namespaces. Naming one is no further error
          (program.module-names). *)
  view : int -> string -> lookup;
      (** What a [use] of a module of the package of this index names. *)
  items : Sset.t Smap.t;
      (** The names of the items that each module declares, in either namespace,
          by its name in the program, which a [use] may name by mistake (E0230).
      *)
}

val whole_view : env -> string -> lookup
(** What a [use] names among all the modules of [env], as the standard library
    and programs without packages read it. *)

val describe : kind -> string
(** A kind of item, as errors name it, such as "a type". *)

val is_type_kind : kind -> bool

(** {1 Contexts} *)

(** What [Self] means: an impl's type, or in a trait the type that implements
    it. *)
type self = No_self | Impl_self of Hir.ty | Trait_self

type quoting = {
  splice : Hir.place -> Ast.expr -> unit;
      (** Resolves a splice's expression, a [Q_splice] or a [Q_spread], in the
          code of the macro, and records it where it stands. *)
  outer : string list;  (** The locals of the macro's code. *)
}
(** Inside a quote, its splices and the code around it (macros.splices and
    macros.quote-hygiene). *)

type ctx = {
  env : env;
  scope : scope;
  self : self;
  type_params : (string * Hir.var) list;
      (** Innermost first, as are the next. *)
  kinds : (int * int) list;
      (** The constructor parameters in scope, by id, with their arities
          (traits.constructor-parameters). *)
  packs : int list;  (** The packs in scope, by id (variadics.packs). *)
  misplaced : int list;
      (** The packs declared where none may be, by id, which E0344 reports and
          which are plain type parameters after it, so that no other error
          follows from them (variadics.packs). *)
  spread : Hir.var list ref option;
      (** Inside a spread in a type, the packs it names so far
          (variadics.type-spreads). *)
  members : (int * (Hir.item * (string * Hir.ty) list) list) list;
      (** For each type parameter in scope, by id, the traits of its bounds,
          each with the types that give the trait's parameters, which its member
          types name (traits.member-types). *)
  ctor : int;
      (** In a constructor trait or an impl of one, the trait's arity, and 0
          anywhere else (traits.constructor-traits and
          traits.constructor-impls). *)
  fixed : bool;
      (** Whether the functions here have the signatures of a trait: those of a
          trait or of a trait impl (traits.where). *)
  row_vars : (string * Hir.var) list;
  value_params : (string * (Hir.var * Hir.ty)) list;
      (** The value parameters in scope, with their types
          (generics.value-parameters-in-body). *)
  locals : (string * Hir.var option) list;
      (** [None] for a binding whose uses have the error type. *)
  in_loop : bool;
  public : bool;
      (** Whether the names being resolved are in a signature that other modules
          see (program.private-in-signatures). *)
  expanding : bool;
      (** Whether the code being resolved is a macro's expansion, whose forms
          leave the module in its tier (macros.advanced-tier). *)
  quoting : quoting option;
      (** Inside a quote, which resolves its names where it is written, not in
          the code around it (macros.quote-hygiene). *)
  lost : bool;
      (** In the scope that a pattern holding a failed use of a procedural macro
          opens, where a name that names nothing has the error type and is
          reported nowhere (macros.failed-uses). *)
}

val module_ctx : env -> scope -> ctx
(** The context at the top level of a module. *)

val advanced : ctx -> unit
(** Records that the context's module uses a feature of the advanced tier
    (program.tiers). *)

val meta : ctx -> unit
(** Records that the context's module uses a feature of the meta tier
    (generics.meta-tier; meta.staging-tier). *)

val systems : ctx -> unit
(** Records that the context's module uses a feature of the systems tier
    (c.systems-tier). *)

val quietly : state -> (unit -> 'a) -> 'a * bool
(** [quietly st f] runs [f], keeping none of the diagnostics it reports, the
    references it records or the tiers it raises, and tells whether it reported
    any. *)

val errorf : ctx -> Code.t -> Hir.loc -> ('a, unit, string, unit) format4 -> 'a
(** Reports a diagnostic in the context's module. *)

val unknown_name :
  ctx -> name:string -> Hir.loc -> ('a, unit, string, unit) format4 -> 'a
(** Reports E0211 for [name], a path as written up to the name in it that
    doesn't resolve. Inside a body, only its first place is reported. *)

val unknown_diagnostic : ctx -> Hir.loc -> string -> Diagnostic.t
(** E0211 at a place in the context's module, with a message. *)

val deferred_name : ctx -> string -> Diagnostic.t -> unit
(** Records, inside a body, that a pattern writes the name without a module
    where it means nothing in scope, which [d] reports unless the type matched
    there has a variant of that name (patterns.unknown-variants). *)

val in_body : state -> file:string -> at:Hir.loc -> (unit -> 'a) -> 'a
(** Resolves the body known by [at] in [file] with [resolve], reporting one
    E0211 for each name that doesn't resolve in it, at the place where that name
    starts first (errors.unknown-names). The E0211 of a name that a pattern of
    the body also writes without a module is held for type checking, which knows
    whether the pattern's name fails, and where. *)

val fresh : ctx -> Hir.name -> Hir.var
(** A new variable, which no other declaration has. *)

val valid_module_path : string list -> bool
(** Whether a module's path is a valid name (program.module-names). *)
