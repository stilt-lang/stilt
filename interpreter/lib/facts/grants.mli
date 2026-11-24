(** The effects and capabilities that packages perform, and the grants of their
    manifests (packages.grants, packages.own-effects, packages.ungranted-effects
    and packages.running-with-ungranted-effect; facts.capability-grants,
    facts.own-capabilities and facts.ungranted-capabilities). *)

type t
(** The functions of a program whose own code performs [io], by package, with
    the capabilities their own code has. *)

val find : Env.t -> Hir.program -> Tast.program -> (string -> int option) -> t
(** [find env hir program package_of_module]: a function performs [io] when its
    body, with its closures, calls or names a function of another package whose
    declared row holds [io] (packages.own-effects). It has each capability that
    such a function has, as facts.capabilities and facts.capability-natives
    infer it, and performs [io] without a capability when such a function has
    none (facts.own-capabilities). A [Broken] body, which has an error, performs
    none. A macro of [hir] has the facts of the functions its templates name, as
    a function of its package that names them (macros.expansion-effects).
    [package_of_module] gives the package of a module of the program, and [None]
    for the standard library's. *)

val diagnostics : t -> Program.packages -> Diagnostic.t list
(** The E0608s of each manifest entry: one for each capability that its
    dependency's own code has and that the entry doesn't grant, and one for [io]
    when that code performs [io] without a capability and the entry doesn't
    grant [io] (facts.ungranted-capabilities). *)

val break : t -> Program.packages -> Tast.program -> Tast.program
(** The program that {!find} read, with each function of a package whose own
    code has a capability, or performs [io] without one, that a manifest doesn't
    grant it replaced by [Broken] (packages.running-with-ungranted-effect;
    facts.ungranted-capabilities). *)
