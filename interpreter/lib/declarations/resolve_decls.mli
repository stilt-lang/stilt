(** Declarations: functions, constants, types, traits and impl blocks, and the
    bodies they hold (traits.impl-blocks and traits.declaring-trait). A body
    whose resolution reports an error is recorded in the state's [unresolved].
*)

open Resolve_context

val resolve_decl : ctx -> Ast.decl Ast.node -> Hir.decl Hir.node

val resolve_impl : ctx -> Ast.impl_decl -> Hir.impl_decl
(** Other modules see the signature of a [pub] member of an inherent impl of a
    [pub] type, and so the block's generics when it has such a member
    (program.private-in-signatures). *)

val check_inherent_members : ctx -> Hir.impl_decl list -> unit
(** [check_inherent_members ctx impls] checks that a name is defined at most
    once across the inherent impls of each type of the module, among [impls]
    (traits.inherent-names). *)
