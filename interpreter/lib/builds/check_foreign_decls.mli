(** The foreign functions of a program, which C gives (c.foreign-functions and
    c.types-c-takes). *)

val check :
  (Program.source * Ast.module_) list -> Hir.program -> Diagnostic.t list
(** E0353 at each part of a foreign function's signature that C can't take: a
    generic's name, [self], the name of an [inout] or [escaping] parameter, the
    type of another parameter or of the result, and a row's element other than
    [io], in the order they are written. Its types are read as [hir] resolves
    them, so that [c.Ptr] is [std.c]'s. *)
