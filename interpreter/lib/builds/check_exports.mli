(** The functions a program exports to C, written [pub extern fn]
    (c.exported-functions). *)

val check :
  Program.packages -> (Program.source * Ast.module_) list -> Diagnostic.t list
(** The errors of the exported functions of the modules read, each with its
    source: E0352 at each part of a signature that C can't take and at a name
    that C or C++ code can already mean (c.exported-signatures and
    c.exported-names), and E0219 at an exported function named like one before
    it in its package, in the order of c.library-header: by its module's path
    within its package, compared as bytes, then in its module's order. *)
