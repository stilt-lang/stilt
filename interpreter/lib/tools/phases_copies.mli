(** Duplicate bodies (docs.bodies-compared, docs.body-size, docs.same-body and
    docs.duplicate-bodies): the bodies of functions and methods that are the
    same typed body, of at least 20 tokens. *)

type candidate = {
  file : string;
  path : string;  (** The function's path (edits.paths). *)
  at : Ast.loc;  (** Its name. *)
  params : Hir.var list;  (** Its parameters, its receiver's first. *)
  block : Tast.block;
}
(** A function's body without an error of phase 1 or 2, in a module of the
    program's own (edits.canonical-text). *)

val warnings : text:(string -> string) -> candidate list -> Diagnostic.t list
(** The W0302 of each body that is the same as one that comes before it in the
    program, by the paths of their files, then their positions, at its
    function's name (edits.showing-parts). [text] gives the text of each file,
    whose tokens are counted (edits.hash). *)
