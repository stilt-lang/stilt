(** Quotes at run time (macros.splices, macros.quote-hygiene and
    macros.outside-run): a quote's tokens, written out with its splices filled.
    In a macro's run, the tokens a quote writes are placed at the use, and
    outside one at the quote. *)

val mark : string -> int
(** The mark of an expansion that a quote of [home] writes names with: the
    running macro's, or a new one, below zero, outside a macro's run
    (macros.quote-hygiene). *)

val place : Ast.loc -> Ast.loc
(** Where a quote's tokens are placed: at the use that the running macro
    expands, or at [loc] outside a run. *)

val quote :
  Eval_state.t -> Eval_state.frame -> Ast.loc -> Tast.quote -> Value.value
(** The code that a quote writes, with its splices filled, as a value of
    [std.meta]. *)
