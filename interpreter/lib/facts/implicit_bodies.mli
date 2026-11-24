(** The sites of every body of a program, with the facts that cross bodies: the
    parameters each function consumes (values.consumed-parameters), which decide
    the copies of modes.copies; the in-place parameters of the functions limited
    by [without alloc] (facts.in-place-parameters); and recursive groups
    (facts.div). *)

val sites :
  Env.t ->
  limited:(Ast.limit -> Tast.fn_def -> bool) ->
  verify:(Implicit_names.key -> Tast.fn_def -> Tast.block -> Accept.t) ->
  (Implicit_names.key * Tast.fn_def) list ->
  (Implicit_names.key * Implicit_sites.site list) list
(** The sites of each body with code: the operations that panic or allocate
    themselves (facts.allocation and facts.native-allocation), the copies at
    calls of in-place parameters, which allocate and copy (facts.copy-at-call
    and facts.copy), the shared modifications, which copy (facts.copy), and the
    operations that may not end (facts.div and facts.descending-self-calls),
    each with the items it names. [verify] reads a body by the rules of
    acceptance, and what they prove neither panics nor may not end
    (facts.rules-of-acceptance). *)
