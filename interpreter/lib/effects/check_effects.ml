(* Effects: the rows that code performs, fitted into the rows that must hold
   them (effects.inference and effects.missing-effects). *)

module T = Types
open Check_state
open Check_unify

let perform ctx row loc = ctx.effects := (row, loc) :: !(ctx.effects)

(* Reports what a row can't hold, each kind of problem once (effects.missing-effects). Each row that effects are fitted into has its own reporter. In
   [main], a test and a doc example, a user-defined effect that reaches the
   row is [unhandled]'s code, E0512 (handlers.no-effect-reaches-main). *)
let reporter ?(unhandled = false) st =
  let reported = ref [] in
  let once key report =
    if not (List.mem key !reported) then (
      reported := key :: !reported;
      report ())
  in
  fun loc problems ->
    List.iter
      (function
        | Missing_io ->
            once "io" (fun () ->
                error st Code.e0502 loc
                  "this performs `io`, which the row doesn't declare")
        | Missing_raise t ->
            once "raise" (fun () ->
                error st Code.e0502 loc
                  "this raises `%s`, which the row doesn't declare" (show t))
        | Missing_var p ->
            once ("var " ^ p.name) (fun () ->
                error st Code.e0502 loc
                  "this performs `%s`, which the row doesn't declare" p.name)
        | Raise_mismatch (u, t) ->
            once "raise type" (fun () ->
                error st Code.e0503 loc
                  "this raises `%s`, but the same code raises `%s`" (show u)
                  (show t))
        | Missing_effect e when unhandled ->
            once ("effect " ^ e.name) (fun () ->
                error st Code.e0512 loc
                  "this performs `%s` outside every `with` of it, but nothing \
                   handles it here; install a handler: `with h { … }`"
                  e.name)
        | Missing_effect e ->
            once ("effect " ^ e.name) (fun () ->
                error st Code.e0502 loc
                  "this performs `%s`, which the row doesn't declare" e.name)
        | Effect_mismatch (e, given, held) ->
            once ("effect type " ^ e.name) (fun () ->
                error st Code.e0311 loc
                  "this performs `%s`, but the row holds `%s`"
                  (Types_show.effect_to_string (e, List.map T.zonk given))
                  (Types_show.effect_to_string (e, List.map T.zonk held)))
        | Cyclic_raise t ->
            error st Code.e0311 loc
              "this raises a value of type `%s`, which would make that type \
               contain itself"
              (show t))
      problems

(* Fits the effects performed so far, in order, into a row (effects.missing-effects).
   Each missing effect is reported where it first occurs. *)
let settle ?unhandled ?handled st effects row =
  let report = reporter ?unhandled st in
  List.iter (fun (r, loc) -> report loc (fit ?handled r row)) (List.rev effects)
