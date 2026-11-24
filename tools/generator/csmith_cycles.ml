(* Cycles through [Shared<T>] handles (cycles.through-shared-values) in a csmith program, made from a
   stream of their own, so that the rest of the program is the one the same
   seed makes without them. [main] links one to four handles into a ring,
   which it walks through [when]s, printing each value, and sometimes writes a
   value through one of them first; a function makes a few thousand two-handle
   rings and lets each go, so that the compiler's runtime collects them while
   the program runs, as well as at its end, where a debug build checks that
   every count is back to zero. Differential testing compares the values the
   walks print with the reference interpreter's, whose memory frees cycles itself. *)

open Code
open Context

(* How likely a program is to link handles. *)
let using = 0.3

let wanted seed =
  Pick.chance (Pick.make (Hashtbl.hash (seed, "uses cycles"))) using

let typed t = Ty.to_string t

(* The scope of a function of no parameters that performs [io]. *)
let empty =
  {
    vars = [];
    frozen = [];
    loop = false;
    may_raise = false;
    io = false;
    returns = None;
    weight = 1;
  }

(* The type of a ring's links, holding values of [t], the function that walks a
   ring, and the one that makes [n] rings and lets them go. Each program gives
   its walk a mark [k] of its own, so that the ten programs that
   [just differential] runs as one don't declare equal bodies, which W0302
   would report (docs.duplicate-bodies). *)
let helpers b t k =
  let value () = (Expr.expr b empty ~depth:2 ~known:true t).text in
  [
    line
      (Printf.sprintf
         "type Link = { value: %s, next: Option<sync.Shared<Link>> }" (typed t));
    block_lines "fn link_walk(start: sync.Shared<Link>, steps: i64) / io {"
      (line "var at = start"
      @ block_lines "for _ in 0..steps {"
          (block_lines "let next = when at {"
             (line (Printf.sprintf "print(\"link %d: {at.value}\")" k)
             @ line "at.next")
             "}"
          @ line "at = next else at")
          "}")
      "}";
    block_lines "fn link_spin(n: i64) -> i64 {"
      (line "var made = 0"
      @ block_lines "for _ in 0..n {"
          (line
             (Printf.sprintf
                "let a = sync.Shared.new(Link { value: %s, next: None })"
                (value ()))
          @ line
              (Printf.sprintf
                 "let b = sync.Shared.new(Link { value: %s, next: Some(a) })"
                 (value ()))
          @ line "when a { a.next = Some(b) }"
          @ line "made += 1")
          "}"
      @ line "made")
      "}";
  ]

(* The lines of [main] that link [k] handles into a ring, maybe write a value
   through one, and walk the ring past its start. *)
let ring b sc t =
  let r = b.p.r in
  let k = Pick.between r 1 4 in
  let names = List.init k (fun _ -> fresh b.p "lk") in
  let value () = (Expr.expr b sc ~depth:2 ~known:true t).text in
  let made =
    List.mapi
      (fun i name ->
        let next =
          if i = 0 then "None" else "Some(" ^ List.nth names (i - 1) ^ ")"
        in
        line
          (Printf.sprintf
             "let %s = sync.Shared.new(Link { value: %s, next: %s })" name
             (value ()) next))
      names
  in
  let first = List.hd names and last = List.nth names (k - 1) in
  let closer = fresh b.p "lk" in
  let written =
    if Pick.chance r 0.5 then
      let at = Pick.one r names in
      line (Printf.sprintf "when %s { %s.value = %s }" at at (value ()))
    else []
  in
  List.concat made
  @ line (Printf.sprintf "let %s = %s" closer last)
  @ line (Printf.sprintf "when %s { %s.next = Some(%s) }" first first closer)
  @ written
  @ line
      (Printf.sprintf "link_walk(%s, %d)" last (Pick.between r 1 ((2 * k) + 1)))

let uses p sc seed =
  let p = { p with r = Pick.make (Hashtbl.hash (seed, "cycles")) } in
  let b = { p; budget = 4_000; spent = 0 } in
  let sc = { sc with weight = 1 } in
  let t = random_ty p ~maps:false 1 in
  let helpers = helpers b t (Pick.between p.r 7 999_999) in
  let rings =
    List.concat (Pick.times (Pick.between p.r 1 2) (fun () -> ring b sc t))
  in
  let spun = Pick.between p.r 1 3_000 in
  ( helpers,
    rings @ line (Printf.sprintf "print(\"link spin: {link_spin(%d)}\")" spun)
  )
