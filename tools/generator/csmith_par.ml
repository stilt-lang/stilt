(* Calls of [std.par] (par.std-par) at the end of a csmith program's [main], made
   from a stream of their own, so that the rest of the program is the one the
   same seed makes without them. Their lists are long enough, most of the time,
   for a call to run on several threads, so that differential testing compares
   the compiler's parallel runs with the reference interpreter's sequential ones: the values
   of [map], [each], [both] and [fold], the bits of float folds, whose tree
   par.fold-tree fixes, and, last and rarely, the panic that a call reports when
   several of its closures' calls panic (par.panics). Closures perform no effect,
   since their scope has neither [io] nor raises. *)

open Code
open Context
open Ty

(* How likely a program is to call [std.par], and, when it does, to end with a
   call whose closure may panic. A panic ends a bundle's run, so it is rare. *)
let calling = 0.5
let panicking = 0.08

let wanted seed =
  Pick.chance (Pick.make (Hashtbl.hash (seed, "uses par"))) calling

let typed t = Ty.to_string t
let print_line name = line (Printf.sprintf "print(\"%s: {%s}\")" name name)

(* The scope with a new variable of type [List<t>], its name, and the line
   that binds it to a literal of a few elements, usually enough for a call to
   run on several threads. *)
let list_of b sc t =
  let r = b.p.r in
  let n =
    Pick.run r
      [
        (1, fun () -> Pick.between r 0 1);
        (2, fun () -> Pick.between r 2 3);
        (7, fun () -> Pick.between r 4 12);
      ]
  in
  let items =
    Pick.times n (fun () -> (Expr.expr b sc ~depth:2 ~known:false t).text)
  in
  let name = fresh b.p "pl" in
  ( declare sc name (List t) ~mutable_:false,
    name,
    line
      (Printf.sprintf "let %s: List<%s> = [%s]" name (typed t)
         (String.concat ", " items)) )

(* A closure's parameter of type [t]. *)
let param b t = { name = fresh b.p "x"; ty = t; mutable_ = false }

(* [body] of the type [t], or with [~fails], a panic whose detail shows
   [shown] when a condition holds. *)
let body ?(fails = false) b sc t shown =
  let text = (Expr.expr b sc ~depth:2 ~known:true t).text in
  if not fails then text
  else
    let c = Expr.cond b sc ~depth:2 in
    let detail = String.concat " " (List.map (fun v -> "{" ^ v ^ "}") shown) in
    Printf.sprintf "if %s { panic(\"%s\") } else { %s }" (head c.text) detail
      text

(* [par.map] of a list into a list of another type. *)
let map ?fails b (sc, setup, xs, t) =
  let u = random_ty b.p ~maps:false 1 in
  let x = param b t in
  let f = body ?fails b (closure_scope sc [ x ]) u [ x.name ] in
  let name = fresh b.p "pm" in
  setup
  @ line
      (Printf.sprintf "let %s: List<%s> = par.map(%s, |%s| %s)" name (typed u)
         xs x.name f)
  @ print_line name

(* [par.each] of a copy of the list, which the list keeps. *)
let each ?fails b (sc, setup, xs, t) =
  let y = param b t in
  let f = body ?fails b (closure_scope sc [ y ]) t [ y.name ] in
  let name = fresh b.p "pe" in
  setup
  @ line (Printf.sprintf "var %s: List<%s> = %s" name (typed t) xs)
  @ line
      (Printf.sprintf "par.each(inout %s, |inout %s| { %s = %s })" name y.name
         y.name f)
  @ line (Printf.sprintf "print(\"%s: {%s} {%s}\")" name name xs)

(* [par.fold] of the list, whose combination needn't be associative. *)
let fold ?fails b (sc, setup, xs, t) =
  let p, q = (param b t, param b t) in
  let f = body ?fails b (closure_scope sc [ p; q ]) t [ p.name; q.name ] in
  let empty = (Expr.expr b sc ~depth:2 ~known:false t).text in
  let name = fresh b.p "pf" in
  setup
  @ line
      (Printf.sprintf "let %s: %s = par.fold(%s, %s, |%s, %s| %s)" name
         (typed t) xs empty p.name q.name f)
  @ print_line name

(* [par.both] of two closures of no parameters. *)
let both b sc =
  let a, c = (random_ty b.p ~maps:false 1, random_ty b.p ~maps:false 1) in
  let f t = (Expr.expr b (closure_scope sc []) ~depth:2 ~known:true t).text in
  let name = fresh b.p "pb" in
  line
    (Printf.sprintf "let %s: %s = par.both(|| %s, || %s)" name
       (typed (Tuple [ a; c ]))
       (f a) (f c))
  @ print_line name

(* A float fold whose tree, of terms of very different sizes, gives other bits
   than a fold from left to right would. *)
let float_fold b =
  let r = b.p.r in
  let terms =
    [ "1e16"; "-1e16"; "1.0"; "0.1"; "-2.5"; "3.25e-8"; "1e300"; "-7.0" ]
  in
  let xs = Pick.times (Pick.between r 4 12) (fun () -> Pick.one r terms) in
  let op = Pick.one r [ "+"; "-"; "*" ] in
  let name = fresh b.p "pg" in
  line
    (Printf.sprintf "let %s: f64 = par.fold([%s], 0.0, |p, q| p %s q)" name
       (String.concat ", " xs) op)
  @ print_line name

(* A call of [map], [each] or [fold] over a new list. *)
let over_list ?fails b sc =
  let t = random_ty b.p ~maps:false 1 in
  let sc', xs, setup = list_of b sc t in
  let call = Pick.one b.p.r [ map; each; fold ] in
  call ?fails b (sc', setup, xs, t)

let calls p sc seed =
  let p = { p with r = Pick.make (Hashtbl.hash (seed, "par")) } in
  let b = { p; budget = 4_000; spent = 0 } in
  let sc = { sc with weight = 1 } in
  let r = p.r in
  let one () =
    Pick.run r
      [
        (5, fun () -> over_list b sc);
        (2, fun () -> both b sc);
        (2, fun () -> float_fold b);
      ]
  in
  let calls = List.concat (Pick.times (Pick.between r 1 4) one) in
  calls @ if Pick.chance r panicking then over_list ~fails:true b sc else []
