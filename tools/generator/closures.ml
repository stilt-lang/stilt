(* Closures, whose bodies read copies of the variables in scope. *)

open Code
open Context
open Ty

(* [xs.fold(init, |acc, x| body)], whose accumulator has type [ty]. *)
let fold expr b sc ~depth ty =
  let d = depth - 1 in
  let elem = random_ty b.p ~maps:false 1 in
  let xs = expr b sc ~depth:d ~known:true (List elem) in
  let init = expr b sc ~depth:d ~known:true ty in
  let acc = { name = fresh b.p "acc"; ty; mutable_ = false } in
  let x = { name = fresh b.p "x"; ty = elem; mutable_ = false } in
  let body = expr b (closure_scope sc [ acc; x ]) ~depth:d ~known:false ty in
  atom
    (Printf.sprintf "%s.fold(%s, |%s, %s| %s)" (operand xs) init.text acc.name
       x.name body.text)

(* A closure of one parameter of type [param], whose body has type [ty]. A
   body whose type nothing else fixes, as [map]'s, is [~known]. *)
let closure expr b sc ~depth ?(known = false) param ty =
  let x = { name = fresh b.p "x"; ty = param; mutable_ = false } in
  let body = expr b (closure_scope sc [ x ]) ~depth ~known ty in
  "|" ^ x.name ^ "| " ^ body.text
