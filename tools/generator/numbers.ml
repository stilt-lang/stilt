(* The forms that make an integer or a float: arithmetic, conversions, and the
   methods of numbers. *)

open Code
open Context
open Ty

(* The operators on integers of kind [k]. *)
let int_operators expr b sc ~depth ~known k =
  let r = b.p.r in
  let d = depth - 1 in
  let me ?(known = false) () = expr b sc ~depth:d ~known (Int k) in
  let binary format =
    let x = me ~known () in
    let y = me () in
    compound ~known:x.known (format (operand x) (operand y))
  in
  [
    ( 4,
      fun () ->
        binary (fun x y -> x ^ Pick.one r [ " +% "; " -% "; " *% " ] ^ y) );
    (2, fun () -> binary (fun x y -> x ^ Pick.one r [ " & "; " | "; " ^ " ] ^ y));
    (* Operands masked so that the checked operators can't overflow, and
       divisors and shift amounts kept in range (numbers.integer-panics and numbers.shift-amounts). *)
    (2, fun () -> binary (Printf.sprintf "(%s & 15) + (%s & 15)"));
    (1, fun () -> binary (Printf.sprintf "(%s & 7) * (%s & 7)"));
    ( (if signed k then 1 else 0),
      fun () -> binary (Printf.sprintf "(%s & 15) - (%s & 15)") );
    ( 1,
      fun () ->
        let op = Pick.one r [ "<<"; ">>" ] in
        (* A shift gives its amount no type, so the amount fixes its own
           (numbers.shifts; numbers.shift-amounts). *)
        let x = me ~known () in
        let y = me ~known:true () in
        compound ~known:x.known
          (Printf.sprintf "%s %s (%s & %d)" (operand x) op (operand y)
             (bits k - 1)) );
    ( 1,
      fun () ->
        let op = Pick.one r [ "/"; "%" ] in
        binary (fun x y -> Printf.sprintf "%s %s ((%s & 7) + 1)" x op y) );
    ( 1,
      fun () ->
        let x = me ~known () in
        compound ~known:x.known ("!" ^ operand x) );
    (* A panicking program's arithmetic as written, unmasked, which panics
       where it overflows or divides by zero (numbers.integer-panics). *)
    ( (if b.p.panics then 1 else 0),
      fun () -> binary (fun x y -> x ^ Pick.one r [ " + "; " - "; " * " ] ^ y)
    );
    ( (if b.p.panics then 1 else 0),
      fun () -> binary (fun x y -> x ^ Pick.one r [ " / "; " % " ] ^ y) );
    ( (if signed k then 1 else 0),
      fun () ->
        let x = me ~known () in
        compound ~known:x.known ("-(" ^ operand x ^ " & 63)") );
  ]

(* The methods that make an integer of kind [k]: conversions from other
   numbers and from strings, and the methods of integers, lists and strings. *)
let int_methods expr b sc ~depth k =
  let r = b.p.r in
  let d = depth - 1 in
  let me ?(known = false) () = expr b sc ~depth:d ~known (Int k) in
  let name = int_name k in
  let narrower =
    List.filter (fun j -> not (widens ~from:j ~into:k)) int_kinds
  in
  let other () = expr b sc ~depth:d ~known:true (Int (Pick.one r int_kinds)) in
  [
    ( 2,
      fun () ->
        let j = Pick.one r int_kinds in
        let x = expr b sc ~depth:d ~known:true (Int j) in
        if widens ~from:j ~into:k then method_on x ("to_" ^ name) []
        else method_on x ("wrap_to_" ^ name) [] );
    ( (if narrower = [] then 0 else 1),
      fun () ->
        let x = expr b sc ~depth:d ~known:true (Int (Pick.one r narrower)) in
        compound
          (operand (method_on x ("to_" ^ name) []) ^ " else " ^ operand (me ()))
    );
    ( 1,
      fun () ->
        method_on (me ~known:true ())
          (Pick.one r [ "min"; "max" ])
          [ (me ()).text ] );
    ( 1,
      fun () ->
        let x = me ~known:true () in
        if signed k then method_on (compound (operand x ^ " & 63")) "abs" []
        else method_on x "abs" [] );
    ( 1,
      fun () ->
        let f =
          expr b sc ~depth:d ~known:true (Float (Pick.one r float_kinds))
        in
        compound
          (operand (method_on f ("to_" ^ name) []) ^ " else " ^ operand (me ()))
    );
    ( 1,
      fun () ->
        let s =
          if Pick.chance r 0.5 then atom ("\"" ^ Lit.int r k ^ "\"")
          else expr b sc ~depth:d ~known:true Str
        in
        compound
          (operand (method_on s ("to_" ^ name) []) ^ " else " ^ operand (me ()))
    );
    ( (if k = I64 then 3 else 0),
      fun () ->
        if Pick.chance r 0.6 then
          let t = random_ty b.p ~maps:false 1 in
          method_on (expr b sc ~depth:d ~known:true (List t)) "len" []
        else method_on (expr b sc ~depth:d ~known:true Str) "len" [] );
    (1, fun () -> method_on (other ()) ("wrap_to_" ^ name) []);
  ]

(* The arithmetic of std.integers on integers of kind [k], none of which can
   panic as the generator calls it. *)
let int_arithmetic expr b sc ~depth k =
  let r = b.p.r in
  let d = depth - 1 in
  let me ?(known = false) () = expr b sc ~depth:d ~known (Int k) in
  let other () = expr b sc ~depth:d ~known:true (Int (Pick.one r int_kinds)) in
  [
    ( 1,
      fun () ->
        method_on (me ~known:true ())
          (Pick.one r [ "saturating_add"; "saturating_sub" ])
          [ (me ()).text ] );
    ( 1,
      fun () ->
        let checked =
          method_on (me ~known:true ())
            (Pick.one r [ "checked_add"; "checked_sub"; "checked_mul" ])
            [ (me ()).text ]
        in
        compound (operand checked ^ " else " ^ operand (me ())) );
    ( 1,
      fun () ->
        (* A divisor from 1 to 8 neither divides by zero nor overflows. *)
        let y = me () in
        method_on (me ~known:true ())
          (Pick.one r [ "div_euclid"; "rem_euclid" ])
          [ "(" ^ operand y ^ " & 7) + 1" ] );
    ( (if k = I64 then 1 else 0),
      fun () ->
        method_on (other ())
          (Pick.one r [ "count_ones"; "leading_zeros"; "trailing_zeros" ])
          [] );
  ]

let int_ops expr b sc ~depth ~known k =
  int_operators expr b sc ~depth ~known k
  @ int_methods expr b sc ~depth k
  @ int_arithmetic expr b sc ~depth k

let float_ops expr b sc ~depth ~known k =
  let r = b.p.r in
  let d = depth - 1 in
  let me ?(known = false) () = expr b sc ~depth:d ~known (Float k) in
  let name = float_name k in
  [
    ( 4,
      fun () ->
        let x = me ~known () in
        let y = me () in
        compound ~known:x.known
          (operand x ^ Pick.one r [ " + "; " - "; " * "; " / " ] ^ operand y) );
    ( 2,
      fun () ->
        method_on (me ~known:true ())
          (Pick.one r [ "sqrt"; "floor"; "ceil"; "trunc"; "round"; "abs" ])
          [] );
    ( 1,
      fun () ->
        method_on (me ~known:true ())
          (Pick.one r [ "min"; "max" ])
          [ (me ()).text ] );
    ( 2,
      fun () ->
        let x = expr b sc ~depth:d ~known:true (Int (Pick.one r int_kinds)) in
        method_on x ("to_" ^ name) [] );
    ( 1,
      fun () ->
        let x =
          expr b sc ~depth:d ~known:true (Float (Pick.one r float_kinds))
        in
        method_on x ("to_" ^ name) [] );
    ( 1,
      fun () ->
        let x = me ~known () in
        compound ~known:x.known ("-" ^ operand x) );
  ]
