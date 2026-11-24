(* The forms that make a [bool]: comparisons, logic, and the methods that test
   a value. *)

open Code
open Context
open Ty

(* A [bool] whose type is fixed without an expected type. *)
let cond expr b sc ~depth = expr b sc ~depth ~known:true Bool

let bool_ops expr b sc ~depth =
  let r = b.p.r in
  let d = depth - 1 in
  let me () = cond expr b sc ~depth:d in
  [
    ( 4,
      fun () ->
        let t = random_ty b.p ~maps:false 1 in
        let ops =
          if Ty.ordered ~decls:b.p.decls t && Pick.chance r 0.5 then
            [ "<"; "<="; ">"; ">=" ]
          else [ "=="; "!=" ]
        in
        let x = expr b sc ~depth:d ~known:true t in
        let y = expr b sc ~depth:d ~known:false t in
        compound (operand x ^ " " ^ Pick.one r ops ^ " " ^ operand y) );
    ( 2,
      fun () ->
        let x = me () in
        let y = me () in
        compound (operand x ^ Pick.one r [ " && "; " || " ] ^ operand y) );
    (1, fun () -> compound ("!" ^ operand (me ())));
    ( 2,
      fun () ->
        let t = random_ty b.p ~maps:false 1 in
        let xs = expr b sc ~depth:d ~known:true (List t) in
        Pick.run r
          [
            (1, fun () -> method_on xs "is_empty" []);
            ( 1,
              fun () ->
                method_on xs "contains"
                  [ (expr b sc ~depth:d ~known:false t).text ] );
            ( 1,
              fun () ->
                method_on xs
                  (Pick.one r [ "any"; "all" ])
                  [ Closures.closure expr b sc ~depth:d t Bool ] );
          ] );
    ( 1,
      fun () ->
        method_on
          (expr b sc ~depth:d ~known:true Str)
          (Pick.one r [ "contains"; "starts_with"; "ends_with" ])
          [ (expr b sc ~depth:d ~known:false Str).text ] );
    ( 1,
      fun () ->
        let o =
          expr b sc ~depth:d ~known:true (Option (random_ty b.p ~maps:false 1))
        in
        method_on o (Pick.one r [ "is_some"; "is_none" ]) [] );
    ( 1,
      fun () ->
        let f =
          expr b sc ~depth:d ~known:true (Float (Pick.one r float_kinds))
        in
        method_on f "is_nan" [] );
  ]
