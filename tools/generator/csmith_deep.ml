(* Deep recursion and large lists in a csmith program, made from a stream of
   their own, so that the rest of the program is the one the same seed makes
   without them. [main] calls recursive functions tens of thousands of calls
   deep: one that accumulates through wrapping arithmetic, one whose result
   waits on its recursive call, a pair that call each other, one that walks a
   list by index, and one that sums a chain of a recursive variant type,
   which a loop builds and another loop measures (declarations.recursive-types).
   It builds lists of 10^5 elements, and sometimes of 10^6, by [push],
   [List.generate] and [List.repeat], and prints their lengths, extremes,
   folds, sorts and the checked, wrapping and saturating sums of numbers.
   The depths stay a fifth of what the reference interpreter's stack holds
   for these bodies, the shallowest of the two implementations'
   (program.exit-statuses), so a program never overflows it. *)

open Code
open Ty

(* How likely a program is to recurse deeply and build large lists. *)
let using = 0.03

let wanted seed =
  Pick.chance (Pick.make (Hashtbl.hash (seed, "uses depth"))) using

(* The deepest recursion a call makes, and its usual size. *)
let deepest = 30_000

let print_of splices =
  line (Printf.sprintf "print(\"%s\")" (String.concat " " splices))

(* The method that turns an integer of kind [k] into an [i64]: [to_i64] when
   every value fits, and [wrap_to_i64] otherwise (numbers.conversions). *)
let wide k = if widens ~from:k ~into:I64 then "to_i64" else "wrap_to_i64"

(* The recursive functions and the chain's type, over integers of kind [k].
   Each program gives them a mark [m] of its own, so that the ten programs
   that [just differential] runs as one don't declare equal bodies, which
   W0302 would report (docs.duplicate-bodies). *)
let helpers k m =
  let t = int_name k and wide = wide k in
  [
    line (Printf.sprintf "type DpChain = | DpEnd | DpNode(%s, DpChain)" t);
    block_lines
      (Printf.sprintf "fn dp_down(n: i64, acc: %s) -> %s {" t t)
      (line
         (Printf.sprintf
            "if n <= 0 { acc } else { dp_down(n - 1, acc *%% (%d).wrap_to_%s() \
             +%% (n %% %d).wrap_to_%s()) }"
            (m mod 97) t m t))
      "}";
    block_lines "fn dp_depth(n: i64, xs: List<i64>) -> i64 {"
      (line "if n <= 0 { return xs.len() }"
      @ line "let here = xs[n % xs.len()]"
      @ line (Printf.sprintf "here.min(%d) +%% dp_depth(n - 1, xs) - (n & 1)" m)
      )
      "}";
    line
      (Printf.sprintf
         "fn dp_even(n: i64, k: i64) -> bool { if n <= 0 { k %% 2 == 0 } else \
          { dp_odd(n - 1, k +%% %d) } }"
         m);
    line
      "fn dp_odd(n: i64, k: i64) -> bool { if n <= 0 { k % 3 == 0 } else { \
       dp_even(n - 1, k *% 3) } }";
    block_lines
      (Printf.sprintf "fn dp_sum(xs: List<%s>, i: i64) -> i64 {" t)
      (line
         (Printf.sprintf
            "if i >= xs.len() { %d } else { xs[i].%s() +%% dp_sum(xs, i + 1) }"
            m wide))
      "}";
    block_lines
      (Printf.sprintf "fn dp_chain(n: i64) -> DpChain {")
      (line "var c = DpEnd"
      @ line
          (Printf.sprintf
             "for i in 0..n { c = DpNode((i *%% %d).wrap_to_%s(), c) }" m t)
      @ line "c")
      "}";
    line
      (Printf.sprintf
         "fn dp_total(c: DpChain) -> i64 { match c { DpEnd => 0, DpNode(v, \
          rest) => v.%s() +%% dp_total(rest) } }"
         wide);
    block_lines "fn dp_length(c: DpChain) -> i64 {"
      (line "var n = 0" @ line "var at = c"
      @ line
          "while true { match at { DpEnd => break, DpNode(_, rest) => { n += \
           1; at = rest } } }"
      @ line "n")
      "}";
  ]

let depth r = Pick.between r 10_000 deepest

(* The calls of the recursive functions, and the chain [dp_l] of [long]
   nodes. *)
let recursions r k ~long =
  let t = int_name k in
  let lo, hi = Lit.bounds k in
  let xs () =
    String.concat ", "
      (Pick.times (Pick.between r 1 4) (fun () ->
           string_of_int (Pick.between r (-9) 9)))
  in
  print_of
    [
      Printf.sprintf "{dp_down(%d, %s)}" (depth r) (Pick.one r [ lo; hi; "7" ]);
      Printf.sprintf "{dp_depth(%d, [%s])}" (depth r) (xs ());
      Printf.sprintf "{dp_even(%d, %d)}" (depth r) (Pick.between r 0 5);
    ]
  @ line (Printf.sprintf "let dp_c = dp_chain(%d)" (depth r))
  @ print_of [ "{dp_total(dp_c)} {dp_length(dp_c)}" ]
  @ line (Printf.sprintf "let dp_l = dp_chain(%d)" long)
  @ print_of [ "{dp_length(dp_l)}" ]
  @ line
      (Printf.sprintf
         "let dp_s: List<%s> = List.generate(%d, |i| (i *%% %d).wrap_to_%s())" t
         (depth r) (Pick.between r 3 99_999) t)
  @ print_of [ "{dp_sum(dp_s, 0)}" ]

(* The lines that make the list [dp_xs] of [n] integers of kind [k]. *)
let made r k n =
  let t = int_name k in
  let lo, hi = Lit.bounds k in
  Pick.run r
    [
      ( 2,
        fun () ->
          line (Printf.sprintf "var dp_xs: List<%s> = []" t)
          @ line
              (Printf.sprintf
                 "for i in 0..%d { dp_xs.push((i *%% %d).wrap_to_%s()) }" n
                 (Pick.between r 3 999_999_999)
                 t) );
      ( 1,
        fun () ->
          line
            (Printf.sprintf
               "let dp_xs = List.generate(%d, |i| (i *%% %d +%% \
                %d).wrap_to_%s())"
               n (Pick.between r 3 999_999) (Pick.between r (-99) 99) t) );
      ( 1,
        fun () ->
          line
            (Printf.sprintf "let dp_xs: List<%s> = List.repeat(%s, %d)" t
               (Pick.one r [ lo; hi; Lit.int r k ])
               n) );
    ]

(* What is read of [dp_xs]: its extremes, folds, and checked, wrapping and
   saturating sums, which reach the bounds of [k], and its sorts and
   searches. Each reads every element at least once. *)
let reads k =
  let t = int_name k and hi = snd (Lit.bounds k) in
  [
    "{dp_xs.max()} {dp_xs.min()}";
    "{dp_xs.fold(dp_z, |a, x| a +% x)}";
    Printf.sprintf "{dp_xs.fold(%s.MIN, |a, x| a.saturating_add(x))}" t;
    Printf.sprintf "{dp_xs.fold(%s.MAX, |a, x| a.saturating_sub(x))}" t;
    "{dp_xs.fold(Some(dp_z), |a, x| if let Some(s) = a { s.checked_add(x) } \
     else { None })}";
    Printf.sprintf "{dp_xs.fold(0, |a, x| a +%% x.%s())}" (wide k);
    "{dp_xs.sorted().take(3)} {dp_xs.deduped().len()}";
    Printf.sprintf "{dp_xs.filter(|x| x == %s).len()}" hi;
    "{dp_xs.reversed().take(2)} {dp_xs.contains(dp_z)}";
  ]

(* A large list of [n] integers of kind [k], with its length and [some] of
   what [reads] reads. *)
let large r k n ~some =
  let rec pick chosen = function
    | [] -> List.rev chosen
    | x :: rest ->
        if List.length chosen < some && Pick.chance r 0.5 then
          pick (x :: chosen) rest
        else pick chosen rest
  in
  made r k n
  @ line (Printf.sprintf "let dp_z: %s = %s" (int_name k) (Lit.int r k))
  @ print_of ("{dp_xs.len()} {dp_xs.take_last(3)}" :: pick [] (reads k))

(* A chain of tens of thousands of nodes and lists of a hundred thousand
   elements: larger ones reach no other code, and cost the differential seconds
   each. *)
let uses seed =
  let r = Pick.make (Hashtbl.hash (seed, "depth")) in
  let k = Pick.one r int_kinds in
  let long = Pick.between r 20_000 40_000 in
  let n, some = (Pick.between r 100_000 105_000, 2) in
  let lines =
    block_lines "{" (recursions r k ~long) "}"
    @ block_lines "{" (large r k n ~some) "}"
  in
  (helpers k (Pick.mark r seed), lines)
