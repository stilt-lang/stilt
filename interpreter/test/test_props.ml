(* Tests of properties' cases and counterexamples (tests.property-cases, tests.running-cases and tests.shrinking),
   whose seeds, draws and values conformance tests can't observe, since they
   see only whether each property passed (conformance.observables). The expected
   values are worked out from the rules: FNV-1a's and SplitMix64's published
   values, and the draws they give. *)

open Stilt

let%expect_test "a seed is the FNV-1a hash of the text (tests.seeds)" =
  List.iter
    (fun s -> Printf.printf "%016Lx\n" (Prop_rand.seed s))
    [ ""; "a"; "foobar" ];
  [%expect
    {|
    cbf29ce484222325
    af63dc4c8601ec8c
    85944171f73967e8
    |}]

let%expect_test
    "draws are SplitMix64's, from the seed plus the case (tests.draws)" =
  let g = Prop_rand.create 0L 0 in
  for _ = 1 to 4 do
    Printf.printf "%016Lx\n" (Prop_rand.next g)
  done;
  let g = Prop_rand.create (-5L) 5 in
  Printf.printf "%016Lx\n" (Prop_rand.next g);
  let g = Prop_rand.create 0L 0 in
  print_endline
    (String.concat " "
       (List.init 12 (fun _ -> string_of_int (Prop_rand.below_int g 4))));
  [%expect
    {|
    e220a8397b1dcdaf
    6e789e6aa1b965f4
    06c45d188009454f
    f88bb8a8724c81ec
    e220a8397b1dcdaf
    3 0 3 0 3 2 1 0 3 2 1 2
    |}]

let shown : Value.value -> string = function
  | Int x -> Int64.to_string x
  | Float x -> Printf.sprintf "%08lx" (Int32.bits_of_float x)
  | Bool b -> string_of_bool b
  | Str s ->
      let cs = ref [] in
      String.iteri
        (fun i _ ->
          let d = String.get_utf_8_uchar s i in
          if Uchar.utf_decode_is_valid d then
            cs :=
              Printf.sprintf "%x" (Uchar.to_int (Uchar.utf_decode_uchar d))
              :: !cs)
        s;
      "[" ^ String.concat " " (List.rev !cs) ^ "]"
  | _ -> "?"

let%expect_test "scalars at size 3, drawn in order (tests.generated-scalars)" =
  let i64 = Option.get (Ints.of_name "i64")
  and u32 = Option.get (Ints.of_name "u32") in
  for state = 0 to 5 do
    let g = Prop_rand.create (Int64.of_int state) 0 in
    let draw node = shown (Prop_gen.scalar g ~size:3 node) in
    let i = draw (Int i64) in
    let u = draw (Int u32) in
    let s = draw Str in
    let f = draw (Float true) in
    Printf.printf "%s %s %s %s\n" i u s f
  done;
  [%expect
    {|
    7960286522194355700 1917616620 [61 65 9] 3f808000
    -3 3 [48] 3f9f8000
    -3 4293391972 [d2586] 5887ccff
    0 3 [f25b8 7a] 3ec20000
    1 653523102 [3d] 3f160000
    2 3657808197 [51] 9ee9e9e8
    |}]

let%expect_test
    "low bits of a draw, read as two's complement (tests.generated-scalars)" =
  let draw name =
    let g = Prop_rand.create 0L 0 in
    shown (Prop_gen.scalar g ~size:5 (Int (Option.get (Ints.of_name name))))
  in
  print_endline (String.concat " " (List.map draw [ "i64"; "u8"; "i8"; "u64" ]));
  let g = Prop_rand.create 0L 0 in
  print_endline (shown (Prop_gen.scalar g ~size:5 Bool));
  [%expect
    {|
    7960286522194355700 244 -12 7960286522194355700
    true
    |}]

(* The [property] objects of a program's properties, from [test]. *)
let verdicts text =
  let sources =
    [
      {
        Program.module_path = Program.module_path "main.lt";
        file = "main.lt";
        text;
        package = 0;
      };
    ]
  in
  match Driver.analyse sources with
  | [], Some (env, hir, program) -> (
      match Eval.test ~out:stdout env hir program with
      | Ok verdicts ->
          List.filter_map
            (fun (v : Eval.verdict) -> Option.map Eval_props.json v.property)
            verdicts
      | Error reason -> [ reason ])
  | _ -> [ "the program has errors" ]

let%expect_test
    "counterexamples, shrunk by tests.shrinking and tests.shrink-candidates" =
  List.iter print_endline
    (verdicts
       "/// prop: |xs: List<i64>| xs.len() > 0\n\
        /// prop: |x: i64| x + 1 > x\n\
        /// prop: |x: i64, y: i64| x + y == y + x || x > 1000000\n\
        /// prop: |xs: List<i64>| reverse(reverse(xs)) == xs\n\
        fn reverse(xs: List<i64>) -> List<i64> { xs.fold([], |acc, x| \
        [x].concat(acc)) }\n");
  [%expect
    {|
    {"seed": "281aaabf0d00138c", "cases": 1, "case": 0, "counterexample": ["[]"], "failure": "false", "shrinks": 0}
    {"seed": "29b4b0c2b0880fe4", "cases": 36, "case": 35, "counterexample": ["9223372036854775807"], "failure": "panic: overflow", "detail": "the result doesn't fit in `i64`", "shrinks": 0}
    {"seed": "b14633fb1d644fa9", "cases": 9, "case": 8, "counterexample": ["1", "9223372036854775807"], "failure": "panic: overflow", "detail": "the result doesn't fit in `i64`", "shrinks": 62}
    {"seed": "e13282d7381055c5", "cases": 100}
    |}]

let%expect_test "a counterexample is shown by its structure, not its Show" =
  List.iter print_endline
    (verdicts
       "type Wrap = | Wrap(i64)\n\
        impl Show for Wrap { fn show(self) -> str { assert false\n\
        \"\" } }\n\
        /// prop: |w: Wrap| match w { Wrap(n) => n < 5 }\n\
        fn wrap(n: i64) -> Wrap { Wrap(n) }\n");
  [%expect
    {| {"seed": "41996ed4b41a2b47", "cases": 2, "case": 1, "counterexample": ["Wrap(5)"], "failure": "false", "shrinks": 62} |}]

let%expect_test "shrinking stops after 1,000 runs (tests.shrinking)" =
  List.iter print_endline
    (verdicts "/// prop: |x: i64| x < 100000\nfn f() {}\n");
  [%expect
    {| {"seed": "8c843fe3ef7143dd", "cases": 3, "case": 2, "counterexample": ["169039"], "failure": "false", "shrinks": 348} |}]

let%expect_test "the same verdicts on every run" =
  let text = "/// prop: |s: str, n: u8| s.len() < n.to_i64()\nfn f() {}\n" in
  print_endline (string_of_bool (verdicts text = verdicts text));
  [%expect {| true |}]
