(* Tests of the procedural macros (macros.procedural-declarations and macros.procedural-uses) that csmith programs use and of the
   mistakes planted in them: the layout of a program with macros, that its
   stream changes nothing else of the program, that its modules declare every
   kind of macro with every form of quote and splice and its programs use them
   everywhere a use may stand, and that each mutant holds exactly one mistake
   in its macros. That the reference interpreter accepts the programs and reports each
   mistake is what `just generated` and `just mutated` check. *)

open Stilt_gen

let seeds n = List.init n succ
let with_macros n = List.filter Csmith_macros.wanted (seeds n)
let lines text = String.split_on_char '\n' text

let contains text part =
  let n = String.length part in
  let rec go i =
    i + n <= String.length text && (String.sub text i n = part || go (i + 1))
  in
  go 0

let count p xs = List.length (List.filter p xs)

(* macros.parts splits a use's group at its commas outside nested groups. *)
let%expect_test "parts" =
  List.iter
    (fun text -> print_endline (Csmith_macros.part text))
    [ "f(1, 2)"; "\"a, \\\"b\""; "{ let k: (i8, str) = c; k }"; "x, y" ];
  [%expect
    {|
    f(1, 2)
    "a, \"b"
    { let k: (i8, str) = c; k }
    (x, y)
    |}]

(* Three programs in ten use macros, each a directory program whose
   [main.lt] imports its module of macros, which is a module of its own in a
   bundle. *)
let%expect_test "layout" =
  let laid_out seed =
    let name = Printf.sprintf "seed_%d" seed and m = Macro_module.name seed in
    let files = Csmith.files seed and modules = Csmith.module_files seed in
    List.map fst files = [ name ^ "/main.lt"; name ^ "/" ^ m ^ ".lt" ]
    && List.mem ("meta use " ^ m) (lines (List.assoc (name ^ "/main.lt") files))
    && List.map fst modules = [ name ^ ".lt"; m ^ ".lt" ]
  in
  let alone seed =
    List.map fst (Csmith.files seed) = [ Printf.sprintf "seed_%d.lt" seed ]
  in
  let macros = with_macros 1000 in
  Printf.printf "%d of 1000, laid out: %b, the others alone: %b\n"
    (List.length macros)
    (List.for_all laid_out macros)
    (List.for_all (fun s -> List.mem s macros || alone s) (seeds 1000));
  [%expect {| 120 of 1000, laid out: true, the others alone: true |}]

(* The lines of the program without macros come, in order, among those of the
   program with them, which only adds the lines that import and use them. *)
let%expect_test "nothing else changes" =
  let rec within xs ys =
    match (xs, ys) with
    | [], _ -> true
    | _, [] -> false
    | x :: xs', y :: ys' -> if x = y then within xs' ys' else within xs ys'
  in
  let kept seed =
    within
      (lines (Csmith.program ~macros:false seed))
      (lines (Csmith.program seed))
  in
  Printf.printf "%b\n" (List.for_all kept (with_macros 300));
  [%expect {| true |}]

(* The first 300 programs with macros: the text of each one's module of
   macros, its own text and its module. *)
let sample =
  lazy
    (with_macros 1000
    |> List.filteri (fun i _ -> i < 300)
    |> List.map (fun seed ->
        let m = Macro_module.make seed in
        (Macro_module.text m, Csmith.program seed, m)))

let counted texts things =
  List.iter
    (fun (name, holds) -> Printf.printf "%s %d\n" name (count holds texts))
    things

(* How many of the sample's modules declare a macro of each kind. *)
let%expect_test "kinds" =
  let declares is (_, _, (m : Macro_kinds.t)) =
    List.exists (fun (d : Macro_kinds.decl) -> is d.kind) m.decls
  in
  counted (Lazy.force sample)
    (List.map
       (fun (name, is) -> (name, declares is))
       [
         ("mix", function Macro_kinds.Mix _ -> true | _ -> false);
         ("spell", function Macro_kinds.Spell _ -> true | _ -> false);
         ("listed", ( = ) Macro_kinds.Listed);
         ("tupled", ( = ) Macro_kinds.Tupled);
         ("called", function Macro_kinds.Called _ -> true | _ -> false);
         ("record", ( = ) Macro_kinds.Record);
         ("words", ( = ) Macro_kinds.Words);
         ("twice", function Macro_kinds.Twice _ -> true | _ -> false);
         ("either", ( = ) Macro_kinds.Either);
         ("some_of", ( = ) Macro_kinds.Some_of);
         ("pair", ( = ) Macro_kinds.Pair);
         ("spelled", ( = ) Macro_kinds.Spelled);
         ("shape", function Macro_kinds.Shape _ -> true | _ -> false);
       ]);
  [%expect
    {|
    mix 120
    spell 86
    listed 120
    tupled 59
    called 59
    record 58
    words 56
    twice 120
    either 57
    some_of 45
    pair 31
    spelled 46
    shape 120
    |}]

(* How many of the sample's modules write each parameter type, each form of
   quote and each splice. *)
let%expect_test "quotes" =
  counted (Lazy.force sample)
    (List.map
       (fun form -> (form, fun (m, _, _) -> contains m form))
       [
         "meta.Expr";
         "meta.Pattern";
         "meta.Type";
         "meta.Text";
         "meta.Tokens";
         "meta.cursor";
         "meta.fresh";
         "quote {";
         "quote pattern {";
         "quote type {";
         "quote field {";
         "$(";
         "$..";
         "let $";
       ]);
  [%expect
    {|
    meta.Expr 120
    meta.Pattern 120
    meta.Type 120
    meta.Text 98
    meta.Tokens 120
    meta.cursor 120
    meta.fresh 120
    quote { 120
    quote pattern { 120
    quote type { 120
    quote field { 58
    $( 98
    $.. 120
    let $ 120
    |}]

(* How many of the sample's programs use a macro in each place. *)
let%expect_test "uses" =
  counted (Lazy.force sample)
    (List.map
       (fun (name, text) -> (name, fun (_, p, _) -> contains p text))
       [
         ("in an arm's pattern", "    macros_");
         ("in a type", ": macros_");
         ("as a result type", ") -> macros_");
         ("with a trailing block", "!() { ");
         ("within a use", "!(macros_");
       ]);
  [%expect
    {|
    in an arm's pattern 120
    in a type 120
    as a result type 62
    with a trailing block 91
    within a use 20
    |}]

(* The code of each annotation of the mutant's files, with its file and
   whether its line is in the module of macros or uses a macro. *)
let planted count seed =
  let marker = "//~ ERROR " in
  let n = String.length marker in
  let annotation line =
    let rec at i =
      if i + n + 5 > String.length line then None
      else if String.sub line i n = marker then Some (String.sub line (i + n) 5)
      else at (i + 1)
    in
    at 0
  in
  List.concat_map
    (fun (path, text) ->
      let file = Filename.basename path in
      List.filter_map
        (fun line ->
          Option.map
            (fun code ->
              (file, (file <> "main.lt" || contains line "macros_", code)))
            (annotation line))
        (lines text))
    (Mutants.mutant ~count seed)

(* Each mutant with macros holds exactly one mistake in them, the first of
   its mistakes, and each kind of mistake is planted about as often. *)
let%expect_test "mutants" =
  let macros = with_macros 900 in
  let ones = List.map (planted 1) macros in
  let fives = List.map (planted 5) macros in
  let in_macros found = count (fun (_, (macro, _)) -> macro) found in
  Printf.printf "one: %b, of five: %b\n"
    (List.for_all
       (fun found -> List.length found = 1 && in_macros found = 1)
       ones)
    (List.for_all (fun found -> in_macros found = 1) fives);
  let where file found =
    match found with
    | [ (f, (_, code)) ] when f = file || file = "" -> Some code
    | _ -> None
  in
  List.iter
    (fun code ->
      let planted file =
        count (fun found -> where file found = Some code) ones
      in
      Printf.printf "%s %d, in a use %d\n" code (planted "") (planted "main.lt"))
    [ "E0227"; "E0223"; "E0225"; "E0228"; "E0211"; "E0212" ];
  [%expect
    {|
    one: true, of five: true
    E0227 19, in a use 19
    E0223 28, in a use 28
    E0225 20, in a use 20
    E0228 17, in a use 0
    E0211 10, in a use 0
    E0212 14, in a use 0
    |}]
