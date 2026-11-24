(* Tests of the effects and handlers (handlers.declaring-effect and
   handlers.with) that csmith programs use: how many programs use them, and
   which forms the programs that do write. That the reference interpreter
   accepts the programs is what `just generated` checks, and that the compiler
   runs them as it does is what `just differential` checks. *)

open Stilt_gen

let seeds n = List.init n succ
let lines text = String.split_on_char '\n' text

let contains text part =
  let n = String.length part in
  let rec go i =
    i + n <= String.length text && (String.sub text i n = part || go (i + 1))
  in
  go 0

(* Three programs in ten use effects, and half of those may install handlers
   inside a [when], which names [std.sync]. *)
let%expect_test "wanted" =
  let using = List.filter Csmith_effects.wanted (seeds 1000) in
  let sharing = List.filter Csmith_effects.shares (seeds 1000) in
  let names_sync seed =
    List.mem "use std.sync" (lines (Csmith.program ~macros:false seed))
  in
  Printf.printf "%d use effects, %d share, naming std.sync: %b\n"
    (List.length using) (List.length sharing)
    (List.for_all names_sync sharing);
  [%expect {| 319 use effects, 146 share, naming std.sync: true |}]

(* The first 200 programs that use effects. *)
let sample =
  lazy
    (List.filter Csmith_effects.wanted (seeds 1000)
    |> List.filteri (fun i _ -> i < 200)
    |> List.map (fun seed -> Csmith.program ~macros:false seed))

(* How many of the sample's programs write each form, in one of their lines. *)
let%expect_test "forms" =
  let programs = List.map lines (Lazy.force sample) in
  let has part line = contains line part in
  let both p q line = p line && q line in
  (* The part of [line] after the first [part], if it holds one. *)
  let after part line =
    let n = String.length part in
    let rec go i =
      if i + n > String.length line then ""
      else if String.sub line i n = part then
        String.sub line (i + n) (String.length line - i - n)
      else go (i + 1)
    in
    go 0
  in
  List.iter
    (fun (name, holds) ->
      Printf.printf "%s %d\n" name
        (List.length (List.filter (List.exists holds) programs)))
    [
      ("an effect", has "effect Ef");
      ("an operation of two parameters or more", both (has "fn eo") (has ", ea"));
      ( "a function that performs two effects",
        fun l -> contains (after "/ {io, Ef" l) ", Ef" );
      ("an inout parameter", has "inout ep");
      ( "a handler that answers",
        both (has "= handler Ef") (fun l -> not (contains l " -> ")) );
      ("a handler that takes control", both (has "= handler Ef") (has " -> "));
      ("a resume", has "resume(");
      ("a performance in a closure", has ".map(|ex");
      ("a performance on the outer handler", has " outer eo");
      ("two handlers in one with", both (has "= with eh") (has ", eh"));
      ("a with in a loop", has "for en");
      ("a with in a when", has "when es");
      ( "a break or a continue",
        fun l -> has "{ break }" l || has "{ continue }" l );
    ];
  [%expect
    {|
    an effect 200
    an operation of two parameters or more 182
    a function that performs two effects 105
    an inout parameter 131
    a handler that answers 151
    a handler that takes control 182
    a resume 173
    a performance in a closure 145
    a performance on the outer handler 103
    two handlers in one with 111
    a with in a loop 136
    a with in a when 46
    a break or a continue 182
    |}]
