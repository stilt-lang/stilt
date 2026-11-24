(* Tests of the limits on capabilities (facts.capabilities, facts.capability-natives and facts.without): each E0204
   names the capability and where the code gets it. Each test prints a
   program's errors with their messages. *)

open Stilt

let main text =
  match
    List.filter Diagnostic.is_error
      (Driver.check (Diagnostics.sources [ ("main.lt", text) ]))
  with
  | [] -> print_endline "ok"
  | errors -> List.iter (fun d -> print_endline (Diagnostic.to_string d)) errors

(* facts.capabilities, facts.capability-natives and facts.without *)
let%expect_test "a capability comes from a native or from what names one" =
  main
    "use std.clock\n\
     use std.fs\n\
     fn stamp(msg: str) -> str / io { \"{clock.unix_ms()} {msg}\" }\n\
     fn indirect(msg: str) -> str / io { stamp(msg) }\n\
     fn report(msg: str) / io without clock, fs {\n\
     print(indirect(msg))\n\
     if fs.exists(\"log.txt\") { print(\"logged\") }\n\
     }\n\
     fn main() / io {}";
  [%expect
    {|
    main.lt:6:7: E0204: this uses `indirect`, which has the capability `clock` through `stamp` at line 4, then `clock.unix_ms` at line 3, beyond `without clock`
    main.lt:7:4: E0204: this uses `fs.exists`, a native with the capability `fs`, beyond `without fs`
    |}]

(* facts.calls-through-function-values and facts.io-and-capabilities *)
let%expect_test "function values and exit add no capability" =
  main
    "use std.fs\n\
     fn each(f: fn() / io) / io without fs, console { f() }\n\
     fn stop() -> Never / io without fs, net, clock, env, console, rand, spawn \
     { exit(1) }\n\
     fn main() / io { each(|| { if fs.exists(\"x\") { print(\"x\") } }) }";
  [%expect {| ok |}]
