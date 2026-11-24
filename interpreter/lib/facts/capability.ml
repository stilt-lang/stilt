(* The capabilities below [io] (facts.capabilities and facts.capability-natives). *)

open Ast

let all = [ Fs; Net; Clock; Env; Console; Rand; Spawn; Exec ]

let name = function
  | Fs -> "fs"
  | Net -> "net"
  | Clock -> "clock"
  | Env -> "env"
  | Console -> "console"
  | Rand -> "rand"
  | Spawn -> "spawn"
  | Exec -> "exec"

let of_name text = List.find_opt (fun c -> name c = text) all

let limit_name = function
  | Panic -> "panic"
  | Overflow -> "overflow"
  | Alloc -> "alloc"
  | Div -> "div"
  | Copy -> "copy"
  | Capability c -> name c
  | Locks -> "locks"
  | Unsafe -> "unsafe"

(* facts.capability-natives. [spawn] is [std.task]'s, which
   reaches it through [async] (tasks.implicit-effects-and-capabilities), and [exit] has no capability:
   it performs [io] without one (facts.io-and-capabilities). *)
let native ~home ~name =
  match (home, name) with
  | "std.prelude", ("print" | "eprint") -> Some Console
  | ( "std.io",
      ("read_line" | "poll_line" | "read_all" | "write" | "ewrite" | "flush") )
    ->
      Some Console
  | "std.fs", _ -> Some Fs
  | "std.clock", ("unix_ms" | "monotonic_ns" | "sleep_ms") -> Some Clock
  | "std.cli", ("args" | "env") -> Some Env
  | "std.random", "entropy" -> Some Rand
  | "std.task", "spawn" -> Some Spawn
  | "std.process", _ -> Some Exec
  | "std.net", _ -> Some Net
  | _ -> None
