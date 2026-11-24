(* The natives of [std.process] (std.process-starting, std.process-runs and
   std.children), on {!Files_process}. A command that can't start, and a write
   to a child that fails, raise [std.io.IoError] (std.io-errors). *)

open Value
module P = Files_process

let strings = function
  | List xs ->
      List.map
        (function Str s -> s | _ -> invalid_arg "Eval_process.strings")
        (Vec.to_list xs)
  | _ -> invalid_arg "Eval_process.strings"

let raised (P.Failed (e, at)) = Eval_system.io_error at e

let child (args : value array) =
  match args.(0) with
  | Int id -> Hashtbl.find P.children id
  | _ -> invalid_arg "Eval_process.child"

let start (t : Eval_state.t) (args : value array) =
  let str i =
    match args.(i) with Str s -> s | _ -> invalid_arg "Eval_process.start"
  in
  let mode =
    match args.(5) with
    | Int m -> Int64.to_int m
    | _ -> invalid_arg "Eval_process.start"
  in
  (* What the program wrote shows before what a program that shares its
     streams writes (std.process-runs). *)
  if mode > 0 then begin
    flush t.out;
    flush stderr
  end;
  match
    P.start ~program:(str 0)
      ~args:(strings args.(1))
      ~set:(strings args.(2))
      ~removed:(strings args.(3))
      ~dir:(str 4) ~mode ~input:(str 6)
  with
  | Ok id -> Int id
  | Error e -> raised e

let native t name args =
  let int n = Int (Int64.of_int n) in
  match name with
  | "start" -> start t args
  | "waited" -> int (P.wait (child args))
  | "captured" -> (
      let out, err = (child args).captured in
      match args.(1) with Int 1L -> Str out | _ -> Str err)
  | "write_input" -> (
      match args.(1) with
      | Str text -> (
          match P.write (child args) text with
          | Ok () -> unit
          | Error e -> raised e)
      | _ -> invalid_arg "Eval_process.native")
  | "close" ->
      P.close_input (child args);
      unit
  | "next_line" ->
      option (Option.map (fun l -> Str l) (P.read_line (child args)))
  | "rest" -> Str (P.read_all (child args))
  | "stop" ->
      P.kill (child args);
      unit
  | _ -> invalid_arg ("Eval_process.native: " ^ name)
