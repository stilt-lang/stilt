(* The native functions of [std.io], [std.fs], [std.cli], [std.clock],
   [std.math] and [std.random] that std.math, std.io and std.fs add. *)

open Value
open Eval_state

let str (args : value array) i =
  match args.(i) with Str s -> s | _ -> invalid_arg "Eval_system.str"

let float (args : value array) i =
  match args.(i) with Float x -> x | _ -> invalid_arg "Eval_system.float"

let int (args : value array) i =
  match args.(i) with Int a -> a | _ -> invalid_arg "Eval_system.int"

(* A failed operation raises [std.io.IoError] with [path] (std.io-errors). *)
let io_error path (error : Files.error) =
  let name =
    match error with
    | Missing -> "NotFound"
    | Denied -> "PermissionDenied"
    | Invalid_utf8 -> "InvalidUtf8"
    | Other -> "Other"
  in
  raise (Raised (Variant ({ home = "std.io"; name }, [ Str path ])))

let io path = function Ok v -> v | Error e -> io_error path e

(* A list holds each element in some ten words: a node, a box and the
   element's own block. *)
let bytes_value text =
  reserve (String.length text * 10 * (Sys.word_size / 8));
  List
    (Vec.of_list
       (List.init (String.length text) (fun i ->
            Int (Int64.of_int (Char.code text.[i])))))

let bytes_of = function
  | List xs ->
      String.of_seq
        (Seq.map
           (function
             | Int b -> Char.chr (Int64.to_int b)
             | _ -> invalid_arg "Eval_system.bytes_of")
           (List.to_seq (Vec.to_list xs)))
  | _ -> invalid_arg "Eval_system.bytes_of"

let fs name args =
  let path = str args 0 in
  match name with
  | "append" ->
      io path (Files.append path (str args 1));
      unit
  | "read_bytes" -> bytes_value (io path (Files.read_bytes path))
  | "write_bytes" ->
      io path (Files.write path (bytes_of args.(1)));
      unit
  | "exists" -> Bool (Files_dirs.exists path)
  | "is_file" -> Bool (Files_dirs.is_file path)
  | "is_dir" -> Bool (Files_dirs.is_dir path)
  | "list_dir" ->
      List
        (Vec.of_list
           (List.map (fun n -> Str n) (io path (Files_dirs.list_dir path))))
  | "create_dir" ->
      io path (Files_dirs.create_dir path);
      unit
  | "remove" ->
      io path (Files_dirs.remove path);
      unit
  | "remove_all" ->
      io path (Files_dirs.remove_all path);
      unit
  | "rename" -> (
      match Files_dirs.rename path (str args 1) with
      | Ok () -> unit
      | Error (e, at) -> io_error at e)
  | _ -> invalid_arg ("Eval_system.fs: " ^ name)

(* The process's start, after which [monotonic_ns] counts, and the latest value
   it gave, which it never goes below. *)
let latest = ref 0L

let clock name args =
  match name with
  | "unix_ms" ->
      Int (Int64.of_float (Float.floor (Unix.gettimeofday () *. 1000.)))
  | "monotonic_ns" ->
      let now = Int64.of_float (Unix.gettimeofday () *. 1e9) in
      latest := Int64.max !latest now;
      Int !latest
  | "sleep_ms" ->
      let ms = int args 0 in
      if ms > 0L then Unix.sleepf (Int64.to_float ms /. 1000.);
      unit
  | _ -> invalid_arg ("Eval_system.clock: " ^ name)

(* std.math-special-values: [pow] is [1.0] when [y] is [0.0] or [x] is [1.0], NaN included,
   and C's [pow] gives [1.0] for [-1.0] to an infinite power. They are written here so that a
   host whose own [pow] differs, as JavaScript's [**] does, gives the same values. *)
let pow x y =
  if y = 0.0 || x = 1.0 then 1.0
  else if x = -1.0 && Float.abs y = Float.infinity then 1.0
  else Float.pow x y

let math name args =
  let unary f = Float (f (float args 0)) in
  let binary f = Float (f (float args 0) (float args 1)) in
  match name with
  | "pow" -> binary pow
  | "exp" -> unary Float.exp
  | "log" -> unary Float.log
  | "log2" -> unary Float.log2
  | "log10" -> unary Float.log10
  | "sin" -> unary Float.sin
  | "cos" -> unary Float.cos
  | "tan" -> unary Float.tan
  | "asin" -> unary Float.asin
  | "acos" -> unary Float.acos
  | "atan" -> unary Float.atan
  | "atan2" -> binary Float.atan2
  | "sinh" -> unary Float.sinh
  | "cosh" -> unary Float.cosh
  | "tanh" -> unary Float.tanh
  | "cbrt" -> unary Float.cbrt
  | "hypot" -> binary Float.hypot
  | _ -> invalid_arg ("Eval_system.math: " ^ name)

(* Eight bytes from the system's source of randomness, or the clock where it
   has none. *)
let entropy () =
  match
    In_channel.with_open_bin "/dev/urandom" (fun c ->
        In_channel.really_input_string c 8)
  with
  | Some s -> String.get_int64_le s 0
  | None | (exception Sys_error _) ->
      Int64.of_float (Unix.gettimeofday () *. 1e9)

(* The value of an environment variable whose name could be set. *)
let env name =
  if name = "" || String.contains name '=' || String.contains name '\000' then
    None
  else Option.map Strings.repair (Sys.getenv_opt name)

(* program.output-flushing: what [io.write] writes reaches the stream with each
   newline, so a line shows as soon as it is written, and the text after the
   last newline waits for the next one. *)
let write out text =
  match String.rindex_opt text '\n' with
  | None -> output_string out text
  | Some i ->
      output_substring out text 0 (i + 1);
      flush out;
      output_substring out text (i + 1) (String.length text - i - 1)

let native t home name args =
  match (home, name) with
  | "std.io", "write" ->
      write t.out (str args 0);
      unit
  | "std.io", "ewrite" ->
      prerr_string (str args 0);
      flush stderr;
      unit
  | "std.io", "flush" ->
      flush t.out;
      unit
  (* What the program wrote shows before it reads (std.io). *)
  | "std.io", "read_all" ->
      flush t.out;
      Str (Files_stdin.read_all ())
  | "std.io", "poll_line" ->
      flush t.out;
      option (Option.map (fun s -> Str s) (Files_stdin.poll_line ()))
  | "std.fs", _ -> fs name args
  | "std.cli", "env" -> option (Option.map (fun v -> Str v) (env (str args 0)))
  | "std.clock", _ -> clock name args
  | "std.math", _ -> math name args
  | "std.random", "entropy" -> Int (entropy ())
  | _ -> invalid_arg ("Eval_system.native: " ^ home ^ "." ^ name)
