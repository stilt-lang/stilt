(* The native items of the standard library (program.prelude-functions). *)

open Tast
open Value
open Eval_state
open Eval_types
open Eval_targets
open Eval_traits
module T = Types

(* Native items that call no code of the program (program.prelude-functions) *)

let native_function t home name args =
  let str i =
    match args.(i) with
    | Str s -> s
    | _ -> invalid_arg "Eval_natives.native_function"
  in
  (* A failed operation raises [std.io.IoError] (std.io-errors). *)
  let io path = function Ok v -> v | Error e -> Eval_system.io_error path e in
  match (home, name) with
  | "std.prelude", "print" ->
      (* Each line reaches stdout when [print] returns (program.output-flushing). *)
      output_string t.out (str 0);
      output_char t.out '\n';
      flush t.out;
      unit
  | "std.prelude", "eprint" ->
      prerr_string (str 0);
      prerr_char '\n';
      flush stderr;
      unit
  | "std.prelude", "panic" ->
      Fault.panic "explicit" "%s" (Strings.quote (str 0))
  | "std.prelude", "unreachable" ->
      Fault.panic "unreachable" "reached unreachable()"
  | "std.prelude", "unwrap_failed" -> Fault.panic "unwrap" "%s" (str 0)
  | "std.prelude", "expect_failed" ->
      Fault.panic "unwrap" "%s" (Strings.quote (str 0))
  | "std.prelude", "exit" -> (
      match args.(0) with
      | Int code -> raise (Exited (Int64.to_int code))
      | _ -> invalid_arg "Eval_natives.native_function")
  | "std.io", "read_line" ->
      (* What the program wrote shows before it waits (std.io). *)
      flush t.out;
      option (Option.map (fun s -> Str s) (Files_stdin.read_line ()))
  | "std.cli", "args" ->
      List (Vec.of_list (List.map (fun a -> Str (Strings.repair a)) t.args))
  | "std.fs", "read" -> Str (io (str 0) (Files.read (str 0)))
  | "std.fs", "read_lines" ->
      let text = io (str 0) (Files.read (str 0)) in
      List (Vec.of_list (List.map (fun l -> Str l) (Strings.lines text)))
  | "std.fs", "write" ->
      io (str 0) (Files.write (str 0) (str 1));
      unit
  | _ -> Eval_system.native t home name args

let int_native (k : Ints.kind) name args =
  let int i =
    match args.(i) with
    | Int a -> a
    | _ -> invalid_arg "Eval_natives.int_native"
  in
  let after prefix =
    let n = String.length prefix in
    Option.get (Ints.of_name (String.sub name n (String.length name - n)))
  in
  let checked f = option (Option.map (fun r -> Int r) (f k (int 0) (int 1))) in
  let binary f = Int (f k (int 0) (int 1)) in
  let unary f = Int (f k (int 0)) in
  match name with
  | "abs" -> Int (if k.signed && int 0 < 0L then Ints.neg k (int 0) else int 0)
  | "checked_add" -> checked Ints_methods.checked_add
  | "checked_sub" -> checked Ints_methods.checked_sub
  | "checked_mul" -> checked Ints_methods.checked_mul
  | "saturating_add" -> binary Ints_methods.saturating_add
  | "saturating_sub" -> binary Ints_methods.saturating_sub
  | "pow" -> binary Ints_methods.pow
  | "div_euclid" -> binary Ints_methods.div_euclid
  | "rem_euclid" -> binary Ints_methods.rem_euclid
  | "count_ones" -> unary Ints_methods.count_ones
  | "leading_zeros" -> unary Ints_methods.leading_zeros
  | "trailing_zeros" -> unary Ints_methods.trailing_zeros
  | "gcd" -> binary Ints_methods.gcd
  | "lcm" -> binary Ints_methods.lcm
  | "min" -> Int (if Ints.compare k (int 0) (int 1) <= 0 then int 0 else int 1)
  | "max" -> Int (if Ints.compare k (int 0) (int 1) >= 0 then int 0 else int 1)
  | "to_f32" -> Float (Ints.to_f32 k (int 0))
  | "to_f64" -> Float (Ints.to_float k (int 0))
  | _ when String.starts_with ~prefix:"wrap_to_" name ->
      Int (Ints.wrap (after "wrap_to_") (int 0))
  | _ when String.starts_with ~prefix:"to_" name ->
      (* A conversion that may lose the value gives an [Option] (numbers.conversions). *)
      let into = after "to_" in
      if Ints.lossless ~from:k into then Int (int 0)
      else if Ints.fits ~from:k into (int 0) then some (Int (int 0))
      else none
  | _ -> invalid_arg ("Eval_natives.int_native: " ^ name)

let float_native f32 name args =
  let float i =
    match args.(i) with
    | Float x -> x
    | _ -> invalid_arg "Eval_natives.float_native"
  in
  let rounded x = Float (Floats.result ~f32 x) in
  match name with
  | "sqrt" -> rounded (Float.sqrt (float 0))
  | "floor" -> rounded (Float.floor (float 0))
  | "ceil" -> rounded (Float.ceil (float 0))
  | "trunc" -> rounded (Float.trunc (float 0))
  | "round" -> rounded (Float.round (float 0))
  | "abs" -> rounded (Float.abs (float 0))
  | "min" -> rounded (Floats.minimum (float 0) (float 1))
  | "max" -> rounded (Floats.maximum (float 0) (float 1))
  | "is_nan" -> Bool (Float.is_nan (float 0))
  | "to_f32" -> Float (Floats.round32 (float 0))
  | "to_f64" -> Float (float 0)
  | _ when String.starts_with ~prefix:"to_" name ->
      let into =
        Option.get (Ints.of_name (String.sub name 3 (String.length name - 3)))
      in
      option (Option.map (fun a -> Int a) (Floats.to_int into (float 0)))
  | _ -> invalid_arg ("Eval_natives.float_native: " ^ name)

let str_join s parts =
  let part = function Str p -> p | _ -> invalid_arg "Eval_natives.str_join" in
  match parts with
  | List parts ->
      let parts = List.map part (Vec.to_list parts) in
      reserve
        (List.fold_left
           (fun n p -> n + String.length p + String.length s)
           0 parts);
      Str (String.concat s parts)
  | _ -> invalid_arg "Eval_natives.str_join"

(* The methods of [str] that std.str and std.code-points adds. *)
let str_method name s args =
  let str i =
    match args.(i) with
    | Str s -> s
    | _ -> invalid_arg "Eval_natives.str_method"
  in
  let int i =
    match args.(i) with
    | Int a -> Int64.to_int a
    | _ -> invalid_arg "Eval_natives.str_method"
  in
  let pair (a, b) = Tuple [ Str a; Str b ] in
  let elements n = reserve (n * 10 * (Sys.word_size / 8)) in
  let module M = Strings_methods in
  match name with
  | "trim_start" -> Str (M.drop_while_start s)
  | "trim_end" -> Str (M.drop_while_end s)
  | "strip_prefix" ->
      option (Option.map (fun r -> Str r) (M.strip_prefix s (str 1)))
  | "strip_suffix" ->
      option (Option.map (fun r -> Str r) (M.strip_suffix s (str 1)))
  | "split_once" -> option (Option.map pair (M.split_once s (str 1)))
  | "rsplit_once" -> option (Option.map pair (M.rsplit_once s (str 1)))
  | "rfind" ->
      option (Option.map (fun i -> Int (Int64.of_int i)) (M.rfind s (str 1)))
  | "count" -> Int (Int64.of_int (M.count s (str 1)))
  | "replace_first" -> Str (M.replace_first s (str 1) (str 2))
  | "split_whitespace" ->
      elements (String.length s);
      List (Vec.of_list (List.map (fun p -> Str p) (M.split_whitespace s)))
  | "pad_start" | "pad_end" ->
      (* The padding holds at most four bytes per scalar value. *)
      reserve (4 * max 0 (int 1 - M.char_count s));
      let pad = if name = "pad_start" then M.pad_start else M.pad_end in
      Str (pad s (int 1) (str 2))
  | "char_count" -> Int (Int64.of_int (M.char_count s))
  | "reversed" -> Str (M.reverse s)
  | "is_ascii" -> Bool (M.is_ascii s)
  | "code_points" ->
      elements (String.length s);
      List
        (Vec.of_list
           (List.map (fun c -> Int (Int64.of_int c)) (M.code_points s)))
  | _ -> (
      match M.classify name with
      | Some test -> Bool (M.classified test s)
      | None -> invalid_arg ("Eval_natives.str_method: " ^ name))

(* The associated functions of [str] that std.str-building and std.code-points adds, which build a
   string from code points or bytes. *)
let str_function name args =
  let ints () =
    match args.(0) with
    | List xs ->
        List.map
          (function
            | Int a -> Int64.to_int a
            | _ -> invalid_arg "Eval_natives.str_function")
          (Vec.to_list xs)
    | _ -> invalid_arg "Eval_natives.str_function"
  in
  let str s = Str s in
  match (name, args.(0)) with
  | "from_code_point", Int c ->
      option (Option.map str (Strings_methods.from_code_point (Int64.to_int c)))
  | "from_utf8", _ ->
      option (Option.map str (Strings_methods.from_utf8 (ints ())))
  | "from_utf8_lossy", _ -> Str (Strings_methods.from_utf8_lossy (ints ()))
  | _ -> invalid_arg ("Eval_natives.str_function: " ^ name)

let str_native name args =
  let str i =
    match args.(i) with
    | Str s -> s
    | _ -> invalid_arg "Eval_natives.str_native"
  in
  let int i =
    match args.(i) with
    | Int a -> a
    | _ -> invalid_arg "Eval_natives.str_native"
  in
  let strings xs = List (Vec.of_list (List.map (fun x -> Str x) xs)) in
  let s = str 0 in
  (* A list holds each element in some ten words: a node, a box and the
     element's own block. *)
  let elements n = reserve (n * 10 * (Sys.word_size / 8)) in
  match name with
  | "len" -> Int (Int64.of_int (String.length s))
  | "is_empty" -> Bool (s = "")
  | "contains" -> Bool (Option.is_some (Strings.find s (str 1)))
  | "starts_with" -> Bool (String.starts_with ~prefix:(str 1) s)
  | "ends_with" -> Bool (String.ends_with ~suffix:(str 1) s)
  | "find" ->
      option
        (Option.map (fun i -> Int (Int64.of_int i)) (Strings.find s (str 1)))
  | "slice" -> Eval_views.slice (Str s) (int 1) (int 2)
  | "split" ->
      elements (String.length s + 1);
      strings (Strings.split s (str 1))
  | "lines" ->
      elements (String.length s);
      strings (Strings.lines s)
  | "trim" -> Str (Strings.trim s)
  | "replace" ->
      let from = str 1 and into = str 2 in
      (* At most one match per byte, or per boundary for an empty [from]. *)
      let matches = (String.length s / max 1 (String.length from)) + 1 in
      reserve (String.length s + (matches * String.length into));
      Str (Strings.replace s from into)
  | "chars" ->
      elements (String.length s);
      strings (Strings.chars s)
  | "bytes" ->
      elements (String.length s);
      let byte c = Int (Int64.of_int (Char.code c)) in
      List (Vec.of_list (List.map byte (List.of_seq (String.to_seq s))))
  | "ascii_upper" -> Str (String.uppercase_ascii s)
  | "ascii_lower" -> Str (String.lowercase_ascii s)
  | "join" -> str_join s args.(1)
  | _ when String.starts_with ~prefix:"to_" name -> (
      let into = String.sub name 3 (String.length name - 3) in
      match Ints.of_name into with
      | Some k -> option (Option.map (fun a -> Int a) (Ints.parse k s))
      | None ->
          option
            (Option.map (fun x -> Float x) (Floats.parse ~f32:(into = "f32") s))
      )
  | _ -> str_method name s args

(* Native items, which call the program's code through callbacks and the
   impls of map keys. *)

(* [sorted_by] and [sorted_desc_by]: the key of each element, in order, then a
   stable sort (std.list-sorting). *)
let sorted_by t fr loc name targs xs key =
  let kty = List.nth targs 1 in
  let key =
    match key with
    | Fn f -> target_of_fn t f
    | _ -> invalid_arg "Eval_natives.sorted_by"
  in
  let keyed =
    List.map (fun x -> (t.apply t fr loc key [| x |], x)) (Vec.to_list xs)
  in
  let ascending (a, _) (b, _) = order t fr loc kty a b in
  let by = if name = "sorted_by" then ascending else fun a b -> ascending b a in
  List (Vec.of_list (List.map snd (List.stable_sort by keyed)))

let list_native t fr loc name targs args =
  let list () =
    match args.(0) with
    | List xs -> xs
    | _ -> invalid_arg "Eval_natives.list_native"
  in
  let int i =
    match args.(i) with
    | Int a -> a
    | _ -> invalid_arg "Eval_natives.list_native"
  in
  let length () = Int64.of_int (Vec.length (list ())) in
  let within ok i =
    if not ok then
      Fault.panic "bounds" "index %Ld is out of bounds for a list of length %Ld"
        i (length ())
  in
  match name with
  | "new" -> List Vec.empty
  | "len" -> Int (length ())
  | "is_empty" -> Bool (length () = 0L)
  | "get" ->
      let i = int 1 in
      if 0L <= i && i < length () then some (Vec.get (list ()) (Int64.to_int i))
      else none
  | "push" ->
      args.(0) <- List (Vec.push (list ()) args.(1));
      unit
  | "pop" -> (
      match Vec.pop (list ()) with
      | Some (rest, x) ->
          args.(0) <- List rest;
          some x
      | None -> none)
  | "insert" ->
      let i = int 1 in
      within (0L <= i && i <= length ()) i;
      args.(0) <- List (Vec.insert (list ()) (Int64.to_int i) args.(2));
      unit
  | "remove" ->
      let i = int 1 in
      within (0L <= i && i < length ()) i;
      let xs = list () in
      args.(0) <- List (Vec.remove xs (Int64.to_int i));
      Vec.get xs (Int64.to_int i)
  | "slice" -> Eval_views.slice args.(0) (int 1) (int 2)
  | "sorted_by" | "sorted_desc_by" ->
      sorted_by t fr loc name targs (list ()) args.(1)
  | _ -> invalid_arg ("Eval_natives.list_native: " ^ name)

let map_native t fr loc name targs args =
  let map () =
    match args.(0) with
    | Map d -> d
    | _ -> invalid_arg "Eval_natives.map_native"
  in
  let kty = List.hd targs in
  match name with
  | "new" -> Map (Dict.empty None)
  | "with_default" -> Map (Dict.empty (Some args.(0)))
  | "len" -> Int (Int64.of_int (Dict.length (map ())))
  | "is_empty" -> Bool (Dict.length (map ()) = 0)
  | "contains" -> Bool (Option.is_some (lookup t fr loc kty (map ()) args.(1)))
  | "get" -> option (Option.map snd (lookup t fr loc kty (map ()) args.(1)))
  | "insert" ->
      args.(0) <- Map (insert t fr loc kty (map ()) args.(1) args.(2));
      unit
  | "remove" -> (
      let d = map () in
      let hash = hash t fr loc kty args.(1) in
      let same other = equal t fr loc kty args.(1) other in
      match Dict.find d ~hash ~same with
      | Some (stamp, v) ->
          args.(0) <- Map (Dict.remove d ~hash stamp);
          some v
      | None -> none)
  | _ -> invalid_arg ("Eval_natives.map_native: " ^ name)

(* polymorphism.lazy-values: [Lazy.new] keeps its function, and [get] runs it the first
   time any copy of the value asks, and keeps what it returns; a [when] that
   runs meanwhile panics. *)
let lazy_native t fr loc name args =
  match (name, args.(0)) with
  | "new", Fn compute -> Deferred { compute; result = None }
  | "get", Deferred { result = Some v; _ } -> v
  | "get", Deferred d ->
      let v =
        Eval_when.computing_lazy (fun () ->
            t.apply t fr loc (target_of_fn t d.compute) [||])
      in
      d.result <- Some v;
      v
  | _ -> invalid_arg ("Eval_natives.lazy_native: " ^ name)

(* tasks.sequential-run and tasks.task-functions: a task runs to its end where it starts, as the
   sequential run that is a program's meaning runs it, under either handler;
   its handle holds its value. *)
let task_item = { Hir.home = "std.task"; name = "Task" }

let task_native t fr loc name args =
  match (name, args) with
  | "spawn", [| Fn f |] ->
      let v = t.apply t fr loc (target_of_fn t f) [||] in
      Variant (task_item, [ v ])
  | "await", [| Variant (_, [ v ]) |] -> v
  | ("threads" | "sequential"), [||] ->
      Handler { heffect = T.async_effect; control = false; ops = [] }
  | _ -> invalid_arg ("Eval_natives.task_native: " ^ name)

let native t fr loc (callee : callee) targs args =
  match callee with
  | Function { home = "std.task"; name = "scope" as name }
  | Member ({ home = "std.task"; name = "Scope" }, name) ->
      Eval_parallel.scope_native t fr loc name args
  | Function { home = "std.par"; name } ->
      Eval_parallel.par_native t fr loc name args
  | Member ({ home = "std.sync"; _ }, name) ->
      Eval_parallel.sync_native name args
  | Function { home = "std.task"; name }
  | Member ({ home = "std.task"; _ }, name) ->
      task_native t fr loc name args
  | Function { home = "std.view"; _ } | Member ({ home = "std.view"; _ }, _) ->
      Eval_views.native t fr loc callee targs args
  | Member ({ home = "std.lazy"; _ }, name) -> lazy_native t fr loc name args
  (* macros.tokens-and-code and macros.cursor *)
  | Member ({ home = "std.meta"; name = owner }, name)
    when List.mem owner Eval_macro_natives.owners ->
      Eval_macro_natives.method_ fr loc owner name args
  | Function { home = "std.meta"; name } ->
      Eval_macro_natives.function_ loc name args
  | Member ({ home = "std.meta"; name = owner }, name) ->
      Eval_meta_natives.native t fr loc owner name targs args
  | Function { home = "std.array"; name }
  | Member ({ home = "std.array"; _ }, name) ->
      Eval_arrays.native t fr loc name targs args
  | Function { home = "std.c"; _ } | Member ({ home = "std.c"; _ }, _) ->
      Eval_foreign.native t callee targs args
  | Function item when Env.is_foreign t.env item ->
      Eval_foreign.native t callee targs args
  | Function { home = "std.process"; name } -> Eval_process.native t name args
  | Function { home = "std.net"; name } -> Eval_net.native name args
  | Function { home; name } -> native_function t home name args
  | Member (owner, name) -> (
      match (numeric (T.Con (owner, [])), owner.name) with
      | Integer k, _ -> int_native k name args
      | Floating f32, _ -> float_native f32 name args
      | Not_numeric, "str"
        when List.mem name [ "from_code_point"; "from_utf8"; "from_utf8_lossy" ]
        ->
          str_function name args
      | Not_numeric, ("str" | "List") when List.mem name Eval_foreign.lends ->
          Eval_foreign.lend t fr loc name targs args
      | Not_numeric, "str" -> str_native name args
      | Not_numeric, "List" -> list_native t fr loc name targs args
      | Not_numeric, "Map" -> map_native t fr loc name targs args
      | Not_numeric, _ -> invalid_arg ("Eval_natives.native: " ^ owner.name))
  | Trait_method _ | Operation _ -> invalid_arg "Eval_natives.native"
