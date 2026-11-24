(* Other programs (std.process-starting, std.process-runs and std.children): a
   command's program looked up in its PATH, its environment and directory, and
   its runs, to their end with their streams captured or inherited, or beside
   the program with their standard input and output piped. *)

type failure = Failed of Files.error * string

(* A child's standard output: the channel it is read from while it is open,
   then what [keep] read of it ahead, from [at]. *)
type output = {
  mutable chan : in_channel option;
  mutable kept : string;
  mutable at : int;
}

type child = {
  program : string;
  pid : int;
  mutable input : out_channel option;
  output : output;
  mutable status : int option;
  mutable captured : string * string;
}

let children : (int64, child) Hashtbl.t = Hashtbl.create 8
let count = ref 0L

let rec restarting f =
  try f () with Unix.Unix_error (Unix.EINTR, _, _) -> restarting f

(* Runs [f], in which a write to a child that has closed its input fails with
   EPIPE rather than ending the program, while no child that it starts
   inherits the signal ignored. *)
let without_broken_pipes f =
  let before = Sys.signal Sys.sigpipe Sys.Signal_ignore in
  Fun.protect ~finally:(fun () -> Sys.set_signal Sys.sigpipe before) f

(* The environment that a command's changes make of the program's own: [set]
   holds names and values in pairs. A name that is empty or holds [=] or NUL,
   and a value that holds NUL, can't be set. *)
let environment set removed =
  let valid name =
    name <> ""
    && (not (String.contains name '='))
    && not (String.contains name '\000')
  in
  let rec pairs = function
    | name :: value :: rest -> (name, value) :: pairs rest
    | _ -> []
  in
  let set = pairs set in
  if
    List.exists (fun (n, v) -> (not (valid n)) || String.contains v '\000') set
    || not (List.for_all valid removed)
  then None
  else
    let changed = List.map fst set @ removed in
    let kept =
      List.filter
        (fun entry ->
          match String.index_opt entry '=' with
          | Some i -> not (List.mem (String.sub entry 0 i) changed)
          | None -> true)
        (Array.to_list (Unix.environment ()))
    in
    Some (Array.of_list (kept @ List.map (fun (n, v) -> n ^ "=" ^ v) set))

let executable path =
  match Unix.stat path with
  | { st_kind = S_REG; _ } -> (
      match Unix.access path [ X_OK ] with
      | () -> `Yes
      | exception Unix.Unix_error _ -> `Denied)
  | _ -> `No
  | exception Unix.Unix_error _ -> `No

(* The file that runs [program]: a path when it holds a [/], relative to the
   program's working directory, and otherwise the first executable file of
   that name in the directories of the [PATH] of [env]. *)
let resolve env program =
  if String.contains program '/' then
    let path =
      if Filename.is_relative program then
        Filename.concat (Sys.getcwd ()) program
      else program
    in
    match executable path with
    | `Yes -> Ok path
    | `Denied -> Error (Failed (Denied, program))
    | `No -> Error (Failed (Missing, program))
  else
    let path =
      Array.fold_left
        (fun found entry ->
          match String.split_on_char '=' entry with
          | "PATH" :: _ -> String.sub entry 5 (String.length entry - 5)
          | _ -> found)
        "" env
    in
    let dirs = List.filter (( <> ) "") (String.split_on_char ':' path) in
    let rec look denied = function
      | [] -> Error (Failed ((if denied then Denied else Missing), program))
      | dir :: rest -> (
          let file = Filename.concat dir program in
          match executable file with
          | `Yes -> Ok file
          | `Denied -> look true rest
          | `No -> look denied rest)
    in
    if program = "" then Error (Failed (Missing, program)) else look false dirs

let status_of = function
  | Unix.WEXITED code -> code
  | Unix.WSIGNALED s | Unix.WSTOPPED s -> -Sys.signal_to_int s

let await pid = snd (restarting (fun () -> Unix.waitpid [] pid))

(* Spawns [file] as [program] with [args], in [dir], whose standard streams
   are the three descriptors given. *)
let spawn ~program ~file ~args ~env ~dir (stdin, stdout, stderr) =
  let argv = Array.of_list (program :: args) in
  let here = Sys.getcwd () in
  Fun.protect ~finally:(fun () -> if dir <> "" then Unix.chdir here)
  @@ fun () ->
  if dir <> "" then Unix.chdir dir;
  Unix.create_process_env file argv env stdin stdout stderr

(* The input written to a run and its two outputs read, at the same time, so
   that neither waits for the other. *)
let communicate input (w, out_r, err_r) =
  let out = Buffer.create 4096 and err = Buffer.create 256 in
  let chunk = Bytes.create 65536 in
  let buffer fd = if fd = out_r then out else err in
  let rec go writing pos reading =
    let writing =
      match writing with
      | Some fd when pos >= String.length input ->
          Unix.close fd;
          None
      | w -> w
    in
    if writing <> None || reading <> [] then begin
      let ws = Option.to_list writing in
      let readable, writable, _ =
        restarting (fun () -> Unix.select reading ws [] (-1.0))
      in
      let writing, pos =
        match writable with
        | fd :: _ -> (
            match
              Unix.single_write_substring fd input pos
                (String.length input - pos)
            with
            | n -> (writing, pos + n)
            | exception Unix.Unix_error ((EAGAIN | EINTR), _, _) ->
                (writing, pos)
            | exception Unix.Unix_error _ ->
                Unix.close fd;
                (None, pos))
        | [] -> (writing, pos)
      in
      let closed =
        List.filter
          (fun fd ->
            match restarting (fun () -> Unix.read fd chunk 0 65536) with
            | 0 -> true
            | n ->
                Buffer.add_subbytes (buffer fd) chunk 0 n;
                false
            | exception Unix.Unix_error _ -> true)
          readable
      in
      List.iter Unix.close closed;
      go writing pos (List.filter (fun fd -> not (List.mem fd closed)) reading)
    end
  in
  Unix.set_nonblock w;
  without_broken_pipes (fun () -> go (Some w) 0 [ out_r; err_r ]);
  (Strings.repair (Buffer.contents out), Strings.repair (Buffer.contents err))

let pipe () = Unix.pipe ~cloexec:true ()

let register child =
  count := Int64.add !count 1L;
  Hashtbl.replace children !count child;
  !count

let ended program status captured =
  let output = { chan = None; kept = ""; at = 0 } in
  register
    { program; pid = -1; input = None; output; status = Some status; captured }

(* Runs a command in [mode], once its program, environment and directory are
   found, as std.process-runs and std.children say. *)
let run ~mode ~input ~program ~file ~args ~env ~dir =
  let go = spawn ~program ~file ~args ~env ~dir in
  match mode with
  | 0 ->
      let in_r, in_w = pipe ()
      and out_r, out_w = pipe ()
      and err_r, err_w = pipe () in
      let pid =
        Fun.protect
          ~finally:(fun () -> List.iter Unix.close [ in_r; out_w; err_w ])
          (fun () -> go (in_r, out_w, err_w))
      in
      let captured = communicate input (in_w, out_r, err_r) in
      ended program (status_of (await pid)) captured
  | 1 ->
      ended program
        (status_of (await (go (Unix.stdin, Unix.stdout, Unix.stderr))))
        ("", "")
  | _ ->
      let in_r, in_w = pipe () and out_r, out_w = pipe () in
      let pid =
        Fun.protect
          ~finally:(fun () -> List.iter Unix.close [ in_r; out_w ])
          (fun () -> go (in_r, out_w, Unix.stderr))
      in
      let output =
        { chan = Some (Unix.in_channel_of_descr out_r); kept = ""; at = 0 }
      in
      register
        {
          program;
          pid;
          input = Some (Unix.out_channel_of_descr in_w);
          output;
          status = None;
          captured = ("", "");
        }

let start ~program ~args ~set ~removed ~dir ~mode ~input =
  let invalid =
    List.exists (fun a -> String.contains a '\000') (program :: dir :: args)
  in
  match environment set removed with
  | _ when invalid -> Error (Failed (Other, program))
  | None -> Error (Failed (Other, program))
  | Some env -> (
      if dir <> "" && not (Sys.file_exists dir && Sys.is_directory dir) then
        Error (Failed (Missing, dir))
      else
        match resolve env program with
        | Error e -> Error e
        | Ok file -> (
            try Ok (run ~mode ~input ~program ~file ~args ~env ~dir)
            with Unix.Unix_error (e, _, _) ->
              Error (Failed (Files.error_of e, program))))

(* A child's streams (std.children) *)

let failed c = Error (Failed (Other, c.program))

let write c text =
  match c.input with
  | None -> failed c
  | Some oc -> (
      try
        without_broken_pipes (fun () ->
            output_string oc text;
            flush oc);
        Ok ()
      with Sys_error _ -> failed c)

let close_input c =
  without_broken_pipes (fun () -> Option.iter close_out_noerr c.input);
  c.input <- None

(* A line without the [\r] that ends it, as [io.read_line] gives one. *)
let line text =
  let n = String.length text in
  let text =
    if n > 0 && text.[n - 1] = '\r' then String.sub text 0 (n - 1) else text
  in
  Strings.repair text

let close_output o =
  Option.iter close_in_noerr o.chan;
  o.chan <- None

let read_line c =
  let o = c.output in
  match o.chan with
  | Some ic -> (
      match In_channel.input_line ic with
      | Some l -> Some (line l)
      | None | (exception Sys_error _) ->
          close_output o;
          None)
  | None when o.at >= String.length o.kept -> None
  | None ->
      let stop =
        Option.value ~default:(String.length o.kept)
          (String.index_from_opt o.kept o.at '\n')
      in
      let l = String.sub o.kept o.at (stop - o.at) in
      o.at <- min (String.length o.kept) (stop + 1);
      Some (line l)

(* The rest of a child's output, which [read_all] gives and [wait] keeps. *)
let take o =
  let text =
    match o.chan with
    | Some ic -> ( try In_channel.input_all ic with Sys_error _ -> "")
    | None -> String.sub o.kept o.at (String.length o.kept - o.at)
  in
  close_output o;
  o.kept <- "";
  o.at <- 0;
  text

let read_all c = Strings.repair (take c.output)

let wait c =
  match c.status with
  | Some s -> s
  | None ->
      close_input c;
      c.output.kept <- take c.output;
      let s = status_of (await c.pid) in
      c.status <- Some s;
      s

let kill c =
  if c.status = None then
    try Unix.kill c.pid Sys.sigkill with Unix.Unix_error _ -> ()
