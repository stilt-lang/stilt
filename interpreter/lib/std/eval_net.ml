(* The natives of [std.net] (std.net, std.net-streams, std.net-listeners and
   std.net-datagrams),
   on {!Files_net}. Opening a connection or a listener, accepting and writing
   raise [std.io.IoError] when they fail (std.io-errors); reads end where they
   fail. *)

open Value
module N = Files_net

let socket (args : value array) =
  match args.(0) with
  | Int id -> Hashtbl.find N.sockets id
  | _ -> invalid_arg "Eval_net.socket"

let str (args : value array) i =
  match args.(i) with Str s -> s | _ -> invalid_arg "Eval_net.str"

let int (args : value array) i =
  match args.(i) with Int n -> n | _ -> invalid_arg "Eval_net.int"

let raised (Files_process.Failed (e, at)) = Eval_system.io_error at e
let id = function Ok n -> Int n | Error e -> raised e
let done_ = function Ok () -> unit | Error e -> raised e

let native name args =
  match name with
  | "lookup" -> (
      match N.lookup (str args 0) with
      | Ok found -> List (Vec.of_list (List.map (fun a -> Str a) found))
      | Error e -> raised e)
  | "open" -> id (N.connect ~host:(str args 0) ~port:(int args 1))
  | "bind" -> id (N.listen ~host:(str args 0) ~port:(int args 1))
  | "local_port" -> Int (Int64.of_int (N.local_port (socket args)))
  | "accepted" -> id (N.accept (socket args))
  | "send" -> done_ (N.send (socket args) (str args 1))
  | "send_bytes" -> done_ (N.send (socket args) (Eval_system.bytes_of args.(1)))
  | "next_line" ->
      option (Option.map (fun l -> Str l) (N.read_line (socket args)))
  | "next_bytes" ->
      let n = Int64.to_int (int args 1) in
      Eval_system.bytes_value (N.read_bytes (socket args) n)
  | "rest" -> Str (N.read_all (socket args))
  | "timeout" ->
      N.set_timeout (socket args) (int args 1);
      unit
  | "shut" ->
      N.shutdown (socket args);
      unit
  | "datagrams" -> id (N.datagrams ~host:(str args 0) ~port:(int args 1))
  | "send_datagram" ->
      done_
        (N.send_to (socket args)
           (Eval_system.bytes_of args.(1))
           ~host:(str args 2) ~port:(int args 3))
  | "received" ->
      option (Option.map Eval_system.bytes_value (N.receive (socket args)))
  | "sender" -> Str (N.sender (socket args))
  | "closed" ->
      N.close (socket args);
      unit
  | _ -> invalid_arg ("Eval_net.native: " ^ name)
