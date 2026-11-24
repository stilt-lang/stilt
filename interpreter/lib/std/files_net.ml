(* The sockets of [std.net] (std.net, std.net-streams, std.net-listeners and
   std.net-datagrams): the addresses of a host, TCP connections, read through a
   buffer and written whole, listeners, and UDP sockets, each known by its
   number. A failure names the address that a socket was opened with, the peer
   that a listener accepted, or the address that a datagram was sent to. *)

type failure = Files_process.failure

type kind =
  | Stream of { mutable input : in_channel option }
  | Listener
  | Datagrams of { mutable from : string }
  | Closed

type socket = { address : string; fd : Unix.file_descr; mutable kind : kind }

let sockets : (int64, socket) Hashtbl.t = Hashtbl.create 8
let count = ref 0L
let restarting = Files_process.restarting
let other at = Error (Files_process.Failed (Files.Other, at))

let register socket =
  count := Int64.add !count 1L;
  Hashtbl.replace sockets !count socket;
  !count

(* The addresses of [host], in the system's order, each once. *)
let addresses host =
  if host = "" || String.contains host '\000' then []
  else
    let found =
      Unix.getaddrinfo host "" [ Unix.AI_SOCKTYPE Unix.SOCK_STREAM ]
      |> List.filter_map (fun (i : Unix.addr_info) ->
          match i.ai_addr with Unix.ADDR_INET (a, _) -> Some a | _ -> None)
    in
    List.fold_left
      (fun kept a -> if List.mem a kept then kept else kept @ [ a ])
      [] found

let lookup host =
  if String.contains host '\000' then other host
  else
    match addresses host with
    | [] -> Error (Files_process.Failed (Files.Missing, host))
    | found -> Ok (List.map Unix.string_of_inet_addr found)

(* A peer's address, as [ip:port], with brackets around an IPv6 address. *)
let peer = function
  | Unix.ADDR_INET (a, port) ->
      let ip = Unix.string_of_inet_addr a in
      let ip = if String.contains ip ':' then "[" ^ ip ^ "]" else ip in
      Printf.sprintf "%s:%d" ip port
  | Unix.ADDR_UNIX path -> path

let domain a = if Unix.is_inet6_addr a then Unix.PF_INET6 else Unix.PF_INET

(* Calls [use] on a new socket for each address of [host] in turn, until one
   gives no error, and gives the first socket that it opens, or the failure
   of the last attempt. *)
let first_of ?(kind = Unix.SOCK_STREAM) ~host ~port use =
  let at = Printf.sprintf "%s:%Ld" host port in
  if port < 0L || port > 65535L || String.contains host '\000' then other at
  else
    let rec go last = function
      | [] -> Error (Files_process.Failed (last, at))
      | a :: rest -> (
          let fd = Unix.socket ~cloexec:true (domain a) kind 0 in
          match use fd (Unix.ADDR_INET (a, Int64.to_int port)) with
          | () ->
              Ok (register { address = at; fd; kind = Stream { input = None } })
          | exception Unix.Unix_error (e, _, _) ->
              Unix.close fd;
              go (Files.error_of e) rest)
    in
    match addresses host with
    | [] -> Error (Files_process.Failed (Files.Missing, at))
    | found -> go Files.Other found

let connect ~host ~port =
  first_of ~host ~port (fun fd addr ->
      restarting (fun () -> Unix.connect fd addr))

let listen ~host ~port =
  let opened =
    first_of ~host ~port (fun fd addr ->
        Unix.setsockopt fd Unix.SO_REUSEADDR true;
        Unix.bind fd addr;
        Unix.listen fd 128)
  in
  Result.iter (fun id -> (Hashtbl.find sockets id).kind <- Listener) opened;
  opened

let datagrams ~host ~port =
  let opened =
    first_of ~kind:Unix.SOCK_DGRAM ~host ~port (fun fd addr ->
        Unix.bind fd addr)
  in
  Result.iter
    (fun id -> (Hashtbl.find sockets id).kind <- Datagrams { from = "" })
    opened;
  opened

(* The most bytes of a datagram that a socket receives: the most that UDP
   carries. *)
let datagram = 65536

(* Sends [bytes] as one datagram to [port] of [host], to each of its addresses
   in turn until one takes it. *)
let send_to s bytes ~host ~port =
  let at = Printf.sprintf "%s:%Ld" host port in
  if port < 0L || port > 65535L || String.contains host '\000' then other at
  else
    match (s.kind, addresses host) with
    | _, [] -> Error (Files_process.Failed (Files.Missing, at))
    | Datagrams _, found ->
        let rec go last = function
          | [] -> Error (Files_process.Failed (last, at))
          | a :: rest -> (
              let to_ = Unix.ADDR_INET (a, Int64.to_int port) in
              match
                restarting (fun () ->
                    Unix.sendto_substring s.fd bytes 0 (String.length bytes) []
                      to_)
              with
              | _ -> Ok ()
              | exception Unix.Unix_error (e, _, _) ->
                  go (Files.error_of e) rest)
        in
        go Files.Other found
    | _ -> other at

(* The bytes of the next datagram, whose sender the socket keeps, or [None]
   where the wait gives up or fails, or the socket is closed. *)
let receive s =
  match s.kind with
  | Datagrams d -> (
      let buffer = Bytes.create datagram in
      match restarting (fun () -> Unix.recvfrom s.fd buffer 0 datagram []) with
      | n, addr ->
          d.from <- peer addr;
          Some (Bytes.sub_string buffer 0 n)
      | exception Unix.Unix_error _ -> None)
  | _ -> None

let sender s = match s.kind with Datagrams d -> d.from | _ -> ""

let local_port s =
  match Unix.getsockname s.fd with
  | Unix.ADDR_INET (_, port) when s.kind <> Closed -> port
  | _ | (exception Unix.Unix_error _) -> 0

let accept s =
  match s.kind with
  | Listener -> (
      match restarting (fun () -> Unix.accept ~cloexec:true s.fd) with
      | fd, addr ->
          Ok
            (register
               { address = peer addr; fd; kind = Stream { input = None } })
      | exception Unix.Unix_error _ -> other s.address)
  | _ -> other s.address

let send s text =
  match s.kind with
  | Stream _ -> (
      let rec go at =
        if at < String.length text then
          go
            (at
            + restarting (fun () ->
                Unix.write_substring s.fd text at (String.length text - at)))
      in
      try
        Files_process.without_broken_pipes (fun () -> go 0);
        Ok ()
      with Unix.Unix_error _ -> other s.address)
  | _ -> other s.address

(* The channel that a stream reads through, made at its first read. *)
let input s =
  match s.kind with
  | Stream r -> (
      match r.input with
      | Some ic -> Some ic
      | None ->
          let ic = Unix.in_channel_of_descr s.fd in
          r.input <- Some ic;
          Some ic)
  | Listener | Datagrams _ | Closed -> None

let read_line s =
  match input s with
  | None -> None
  | Some ic -> (
      match In_channel.input_line ic with
      | Some l -> Some (Files_process.line l)
      | None | (exception (Sys_error _ | Sys_blocked_io)) -> None)

(* At most [n] bytes, fewer only at the end, or where a read fails. *)
let read_bytes s n =
  let b = Buffer.create (max 0 (min n 65536)) in
  let chunk = Bytes.create 65536 in
  let rec go ic left =
    if left > 0 then
      match In_channel.input ic chunk 0 (min left 65536) with
      | 0 -> ()
      | got ->
          Buffer.add_subbytes b chunk 0 got;
          go ic (left - got)
      | exception (Sys_error _ | Sys_blocked_io) -> ()
  in
  Option.iter (fun ic -> go ic n) (input s);
  Buffer.contents b

let read_all s = Strings.repair (read_bytes s max_int)

let set_timeout s ms =
  let seconds = if ms > 0L then Int64.to_float ms /. 1000. else 0. in
  try
    Unix.setsockopt_float s.fd Unix.SO_RCVTIMEO seconds;
    Unix.setsockopt_float s.fd Unix.SO_SNDTIMEO seconds
  with Unix.Unix_error _ -> ()

let shutdown s =
  if s.kind <> Closed then
    try Unix.shutdown s.fd Unix.SHUTDOWN_SEND with Unix.Unix_error _ -> ()

let close s =
  (match s.kind with
  | Stream { input = Some ic } -> close_in_noerr ic
  | Stream { input = None } | Listener | Datagrams _ -> (
      try Unix.close s.fd with Unix.Unix_error _ -> ())
  | Closed -> ());
  s.kind <- Closed
