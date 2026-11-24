(** The sockets of [std.net] (std.net, std.net-streams, std.net-listeners and
    std.net-datagrams): the addresses of a host, TCP connections, read through a
    buffer and written whole, listeners, and UDP sockets, each known by its
    number. A failure names the address that a socket was opened with, the peer
    that a listener accepted, or the address that a datagram was sent to. *)

type failure = Files_process.failure
(** The sockets of [std.net] (std.net, std.net-streams, std.net-listeners and
    std.net-datagrams): the addresses of a host, TCP connections, read through a
    buffer and written whole, listeners, and UDP sockets, each known by its
    number. A failure names the address that a socket was opened with, the peer
    that a listener accepted, or the address that a datagram was sent to. *)

type kind =
  | Stream of { mutable input : in_channel option }
  | Listener
  | Datagrams of { mutable from : string }
  | Closed

type socket = { address : string; fd : Unix.file_descr; mutable kind : kind }

val sockets : (int64, socket) Hashtbl.t
(** The open sockets, each by the number that [std.net] knows it by. *)

val lookup : string -> (string list, Files_process.failure) result
(** The addresses of [host], in the system's order, each once, or [Missing] when
    it has none. *)

val connect : host:string -> port:int64 -> (int64, Files_process.failure) result
(** A TCP connection to [port] of [host], tried at each of its addresses in
    turn, as a socket's number. *)

val listen : host:string -> port:int64 -> (int64, Files_process.failure) result
(** A listener bound to [port] of [host], at its first address that takes it, as
    a socket's number. *)

val datagrams :
  host:string -> port:int64 -> (int64, Files_process.failure) result
(** A UDP socket bound to [port] of [host], at its first address that takes it,
    as a socket's number. *)

val send_to :
  socket ->
  string ->
  host:string ->
  port:int64 ->
  (unit, Files_process.failure) result
(** Sends [bytes] as one datagram to [port] of [host], to each of its addresses
    in turn until one takes it. *)

val receive : socket -> string option
(** The bytes of the next datagram, whose sender the socket keeps, or [None]
    where the wait gives up or fails, or the socket is closed. *)

val sender : socket -> string
(** The address of the sender of the last datagram the socket received, as
    [ip:port], or [""]. *)

val local_port : socket -> int
(** The port the socket is bound to, or 0 for one that is closed or has none. *)

val accept : socket -> (int64, Files_process.failure) result
(** The next connection a listener accepts, as a new socket's number, named by
    its peer's address. *)

val send : socket -> string -> (unit, Files_process.failure) result
(** Writes all of [text] to a connection. *)

val read_line : socket -> string option
(** The next line a connection reads, without its line break, or [None] at the
    end or where a read fails. *)

val read_bytes : socket -> int -> string
(** At most [n] bytes, fewer only at the end, or where a read fails. *)

val read_all : socket -> string
(** What a connection reads until its end, with invalid UTF-8 repaired. *)

val set_timeout : socket -> int64 -> unit
(** Gives up a read or a write that waits longer than [ms] milliseconds, or
    never for 0. *)

val shutdown : socket -> unit
(** Ends what the socket sends, so that its peer reads the end. *)

val close : socket -> unit
(** Closes the socket, which then reads and sends nothing. *)
