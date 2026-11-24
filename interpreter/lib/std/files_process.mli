(** Other programs (std.process-starting, std.process-runs and std.children): a
    command's program looked up in its PATH, its environment and directory, and
    its runs, to their end with their streams captured or inherited, or beside
    the program with their standard input and output piped. *)

type failure =
  | Failed of Files.error * string
      (** Other programs (std.process-starting, std.process-runs and
          std.children): a command's program looked up in its PATH, its
          environment and directory, and its runs, to their end with their
          streams captured or inherited, or beside the program with their
          standard input and output piped. *)

type output = {
  mutable chan : in_channel option;
  mutable kept : string;
  mutable at : int;
}
(** A child's standard output: the channel it is read from while it is open,
    then what [keep] read of it ahead, from [at]. *)

type child = {
  program : string;
  pid : int;
  mutable input : out_channel option;
  output : output;
  mutable status : int option;
  mutable captured : string * string;
}

val children : (int64, child) Hashtbl.t
(** The children that commands started, and the runs that ended, each by the
    number that [std.process] knows it by. *)

val restarting : (unit -> 'a) -> 'a
(** [f ()], started again each time a signal interrupts it. *)

val without_broken_pipes : (unit -> 'a) -> 'a
(** Runs [f], in which a write to a child that has closed its input fails with
    EPIPE rather than ending the program, while no child that it starts inherits
    the signal ignored. *)

val start :
  program:string ->
  args:string list ->
  set:string list ->
  removed:string list ->
  dir:string ->
  mode:int ->
  input:string ->
  (int64, failure) result
(** Runs [program] with [args], in [dir] when it isn't empty, with the program's
    environment but the names [set] gives values to and those [removed]: in mode
    0 to its end with [input] written to it and its streams captured, in mode 1
    to its end with the program's streams, and otherwise beside the program with
    its standard input and output piped. Gives the child's number. *)

val write : child -> string -> (unit, failure) result
(** Writes [text] to a child's standard input. *)

val close_input : child -> unit
(** Closes a child's standard input, so that it reads its end. *)

val line : string -> string
(** A line without the [\r] that ends it, as [io.read_line] gives one. *)

val read_line : child -> string option
(** The next line of a child's standard output, without its line break, or
    [None] at its end. *)

val read_all : child -> string
(** The rest of a child's standard output, with invalid UTF-8 repaired. *)

val wait : child -> int
(** A child's exit status once it ends, after closing its input and keeping the
    rest of its output for [read_line] and [read_all]. *)

val kill : child -> unit
(** Ends a child that hasn't ended, by [SIGKILL]. *)
