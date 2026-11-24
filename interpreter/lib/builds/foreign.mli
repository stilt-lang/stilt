(** What the reference interpreter does with C (c.linking, c.calls and
    c.both-implementations), through its own stubs over the platform's loader
    and libffi: the libraries a program links, its foreign calls, and the memory
    that lent lists and strings copy into. *)

val load : string -> bool
(** [load name] loads the library [name] as the dynamic loader finds
    [libNAME.dylib] on macOS and [libNAME.so] elsewhere, its functions visible
    to every later call, and tells whether it found it (c.loading-libraries). *)

val call :
  string -> Types.ty list -> Types.ty -> Value.value list -> Value.value
(** [call name params ret args] calls the C function [name], found among the C
    library and the libraries loaded, with arguments of types [params], and
    gives its result, of type [ret] (c.calls). A name that nothing loaded
    defines ends the program, as running out of memory does.

    @raise Eval_state.Fatal for a name that nothing defines. *)

val size : Types.ty -> int
(** The bytes that C holds a value of a type in: its width for a number, one for
    [bool], and an address's for a [c.Ptr] (c.element-types). *)

val read : Types.ty -> int64 -> Value.value
(** [read t address] is the value of type [t] at [address]. *)

val write : Types.ty -> int64 -> Value.value -> unit
(** [write t address v] writes [v], of type [t], at [address]. *)

val lend : Types.ty -> Value.value list -> int64
(** [lend t xs] copies the elements of a list of [t] into a new C buffer, one
    after another as C holds them, and gives its address, which isn't 0 even for
    no element (c.lending-buffer). {!free} frees it. *)

val read_list : Types.ty -> int64 -> int -> Value.value list
(** [read_list t address n] reads [n] values of [t] from [address] on. *)

val c_string : string -> int64
(** A new C buffer holding the bytes of a string and a NUL. {!free} frees it. *)

val to_str : int64 -> string
(** The bytes at an address up to the NUL, each maximal subpart of an invalid
    UTF-8 sequence replaced by one U+FFFD. *)

val free : int64 -> unit
