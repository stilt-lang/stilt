(** The files that procedural macros' uses name, which the compiler reads
    (macros.named-files). *)

val read : dir:string -> string -> (string, string) result
(** [read ~dir path] is the contents of the file that [path] names relative to
    the directory [dir]: names separated by [/], none empty, none [.] or [..]
    and none starting with [.], each matching an entry of its directory byte for
    byte, naming a regular file whose real path lies inside [dir] and whose
    contents are UTF-8. Anything else is [Error], with why. *)

val dir : Program.packages -> Program.source -> string
(** The directory that a literal of the source's paths are relative to: that of
    its package's manifest, or of the program's root file without one. *)
