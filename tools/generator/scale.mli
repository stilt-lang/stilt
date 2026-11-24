(** Scale projects: directory programs of many modules that import one another,
    whose modules are csmith programs without [main]. *)

val project : seed:int -> lines:int -> (string * string) list
(** A scale project from [seed], of at least [lines] lines: the module that
    declares the error type, modules that import one another in an acyclic
    graph, and [main], which imports the last eight of them. Each file comes
    with its path from the project's root. *)
