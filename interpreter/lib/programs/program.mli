(** The source files of a program (program.forms and program.module-names), and
    its packages (packages.manifest). *)

type source = {
  module_path : string list;
      (** The segments of the module's name in the program, which the file's
          path and its package decide: [["a"; "b"]] for module [a.b], and
          [["csv"; "a"]] for module [a] of a dependency [csv]
          (packages.modules-of-dependencies). They may break the naming rule of
          program.module-names, which name resolution enforces. *)
  file : string;
      (** The path that reports name the file by: relative to the program's root
          directory, with [/] as the separator. *)
  text : string;
  package : int;  (** The index of its package in {!packages}. *)
}

type dep = {
  dep_name : string;
  target : int option;
      (** The package the entry names, or [None] when the entry has an error, so
          that what names its modules has the error type
          (packages.manifests-with-errors). *)
  may_io : bool;
      (** Whether the entry grants [io], and with it every capability
          (packages.grants; facts.capability-grants). *)
  may : Ast.capability list;
      (** The capabilities it grants (facts.capability-grants). *)
  may_unsafe : bool;  (** Whether it grants [unsafe] (c.granting-unsafe). *)
  key : Ast.loc;  (** Where the entry's key is, in its manifest. *)
}
(** An entry of a manifest's [[dependencies]]. *)

type package = {
  name : string option;
  prefix : string option;
      (** The first segment of its modules' names in the program: [None] for the
          root, whose modules keep their names. *)
  manifest : string option;  (** The path that reports give its manifest. *)
  links : (string * Ast.loc) list;
      (** The C libraries it links, each where its manifest names it
          (c.linking). *)
  deps : dep list;
  declares : bool;  (** Whether its manifest declares dependencies. *)
}

type packages = {
  list : package list;
  problems : Diagnostic.t list;
  root : string;
      (** The directory of the program's root file, or of its manifest, which
          the paths of sources and manifests are relative to. *)
}
(** A program's packages, the root's first, and the diagnostics of their
    manifests. *)

type t = { sources : source list; packages : packages }

val single : packages
(** The packages of a program without a manifest: one, which names no
    dependency. *)

val local_path : packages -> source -> string list
(** The segments of a module's name in its package: [["main"]] for a
    dependency's root module. *)

val load_libraries : packages -> unit
(** Loads the C libraries of the packages, in their order, the root's first,
    each once, before the program starts (c.loading-libraries). One that isn't
    found, which [check] reports, is left out. *)

val load : string -> (t, string) result
(** [load path] reads the program at [path], sorted by file. The program is a
    single file, which is module [main] whatever its name; a package, which is a
    directory holding [stilt.toml], whose modules are the [.lt] files under its
    [src/], and which has none without one, with the packages that its manifest
    names through path entries; or a directory program, which is any other
    directory holding [main.lt], whose modules are its [.lt] files, as
    program.module-names finds them, through links and without hidden entries.
    Any other path is an error, with a message for people, and so are a manifest
    that names a fetched dependency and a file of the program that can't be
    read. *)

val module_path : string -> string list
(** [module_path file] is the module path of the file [file], given relative to
    the module root: [["a"; "b"]] for [a/b.lt]. *)

val std : unit -> source list
(** The modules of the standard library, sorted by file. Unless
    {!read_std_examples} was called, each line that holds a doc example,
    [/// ex:] after any indentation, is cut to its [///]: only [test --std] runs
    the library's examples (std.examples), and every other command is spared
    checking them, while every position stays. *)

val read_std_examples : unit -> unit
(** Makes {!std} keep the library's doc examples. *)

val reads_std_examples : unit -> bool
(** Whether {!read_std_examples} was called. *)
