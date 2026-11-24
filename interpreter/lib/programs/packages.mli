(** The packages of a program, as its manifests name them through path entries
    (packages.path-dependencies, packages.one-name-one-package and
    packages.dependency-cycles). *)

exception Fetched of string
(** A manifest names a fetched dependency, from this repository, which the
    reference interpreter doesn't fetch: conformance tests reach only path
    dependencies. *)

type package = {
  dir : string;  (** Its directory on disk. *)
  shown : string;
      (** Its directory as reports name it, relative to the root's: empty for
          the root. *)
  manifest : Manifest.t;
  text : string;  (** The manifest's text. *)
  mutable deps : int option list;
      (** What each entry of its manifest names, in order: the index of the
          package, or [None] when the entry has an error. *)
}

type t = { packages : package list; problems : Diagnostic.t list }
(** The packages of a program, the root first, and the diagnostics of their
    manifests. *)

val manifest_path : package -> string
(** The path that reports give the package's manifest. *)

val position : string -> int -> Ast.loc
(** The line and column of a byte offset of a text. *)

val read_graph : string -> t
(** The packages of the program whose root package is in the directory.

    @raise Fetched if a manifest names a fetched dependency. *)
