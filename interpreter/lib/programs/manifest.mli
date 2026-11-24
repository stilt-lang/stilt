(** A package's manifest, [stilt.toml] (packages.manifest,
    packages.package-table and packages.dependencies; facts.capability-grants;
    c.granting-unsafe and c.linking). *)

(** Where a dependency comes from. *)
type source =
  | Path of string  (** A directory, relative to the manifest's. *)
  | From of { from : string; version : string option; hash : string option }
      (** A git repository, which the reference interpreter doesn't fetch. *)

type entry = {
  name : string;
  key_at : int;  (** The byte offset of its key. *)
  source : source option;  (** [None] when the entry has an E0600. *)
  may_io : bool;  (** Whether its [may] grants [io], and every capability. *)
  may : Ast.capability list;
      (** The capabilities its [may] lists, in order (facts.capability-grants).
      *)
  may_unsafe : bool;
      (** Whether its [may] grants [unsafe] (c.granting-unsafe). *)
}
(** An entry of [[dependencies]]. *)

type t = {
  name : string option;  (** The valid name of [[package]], if it gives one. *)
  links : (string * int) list;
      (** The C libraries that [[package]]'s [link] names validly, in order,
          each with the byte offset of its string (c.linking). *)
  declares : bool;
      (** Whether it declares dependencies: it is TOML 1.0, and its
          [[dependencies]] is a table when it has one (packages.dependencies).
      *)
  entries : entry list;
  problems : (int * string) list;
      (** Its E0600s, each at a byte offset, with a message, in order. *)
}

val read : string -> t
(** Reads a manifest. A text that isn't TOML 1.0 declares no name and no
    dependency, and has one E0600, where no TOML document can continue. *)
