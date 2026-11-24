(** The directories, existence, removal and renaming of [std.fs]
    (std.directories). Failures are classified as {!Files} classifies them. *)

val exists : string -> bool
val is_file : string -> bool

val is_dir : string -> bool
(** Whether anything, a regular file or a directory, is at a path, following
    symbolic links: [false] when it can't be found out. *)

val list_dir : string -> (string list, Files.error) result
(** The names of a directory's entries, without [.] and [..], with invalid UTF-8
    repaired, sorted by their bytes. A path that names a file is [Other]. *)

val create_dir : string -> (unit, Files.error) result
(** Creates a directory and every missing directory on its path. *)

val remove : string -> (unit, Files.error) result
(** Removes a file, or a directory when it is empty. *)

val remove_all : string -> (unit, Files.error) result
(** Removes a file, or a directory and everything in it, never following a
    symbolic link. *)

val rename : string -> string -> (unit, Files.error * string) result
(** [rename from into]: a failure names [from] when it doesn't exist, and
    otherwise [into]. *)
