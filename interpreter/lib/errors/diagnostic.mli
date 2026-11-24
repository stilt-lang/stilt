(** Diagnostics, as conformance.diagnostic-lines compares them: a code on a line
    of a file. *)

type t = {
  code : Code.t;  (** A code of the registry, such as [Code.e0404]. *)
  file : string;
  line : int;  (** 1-based. *)
  col : int;  (** 1-based, counting Unicode scalar values. *)
  message : string;
      (** A short explanation for people reading the reference interpreter's
          output. Conformance tests never compare it. *)
}

val at : file:string -> Code.t -> Ast.loc -> string -> t
(** [at ~file code loc message] is the diagnostic [code] at [loc] in [file]. *)

val is_error : t -> bool
(** Whether the diagnostic is an error rather than a warning. *)

val to_json : t -> string
(** The diagnostic as a JSON object with the fields [code], [file], [line],
    [col] and [message]. *)

val to_string : t -> string
(** The diagnostic as one line, [file:line:col: CODE: message]. *)
