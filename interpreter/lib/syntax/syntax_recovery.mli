(** A file with a syntax error, read a part at a time (errors.parts and
    errors.resuming). *)

type report = {
  error : Diagnostic.t;  (** A part's first syntax error. *)
  from : Ast.loc;  (** The part's first token. *)
  until : Ast.loc option;
      (** Where the next part starts, or reading resumes, if the part doesn't
          run to the end of the file. *)
}
(** The syntax error that a part reports, and the text in which it holds back
    every other diagnostic. *)

type t = {
  module_ : Ast.module_;  (** What the file's parts declare. *)
  broken : Ast.loc list;
      (** The names of the functions and constants, and the [test] keywords of
          the tests, that its parts that break declare with an error. *)
  reports : report list;  (** In order. *)
  extents : Syntax_parts.extent list;  (** The items of its parts, in order. *)
  comments : Lexer.comment list;  (** The comments that were lexed. *)
  unreadable : bool;
      (** Whether the file breaks lexical.source-text, and so declares nothing,
          and every path into its module has the error type. *)
}

val read : file:string -> string -> t
(** [read ~file text] reads the contents [text] of the source file [file] a part
    at a time: from its start, and again from each line where reading resumes
    after a part that breaks. *)
