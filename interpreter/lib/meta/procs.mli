(** What name resolution asks of the procedural macros that a program's uses
    name, which run in the macro's module once that module and its imports are
    checked (macros.expansion-order and macros.running). The driver gives the
    answers, since it checks and runs a program; resolution only asks. *)

(** What a parameter of a macro takes: [meta.Expr], [meta.Pattern], [meta.Type],
    [meta.Text], [meta.File] or [meta.Tokens] (macros.procedural-declarations).
*)
type input = Takes_code of Hir.code | Takes_text | Takes_file | Takes_tokens

type signature = { inputs : input list; result : Hir.code }
(** A macro's parameters and the code it gives, [Code_expr], [Code_pattern] or
    [Code_type]. *)

(** A macro as the check of its module leaves it: one whose module has an error
    expands no use, and reports nothing there (macros.expansion-order). *)
type state = Usable of signature | Unusable

type literal = { token : Lexer.token; text : string }
(** A string literal without interpolation, and its value. *)

(** What a use gives a parameter (macros.part-forms). *)
type arg =
  | Code_arg of Hir.code * Lexer.token list
      (** A part that parses as the parameter's form, as its tokens were lexed
          where they are written. *)
  | Text_arg of literal
  | File_arg of literal * string
      (** The literal that names the file, and the file's contents, which the
          compiler read (macros.named-files). *)
  | Tokens_arg of Ast.tree list * Ast.loc
      (** Tokens, and the closing bracket that ends them. *)

type use = {
  home : string;  (** The macro's module. *)
  name : string;
  file : string;  (** The file of the use. *)
  at : Ast.loc;  (** The start of the use's path. *)
  args : arg list;
  mark : string -> int;
      (** A new number for the names that a quote of the module given writes,
          which resolve among that module's items (macros.quote-hygiene). *)
}

(** How a run ends (macros.running, macros.raised-errors and
    macros.step-limits). *)
type outcome =
  | Expanded of Lexer.token list  (** The expansion, as tokens. *)
  | Raised of Ast.loc * string
      (** A raised error: where it is placed, at the use's file, and its
          message, notes and the macro's name (E0225). *)
  | Stopped of string
      (** A run that didn't finish: the reason and the frames (E0226). *)

type host = {
  state : find:(int -> string -> string option) -> string -> string -> state;
      (** [state ~find home name], the macro [name] of the module [home], which
          a module named with [meta use], where [find] gives the module that a
          [use] in a source of a package names
          (packages.modules-of-dependencies). *)
  run : use -> outcome;
  read : file:string -> string -> (string, string) result;
      (** The contents of the file that a path names, which a literal in the
          source file [file] writes, or why no macro can be given it
          (macros.named-files). *)
  source : string -> string option;
      (** The text of a source file, by the path that reports name it. *)
}

val input : Hir.ty -> input option
(** What a parameter of this type takes, if its type is an input type of
    [std.meta]. *)

val result : Hir.ty -> Hir.code option
(** The code that a macro of this result type gives, if it is [meta.Expr],
    [meta.Pattern] or [meta.Type]. *)

val none : host
(** The host of a program that names no macro's module, such as the standard
    library: every macro is unusable. *)
