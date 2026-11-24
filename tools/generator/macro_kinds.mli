(** The kinds of the procedural macros (macros.procedural-declarations and
    macros.procedural-bodies) of a csmith program's module of macros, made from
    a stream of their own. Each kind fixes what a use gives the macro and what
    it expands to, so that {!Csmith_macros} writes uses that check by
    construction. A macro's own code and the code its quotes write are generated
    as a function's body is, over the types of the standard library, which the
    module can name, so they can't panic, raise or loop without end
    (macros.step-limits). *)

type kind =
  | Mix of Ty.t list * Ty.t
      (** [meta.Expr] parts of these types, which the quote binds and combines
          into an expression of the last type, with [$x] splices. *)
  | Spell of Ty.t list * Ty.t
      (** A string literal, a [meta.Text], then [meta.Expr] parts of these
          types: the literal's value and values the macro computes from it,
          spliced as literals with [$x] and [$(e)], combined with the parts into
          an expression of the last type. *)
  | Listed
      (** [meta.Tokens], read by a cursor as expressions of one type separated
          by commas: a list of them, with a [$..xs] splice. *)
  | Tupled
      (** [meta.Tokens], read as expressions: a tuple of their number and them.
      *)
  | Called of Context.fn_sig
      (** [meta.Tokens], read as the helper's arguments: its call, which names
          the private helper in a quote (macros.linking). *)
  | Record
      (** [meta.Tokens], read as [name = expr] fields: a record literal whose
          fields are the user's names, through [quote field] and a [$..fields]
          splice. *)
  | Words  (** [meta.Tokens]: a [str] that tells what each token is. *)
  | Twice of Context.fn_sig
      (** A [meta.Expr] of the helper's first parameter's type, bound to a
          [meta.fresh] name by one quote, which another quote passes to the
          helper. *)
  | Either  (** Two [meta.Pattern] parts: either. *)
  | Some_of  (** A [meta.Pattern] part: [Some] of it. *)
  | Pair  (** Two [meta.Pattern] parts: the pair of them. *)
  | Spelled
      (** A [meta.Text]: a pattern of its value or of a [str] the macro computes
          from it. *)
  | Shape of Ty.t * string list
      (** [meta.Type] parts: the type, in which each of the holes, [Named] types
          written [$t], stands for the part of that parameter. *)

type decl = {
  called : string;  (** The macro's name. *)
  kind : kind;
  doc : string;  (** Its doc comment's text. *)
  params : (string * string) list;  (** Its parameters and their types. *)
  result : string;  (** [Expr], [Pattern] or [Type]. *)
  raises : bool;  (** Whether its row is [raise<meta.Error>]. *)
  body : Code.line list;
}
(** A macro's declaration. *)

type t = {
  module_name : string;
  helpers : Code.line list list;
      (** The module's functions, which its macros call. *)
  decls : decl list;  (** Its macros. *)
}
(** A module of macros. *)

val scope : Context.var list -> Context.scope
(** The scope of code that has only [vars], which performs nothing. *)

val var : Context.program -> string -> Ty.t -> Context.var
(** An immutable variable of type [ty], with a fresh name made of [prefix]. *)

val typed : Context.var -> string
(** [name: type]. *)

val helper : Context.program -> Context.fn_sig * Code.line list
(** A private function of the module, of one to three parameters, which the
    module's program declares, its body of one to three statements and its
    result. *)

val quote : ?form:string -> Code.line list -> Code.line list
(** A quote of the form [form], [pattern] or [type], or of an expression, of
    [lines]. *)

val fill : (string * Ty.t) list -> Ty.t -> Ty.t
(** [ty] with each hole replaced by its type in [types]. *)

val values :
  Context.body -> Context.var list -> int -> Context.var list * Code.line list
(** Lines that bind [n] new variables to values made from [vars], with the
    variables after them. *)

val mix : Context.program -> mark:int -> string -> decl
val spell : Context.program -> mark:int -> string -> decl
val twice : Context.program -> string -> Context.fn_sig -> decl
val spelled : Context.program -> mark:int -> string -> decl

val shape : Context.program -> string -> decl
(** Macros of these kinds, named [name], made with the module's program. The
    bodies that could be the same in two modules, the code of [Mix], [Spell] and
    [Spelled], bind the module's [mark], an [i64] that random code may read, and
    a [Shape]'s body is kept under the 20 tokens that W0302 compares
    (docs.body-size), so that no two modules of a bundle declare macros of the
    same body, which W0302 would report. *)
