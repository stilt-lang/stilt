(** The tokens of Stilt (lexical.tokens), the parser's terminals. The spellings
    of the keywords and of the operators and punctuation are [Lexicon]'s, which
    [Token] gives the lexer. *)

type t =
  | LIDENT of string
      (** An identifier whose first letter, after any leading underscores, is
          lowercase. Primitive type names and contextual keywords are [LIDENT]s.
      *)
  | UIDENT of string
      (** An identifier whose first letter, after any leading underscores, is
          uppercase. *)
  | UNDERSCORE  (** The wildcard [_]. *)
  | INT of string
      (** An integer literal, as written but without [_] separators. *)
  | FLOAT of string
      (** A float literal, as written but without [_] separators. *)
  | STRING of string
      (** A string literal with no interpolation, with its escapes resolved. *)
  | STRING_HEAD of string
      (** The text of a string literal before its first interpolation. *)
  | STRING_MID of string  (** The text between two interpolations. *)
  | STRING_TAIL of string  (** The text after the last interpolation. *)
  | FORMAT of string
      (** The format spec that ends an interpolation, without its [:]. *)
  | ASSERT
  | BREAK
  | CATCH
  | CONST
  | CONTINUE
  | ELSE
  | FALSE
  | FN
  | FOR
  | IF
  | IMPL
  | IN
  | INOUT
  | LET
  | LOOP
  | MATCH
  | MODULE
  | PUB
  | RAISE
  | RETURN
  | SELF
  | SELF_TYPE  (** [Self]. *)
  | TEST
  | TRAIT
  | TRUE
  | TRY
  | TYPE
  | USE
  | VAR
  | WHILE
  | YIELD
  | WHERE
  | SYNTAX
      (** [syntax], which declares a pattern macro (macros.syntax-declarations).
      *)
  | EFFECT
      (** [effect], which declares an effect (handlers.declaring-effect). *)
  | HANDLER
      (** [handler], of a handler type or literal (handlers.handler-literals).
      *)
  | WITH  (** [with], which installs handlers (handlers.with). *)
  | RESUME  (** [resume], in a handler's operation (handlers.resuming). *)
  | ASYNC  (** [async], the effect of tasks (tasks.async). *)
  | AWAIT
      (** [await], a member's name after [.] (tasks.std-task), and the name of
          one declaration of the standard library. *)
  | WHEN  (** [when], which holds shared values (shared.when). *)
  | COMPTIME
      (** [comptime], a staging annotation (meta.staging-annotations). *)
  | MACRO
      (** [macro], which declares a procedural macro
          (macros.procedural-declarations). *)
  | QUOTE  (** [quote] (macros.quote). *)
  | EXTERN
      (** [extern], which exports a function after [pub] (c.exported-functions),
          and declares a foreign function before one without a body
          (c.foreign-functions). *)
  | UNSAFE
      (** [unsafe], which starts a block (c.unsafe-because) and is a limit
          (c.without-unsafe). *)
  | WITHOUT
      (** The lexer never produces the contextual keywords, from [WITHOUT] to
          [IO]. It produces [LIDENT]s, which the parser reads as these tokens
          where its grammar accepts them (lexical.contextual-keywords). *)
  | PANIC
  | ALLOC
  | DIV
  | COPY
  | FS
  | NET
  | CLOCK
  | ENV
  | CONSOLE
  | RAND
  | SPAWN
  | EXEC
  | LOCKS  (** [locks], a limit (shared.locks). *)
  | OVERFLOW  (** [overflow], a limit (effects.without-overflow). *)
  | BECAUSE
  | IO
  | ESCAPING
  | META  (** [meta] before [use] (macros.meta-use). *)
  | PATTERN
  | FIELD  (** [pattern] and [field] after [quote] (macros.quote). *)
  | PLUS
  | MINUS
  | STAR
  | SLASH
  | PERCENT
  | PLUS_WRAP
  | MINUS_WRAP
  | STAR_WRAP
  | EQ_EQ
  | BANG_EQ
  | LT
  | LT_EQ
  | GT
  | GT_EQ
  | AMP_AMP
  | PIPE_PIPE
  | BANG
  | AMP
  | PIPE
  | CARET
  | LT_LT
  | GT_GT
  | EQ
  | PLUS_EQ
  | MINUS_EQ
  | STAR_EQ
  | SLASH_EQ
  | PERCENT_EQ
  | PLUS_WRAP_EQ
  | MINUS_WRAP_EQ
  | STAR_WRAP_EQ
  | AMP_EQ
  | PIPE_EQ
  | CARET_EQ
  | LT_LT_EQ
  | GT_GT_EQ
  | ARROW
  | FAT_ARROW
  | DOT
  | DOT_DOT
  | DOT_DOT_EQ
  | COMMA
  | COLON
  | LPAREN
  | RPAREN
  | LBRACKET
  | RBRACKET
  | LBRACE
  | RBRACE
  | QUESTION
  | AT  (** Reserved for later tiers, like [TICK] and [HASH]. *)
  | DOLLAR
      (** [$], which stands only in a macro's patterns and templates
          (macros.templates), and in quotes (macros.splices). *)
  | SPLICE
      (** [$] inside a quote, as the parser's driver offers it, which the lexer
          never makes (macros.splices). *)
  | TICK  (** ['], reserved. *)
  | HASH
  | SEP  (** A separator: [;] or an inserted terminator. *)
  | DOC of Ast.doc_line list
      (** A run of doc comments, placed just before the token it documents. The
          parser's driver makes these from comments; the lexer doesn't. *)
  | MISPLACED_DOC
      (** A doc comment that documents nothing. The grammar never accepts it. *)
  | MACRO_TOKEN of Ast.atom
      (** A token that stands for itself among the tokens of a macro's pattern,
          its template or a use's groups (macros.patterns, macros.templates and
          macros.uses). The lexer never produces it: the parser's driver reads a
          token as one where the grammar accepts it. *)
  | EOF
