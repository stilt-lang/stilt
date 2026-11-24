(* The words and tokens of reference/02-lexical.md, and the limits of the
   [limit] production of reference/03-syntax.md. Generated from the Reference
   by `just grammar-generate`, and checked current by `just grammar`. *)

open Token_type

(** The keywords of lexical.keywords, then the words that lexical.reserved-words
    reserves. *)
let keywords =
  [
    ("const", CONST);
    ("fn", FN);
    ("impl", IMPL);
    ("module", MODULE);
    ("pub", PUB);
    ("test", TEST);
    ("trait", TRAIT);
    ("type", TYPE);
    ("use", USE);
    ("inout", INOUT);
    ("let", LET);
    ("var", VAR);
    ("break", BREAK);
    ("continue", CONTINUE);
    ("else", ELSE);
    ("for", FOR);
    ("if", IF);
    ("in", IN);
    ("loop", LOOP);
    ("match", MATCH);
    ("return", RETURN);
    ("while", WHILE);
    ("assert", ASSERT);
    ("catch", CATCH);
    ("raise", RAISE);
    ("try", TRY);
    ("false", FALSE);
    ("self", SELF);
    ("Self", SELF_TYPE);
    ("true", TRUE);
    ("async", ASYNC);
    ("await", AWAIT);
    ("comptime", COMPTIME);
    ("effect", EFFECT);
    ("extern", EXTERN);
    ("handler", HANDLER);
    ("macro", MACRO);
    ("quote", QUOTE);
    ("resume", RESUME);
    ("syntax", SYNTAX);
    ("unsafe", UNSAFE);
    ("when", WHEN);
    ("where", WHERE);
    ("with", WITH);
    ("yield", YIELD);
  ]

(** The contextual keywords of lexical.contextual-keywords, which the lexer
    leaves as identifiers. *)
let contextual =
  [
    ("because", BECAUSE);
    ("io", IO);
    ("escaping", ESCAPING);
    ("without", WITHOUT);
    ("panic", PANIC);
    ("overflow", OVERFLOW);
    ("alloc", ALLOC);
    ("div", DIV);
    ("copy", COPY);
    ("fs", FS);
    ("net", NET);
    ("clock", CLOCK);
    ("env", ENV);
    ("console", CONSOLE);
    ("rand", RAND);
    ("spawn", SPAWN);
    ("exec", EXEC);
    ("locks", LOCKS);
    ("meta", META);
    ("pattern", PATTERN);
    ("field", FIELD);
  ]

(** The limits of a [without] clause, the alternatives of the production
    [limit]. *)
let limits =
  [
    ("panic", PANIC);
    ("overflow", OVERFLOW);
    ("alloc", ALLOC);
    ("div", DIV);
    ("copy", COPY);
    ("fs", FS);
    ("net", NET);
    ("clock", CLOCK);
    ("env", ENV);
    ("console", CONSOLE);
    ("rand", RAND);
    ("spawn", SPAWN);
    ("exec", EXEC);
    ("locks", LOCKS);
    ("unsafe", UNSAFE);
  ]

(** The operators and punctuation of lexical.tokens, longest first, for maximal
    munch. *)
let punctuation =
  [
    ("+%=", PLUS_WRAP_EQ);
    ("-%=", MINUS_WRAP_EQ);
    ("*%=", STAR_WRAP_EQ);
    ("<<=", LT_LT_EQ);
    (">>=", GT_GT_EQ);
    ("..=", DOT_DOT_EQ);
    ("+%", PLUS_WRAP);
    ("-%", MINUS_WRAP);
    ("*%", STAR_WRAP);
    ("==", EQ_EQ);
    ("!=", BANG_EQ);
    ("<=", LT_EQ);
    (">=", GT_EQ);
    ("&&", AMP_AMP);
    ("||", PIPE_PIPE);
    ("<<", LT_LT);
    (">>", GT_GT);
    ("+=", PLUS_EQ);
    ("-=", MINUS_EQ);
    ("*=", STAR_EQ);
    ("/=", SLASH_EQ);
    ("%=", PERCENT_EQ);
    ("&=", AMP_EQ);
    ("|=", PIPE_EQ);
    ("^=", CARET_EQ);
    ("->", ARROW);
    ("=>", FAT_ARROW);
    ("..", DOT_DOT);
    ("+", PLUS);
    ("-", MINUS);
    ("*", STAR);
    ("/", SLASH);
    ("%", PERCENT);
    ("<", LT);
    (">", GT);
    ("!", BANG);
    ("&", AMP);
    ("|", PIPE);
    ("^", CARET);
    ("=", EQ);
    (".", DOT);
    (",", COMMA);
    (":", COLON);
    (";", SEP);
    ("(", LPAREN);
    (")", RPAREN);
    ("[", LBRACKET);
    ("]", RBRACKET);
    ("{", LBRACE);
    ("}", RBRACE);
    ("?", QUESTION);
    ("$", DOLLAR);
    ("@", AT);
    ("'", TICK);
    ("#", HASH);
  ]

(** The primitive type names of lexical.primitive-type-names. *)
let primitive_types =
  [
    "bool";
    "i8";
    "i16";
    "i32";
    "i64";
    "u8";
    "u16";
    "u32";
    "u64";
    "f32";
    "f64";
    "str";
  ]
