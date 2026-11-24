(* The grammar of core Stilt, as reference/03-syntax.md states it. Its sections
   follow the sections of that document, over five files that Menhir joins into
   one parser: this one, with the tokens, their priorities, the lists and
   programs, then parser_declarations.mly, parser_macros.mly, parser_types.mly,
   parser_patterns.mly and parser_expressions.mly. A symbol that another file refers to is
   %public, and the header below serves the actions of all five.

   Every syntax error is found by the automaton itself: no action rejects
   anything. Ambiguities are settled by the precedence declarations, which
   transcribe the rules of the grammar's "Settling ambiguities" section, and by
   nothing else: Menhir runs with --strict, so any conflict they leave is an
   error. *)

%{
open Ast

(* Positions come from [$startpos], or from [$symbolstartpos] where a
   production can start with an empty symbol such as [boption(PUB)], whose
   [$startpos] would be the end of the previous token. *)
let loc (p : Lexing.position) = { line = p.pos_lnum; col = p.pos_cnum }
let node desc p = { desc; loc = loc p }

(* A pack, [..T], whose name is placed at its [..] (variadics.packs). *)
let packed p (t : type_param) =
  { t with pack = true; name = { t.name with loc = loc p } }

(* expressions.trailing-commas: [(e)] is [e], and [(e,)] is a one-element tuple. A spread
   makes a tuple of its own (variadics.spread-expressions). *)
let parenthesized ?(spread = fun _ -> false) ~tuple (items, trailing) p =
  match items with
  | [ item ] when not (trailing || spread item) -> item
  | items -> node (tuple items) p

let is_spread_ty (t : ty) = match t.desc with Ty_spread _ -> true | _ -> false

let is_spread (e : expr) =
  match e.desc with Spread _ | Q_spread _ -> true | _ -> false

(* A record literal or a struct literal, or in a quote one with a field that
   a splice names, or a spread of fields (macros.splices). *)
let plain_fields fields =
  List.fold_right
    (fun f plain ->
      match (f, plain) with
      | Field_init f, Some fs -> Some (f :: fs)
      | _ -> None)
    fields (Some [])

let record_literal base fields p =
  match plain_fields fields with
  | Some fs -> node (Record_literal (base, fs)) p
  | None -> node (Q_record (base, fields)) p

let struct_literal path base fields p =
  match plain_fields fields with
  | Some fs -> node (Struct (path, base, fs)) p
  | None -> node (Q_struct (path, base, fields)) p

let record_pattern path (fields, rest) p =
  let plain =
    List.fold_right
      (fun f plain ->
        match (f, plain) with
        | Field_pattern f, Some fs -> Some (f :: fs)
        | _ -> None)
      fields (Some [])
  in
  match plain with
  | Some fs -> node (P_record (path, fs, rest)) p
  | None -> node (P_spliced_record (path, fields, rest)) p

(* macros.quote: a quote, with its contents between two brackets. *)
let quote form opening closing p =
  node (Quote { form; tokens = Quote_tokens.between opening closing }) p

(* The expression a path of identifiers stands for: a name, then fields. *)
let path_expr (path : path) =
  match path with
  | [] -> assert false
  | first :: rest ->
      List.fold_left
        (fun base (member : name) -> { desc = Field (base, member); loc = base.loc })
        { desc = Name first.desc; loc = first.loc }
        rest

let fn_decl (name, generics, params, (projection, ret), row) where_ without body =
  { name; generics; params; ret; projection; row; where_; without; body }

let documented doc (d : decl node) = { d with desc = { d.desc with doc } }

let segments head splices =
  let text s = if s = "" then [] else [ Text s ] in
  text head @ List.concat_map (fun (splice, after) -> splice :: text after) splices
%}

%token <string> LIDENT UIDENT INT FLOAT STRING
%token <string> STRING_HEAD STRING_MID STRING_TAIL FORMAT
%token UNDERSCORE ASSERT BREAK CATCH CONST CONTINUE ELSE FALSE FN FOR IF
%token IMPL IN INOUT LET LOOP MATCH MODULE PUB RAISE RETURN SELF SELF_TYPE
%token TEST TRAIT TRUE TRY TYPE USE VAR WHERE WHILE YIELD SYNTAX
%token EFFECT HANDLER WITH RESUME ASYNC AWAIT WHEN COMPTIME MACRO QUOTE EXTERN
%token UNSAFE
%token WITHOUT PANIC ALLOC DIV COPY BECAUSE IO ESCAPING META PATTERN FIELD
%token FS NET CLOCK ENV CONSOLE RAND SPAWN EXEC LOCKS OVERFLOW
%token PLUS MINUS STAR SLASH PERCENT PLUS_WRAP MINUS_WRAP STAR_WRAP
%token EQ_EQ BANG_EQ LT LT_EQ GT GT_EQ AMP_AMP PIPE_PIPE BANG AMP PIPE CARET
%token LT_LT GT_GT
%token EQ PLUS_EQ MINUS_EQ STAR_EQ SLASH_EQ PERCENT_EQ PLUS_WRAP_EQ
%token MINUS_WRAP_EQ STAR_WRAP_EQ AMP_EQ PIPE_EQ CARET_EQ LT_LT_EQ GT_GT_EQ
%token ARROW FAT_ARROW DOT DOT_DOT DOT_DOT_EQ COMMA COLON
%token LPAREN RPAREN LBRACKET RBRACKET LBRACE RBRACE QUESTION
%token AT DOLLAR SPLICE TICK HASH SEP EOF
%token <Ast.doc_line list> DOC
%token MISPLACED_DOC
%token <Ast.atom> MACRO_TOKEN

(* From loosest to tightest. The first two levels are pseudo-tokens that
   name productions: a function type without a row gives way to the [/] of
   a row, and an [if] without [else] to an [else]. Then expressions.precedence table runs
   from level 14 up to level 3. [CATCH] sits between level 14 and [else], so
   that a [catch] joins the innermost [try] still open. *)
%nonassoc below_slash below_else
%nonassoc LEVEL14
%nonassoc CATCH
%right ELSE
%left PIPE_PIPE
%left AMP_AMP
%nonassoc EQ_EQ BANG_EQ LT LT_EQ GT GT_EQ
%left PIPE
%left CARET
%left AMP
%left LT_LT GT_GT
%left PLUS MINUS PLUS_WRAP MINUS_WRAP
%left STAR SLASH PERCENT STAR_WRAP
%nonassoc PREFIX

%start <Ast.module_> file
%start <Ast.expr> example
%start <unit> code
%start <Ast.pattern> pattern_example
%start <Ast.ty> type_example
%start <Ast.block> block_example

%%

(* Lists *)

(* A comma-separated list that may be empty and may end with a comma. *)
%public comma_list(X):
  | { [] }
  | xs = nonempty_comma_list(X) { xs }

%public nonempty_comma_list(X):
  | x = X { [ x ] }
  | x = X COMMA { [ x ] }
  | x = X COMMA xs = nonempty_comma_list(X) { x :: xs }

(* A comma-separated list, telling whether it ends with a comma. *)
%public comma_list_t(X):
  | { ([], false) }
  | x = X { ([ x ], false) }
  | x = X COMMA { ([ x ], true) }
  | x = X COMMA rest = comma_list_t_more(X) { (x :: fst rest, snd rest) }

comma_list_t_more(X):
  | x = X { ([ x ], false) }
  | x = X COMMA { ([ x ], true) }
  | x = X COMMA rest = comma_list_t_more(X) { (x :: fst rest, snd rest) }

(* Programs *)

file:
  | MODULE path = lower_path tail = header_tail
    { let withouts, items = tail in
      { header = Some (node { path; withouts } $startpos); items } }
  | items = separated_list(SEP, item) EOF { { header = None; items } }

(* A header may hold several clauses: name resolution reports every one after
   the first (program.module-header). A clause follows the path on its line, on the
   next, where no separator ends the line (lexical.terminator-insertion), or after a [;]. *)
header_tail:
  | EOF { ([], []) }
  | SEP w = without tail = header_tail { (w :: fst tail, snd tail) }
  | w = without tail = header_tail { (w :: fst tail, snd tail) }
  | SEP items = separated_nonempty_list(SEP, item) EOF { ([], items) }

(* A [without] clause, in a header or on a function (program.header-limits; declarations.limits). *)
%public without:
  | WITHOUT limits = separated_nonempty_list(COMMA, limit)
    { node limits $startpos }

limit:
  | PANIC { node Panic $startpos }
  | ALLOC { node Alloc $startpos }
  | DIV { node (Div : limit) $startpos }
  | COPY { node Copy $startpos }
  (* facts.without *)
  | FS { node (Capability Fs) $startpos }
  | NET { node (Capability Net) $startpos }
  | CLOCK { node (Capability Clock) $startpos }
  | ENV { node (Capability Env) $startpos }
  | CONSOLE { node (Capability Console) $startpos }
  | RAND { node (Capability Rand) $startpos }
  | SPAWN { node (Capability Spawn) $startpos }
  | EXEC { node (Capability Exec) $startpos }
  (* shared.locks *)
  | LOCKS { node Locks $startpos }
  (* effects.without-overflow *)
  | OVERFLOW { node Overflow $startpos }
  (* c.without-unsafe: a keyword, not a contextual one *)
  | UNSAFE { node (Unsafe : limit) $startpos }

item:
  | USE path = use_path { node (Use path) $startpos }
  (* macros.meta-use *)
  | META USE path = use_path { node (Meta_use path) $startpos }
  | doc = doc d = module_decl { { desc = Decl (documented doc d).desc; loc = d.loc } }
  | IMPL generics = impl_generics self_ty = ty where_ = option(where_clause)
    LBRACE members = separated_list(SEP, inherent_member) RBRACE
    { node (Impl { generics; trait_ = None; self_ty; where_; members }) $startpos }
  | IMPL generics = impl_generics trait_ = bound FOR self_ty = ty
    where_ = option(where_clause)
    LBRACE members = separated_list(SEP, trait_impl_member) RBRACE
    { node (Impl { generics; trait_ = Some trait_; self_ty; where_; members }) $startpos }

%public doc:
  | { [] }
  | d = DOC { d }

(* Doc examples (program.doc-examples) *)

example:
  | e = expr EOF { e }

(* The forms that a macro's fragments match, and that its expansions are
   parsed as (macros.checked-templates, macros.matching and macros.expansion), beside [example] for expressions. *)

pattern_example:
  | p = pattern EOF { p }

type_example:
  | t = ty EOF { t }

block_example:
  | b = block EOF { b }

(* Commented-out code (lexical.commented-out-code): the text of a comment that holds
   statements or items. *)

code:
  | separated_nonempty_list(SEP, stmt) EOF { () }
  | separated_nonempty_list(SEP, item) EOF { () }
