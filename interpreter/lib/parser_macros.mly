(* The macros of the grammar: declarations of pattern macros and their uses
   (macros.uses). Menhir joins this file with parser.mly, whose header holds the
   helpers of the actions.

   A [MACRO_TOKEN] is any token but a bracket, [$] and a separator, which
   stands for itself. The driver offers a token as one wherever the grammar
   accepts it, which is only among the matchers of a pattern, the items of a
   template and the tokens of a use's groups. *)

%%

(* Declarations (macros.syntax-declarations, macros.patterns and macros.templates) *)

%public syntax_decl:
  | SYNTAX name = lower_name
    LBRACE arms = separated_list(SEP, macro_arm) RBRACE
    { Syntax { name; arms } }

macro_arm:
  | pattern = arm_group block = option(trailing_fragment) FAT_ARROW
    template = template
    { { pattern; block; template } }

arm_group:
  | LPAREN ms = trees(matcher) RPAREN
    { node (Group (Paren, ms, loc $startpos($3))) $startpos }
  | LBRACKET ms = trees(matcher) RBRACKET
    { node (Group (Bracket, ms, loc $startpos($3))) $startpos }

trailing_fragment:
  | DOLLAR n = lower_name COLON k = lower_name { (n, k) }

(* Trees, among which separators stand for themselves. *)
trees(X):
  | { [] }
  | x = X xs = trees(X) { x :: xs }
  | SEP xs = trees(X) { node (Token A_sep) $startpos :: xs }

group(X):
  | LPAREN xs = trees(X) RPAREN
    { node (Group (Paren, xs, loc $startpos($3))) $startpos }
  | LBRACKET xs = trees(X) RBRACKET
    { node (Group (Bracket, xs, loc $startpos($3))) $startpos }
  | LBRACE xs = trees(X) RBRACE
    { node (Group (Brace, xs, loc $startpos($3))) $startpos }

(* Which words are kinds is decided after parsing (macros.patterns). *)
matcher:
  | DOLLAR n = lower_name COLON k = fragment_kind
    { node (Fragment (n, Some k)) $startpos }
  | DOLLAR LPAREN ms = trees(matcher) RPAREN s = repeat_sep o = repeat_op
    { node (Repeat (ms, s, o)) $startpos }
  | g = group(matcher) { g }
  | t = MACRO_TOKEN { node (Token t) $startpos }

fragment_kind:
  | n = lower_name { n }
  | n = upper_name { n }
  | TYPE { node "type" $startpos }

repeat_sep:
  | { None }
  | COMMA { Some "," }
  | SEP { Some ";" }

repeat_op:
  | STAR { "*" }
  | PLUS { "+" }

(* A template runs to the separator that ends its arm. *)
template:
  | t = template_item { [ t ] }
  | t = template_item ts = template { t :: ts }

template_item:
  | DOLLAR n = lower_name { node (Fragment (n, None)) $startpos }
  | DOLLAR LPAREN ts = trees(template_item) RPAREN s = repeat_sep o = repeat_op
    { node (Repeat (ts, s, o)) $startpos }
  | g = group(template_item) { g }
  | t = MACRO_TOKEN { node (Token t) $startpos }

(* Uses (macros.uses): the [!] and the group of a use, whose tokens are
   read by the macro's arms once its name is resolved. *)

%public macro_group:
  | BANG LPAREN ts = trees(token_tree) RPAREN
    { node (Group (Paren, ts, loc $startpos($4))) $startpos($2) }
  | BANG LBRACKET ts = trees(token_tree) RBRACKET
    { node (Group (Bracket, ts, loc $startpos($4))) $startpos($2) }

(* A use's trailing block, on the line where its group ends. *)
%public macro_block:
  | LBRACE ts = trees(token_tree) RBRACE
    { node (Group (Brace, ts, loc $startpos($3))) $startpos }

token_tree:
  | g = group(token_tree) { g }
  | t = MACRO_TOKEN { node (Token t) $startpos }
