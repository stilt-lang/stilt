(* The patterns of the grammar of core Stilt. Menhir joins this file with
   parser.mly, whose header holds the helpers of the actions. *)

%%

(* Patterns *)

%public pattern:
  | p = alt { p }
  | p = alt PIPE ps = separated_nonempty_list(PIPE, alt)
    { node (P_or (p :: ps)) $startpos }

%public alt:
  | UNDERSCORE { node P_wild $startpos }
  | n = LIDENT { node (P_bind n) $startpos }
  | i = INT { node (P_int i) $startpos }
  | MINUS i = INT { node (P_int ("-" ^ i)) $startpos }
  | s = STRING { node (P_str s) $startpos }
  | TRUE { node (P_bool true) $startpos }
  | FALSE { node (P_bool false) $startpos }
  | p = upper_path { node (P_path p) $startpos }
  | p = upper_path LPAREN ps = nonempty_comma_list(pattern) RPAREN
    { node (P_variant (p, ps)) $startpos }
  | p = upper_path LBRACE fs = field_patterns RBRACE
    { record_pattern (Some p) fs $startpos }
  (* records.anonymous-patterns: an anonymous record has a field, so its pattern names
     one or ends with [..], and [catch {}] keeps its empty arms. *)
  | LBRACE fs = some_field_patterns RBRACE
    { record_pattern None fs $startpos }
  | LPAREN ps = comma_list_t(pattern) RPAREN
    { parenthesized ~tuple:(fun ps -> P_tuple ps) ps $startpos }
  | LBRACKET l = list_pattern RBRACKET { node (P_list (fst l, snd l)) $startpos }
  (* macros.uses: a use takes no trailing block in a pattern. *)
  | p = lower_path g = macro_group { node (P_macro (p, g)) $startpos }
  (* macros.splices *)
  | s = q_splice { node (P_splice s) $startpos }

field_patterns:
  | { ([], false) }
  | DOT_DOT option(COMMA) { ([], true) }
  | f = field_pattern { ([ f ], false) }
  | f = field_pattern COMMA rest = field_patterns { (f :: fst rest, snd rest) }

some_field_patterns:
  | DOT_DOT option(COMMA) { ([], true) }
  | f = field_pattern { ([ f ], false) }
  | f = field_pattern COMMA rest = field_patterns { (f :: fst rest, snd rest) }

(* In a quote, a splice may name a field (macros.splices and macros.spreads). *)
field_pattern:
  | field = lower_name COLON pattern = pattern { Field_pattern { field; pattern } }
  | field = lower_name
    { Field_pattern { field; pattern = node (P_bind field.desc) $startpos } }
  | s = q_splice COLON p = pattern { Spliced_field_pattern (s, p) }
  | s = q_splice { Spliced_field_pattern (s, node (P_splice s) $startpos) }

list_pattern:
  | { ([], Exact) }
  | DOT_DOT option(COMMA) { ([], Rest) }
  | DOT_DOT n = lower_name option(COMMA) { ([], Rest_bind n) }
  | p = pattern { ([ p ], Exact) }
  | p = pattern COMMA rest = list_pattern { (p :: fst rest, snd rest) }
