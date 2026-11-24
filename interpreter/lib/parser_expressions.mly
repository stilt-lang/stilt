(* The statements, blocks and expressions of the grammar of core Stilt. Menhir
   joins this file with parser.mly, whose header holds the helpers of the
   actions. *)

%%

(* Statements and blocks *)

%public block:
  | LBRACE stmts = separated_list(SEP, stmt) RBRACE { stmts }

%public stmt:
  | LET b = binding { node (Let b) $startpos }
  | VAR b = binding { node (Var b) $startpos }
  | ASSERT e = expr { node (Assert e) $startpos }
  | YIELD e = expr { node (Yield e) $startpos }
  | place = expr op = assign_op value = expr
    { node (Assign (op, place, value)) $startpos }
  | e = expr { node (Expr e) $startpos }

binding:
  | pattern = pattern annotation = option(preceded(COLON, ty)) EQ value = expr
    { { pattern; annotation; value } }

assign_op:
  | EQ { None }
  | PLUS_EQ { Some Add }
  | MINUS_EQ { Some Sub }
  | STAR_EQ { Some Mul }
  | SLASH_EQ { Some Div }
  | PERCENT_EQ { Some Rem }
  | PLUS_WRAP_EQ { Some Add_wrap }
  | MINUS_WRAP_EQ { Some Sub_wrap }
  | STAR_WRAP_EQ { Some Mul_wrap }
  | AMP_EQ { Some Bit_and }
  | PIPE_EQ { Some Bit_or }
  | CARET_EQ { Some Bit_xor }
  | LT_LT_EQ { Some Shl }
  | GT_GT_EQ { Some Shr }

(* Expressions. [expr] is the full grammar. [head] is the grammar of the heads
   of expressions.heads, which leaves out every form that holds a [{] of its own
   outside parentheses and brackets. Both share [expr_core] and
   [postfix_core], and differ in their primaries. *)

%public expr:
  | e = expr_core(expr, primary) { e }
  | TRY operand = expr CATCH LBRACE arms = arms(catch_arm(expr)) RBRACE
    { node (Try (operand, Some arms)) $startpos }

head:
  | e = expr_core(head, head_primary) { e }

expr_core(E, PRIMARY):
  | e = postfix(PRIMARY) { e }
  | MINUS e = E %prec PREFIX { node (Unary (Neg, e)) $startpos }
  | BANG e = E %prec PREFIX { node (Unary (Not, e)) $startpos }
  | a = E op = binary b = E { node (Binary (op, a, b)) $startpos }
  | a = E ELSE b = E { node (Else (a, b)) $startpos }
  | TRY e = E %prec LEVEL14 { node (Try (e, None)) $startpos }
  | TRY e = E CATCH arm = catch_arm(E) { node (Try (e, Some [ arm ])) $startpos }
  | RAISE e = E %prec LEVEL14 { node (Raise e) $startpos }
  | RETURN %prec LEVEL14 { node (Return None) $startpos }
  | RETURN e = E %prec LEVEL14 { node (Return (Some e)) $startpos }
  | BREAK { node Break $startpos }
  | CONTINUE { node Continue $startpos }
  | PIPE ps = comma_list(closure_param) PIPE body = E %prec LEVEL14
    { node (Closure (ps, body)) $startpos }
  | PIPE_PIPE body = E %prec LEVEL14 { node (Closure ([], body)) $startpos }
  (* handlers.resuming *)
  | RESUME LPAREN e = option(expr) RPAREN { node (Resume e) $startpos }

%inline binary:
  | PLUS { Add }
  | MINUS { Sub }
  | STAR { Mul }
  | SLASH { Div }
  | PERCENT { Rem }
  | PLUS_WRAP { Add_wrap }
  | MINUS_WRAP { Sub_wrap }
  | STAR_WRAP { Mul_wrap }
  | EQ_EQ { Eq }
  | BANG_EQ { Ne }
  | LT { Lt }
  | LT_EQ { Le }
  | GT { Gt }
  | GT_EQ { Ge }
  | AMP_AMP { And }
  | PIPE_PIPE { Or }
  | AMP { Bit_and }
  | PIPE { Bit_or }
  | CARET { Bit_xor }
  | LT_LT { Shl }
  | GT_GT { Shr }

(* An [inout] parameter is a name, not a pattern (expressions.inout-closure-parameters). *)
closure_param:
  | pattern = alt annotation = option(preceded(COLON, ty))
    { { mode = Let; pattern; annotation } }
  | INOUT n = lower_name annotation = option(preceded(COLON, ty))
    { { mode = Inout; pattern = { desc = P_bind n.desc; loc = n.loc }; annotation } }

(* A catch-all has no guard (effects.catch-alls-need-reason), so an arm has a guard or a reason, never
   both. *)
catch_arm(E):
  | pattern = pattern guard = option(preceded(IF, E)) FAT_ARROW body = E
    %prec LEVEL14
    { { pattern; guard; because = None; body } }
  | pattern = pattern BECAUSE reason = STRING FAT_ARROW body = E %prec LEVEL14
    { { pattern; guard = None; because = Some (node reason $startpos(reason)); body } }

match_arm:
  | pattern = pattern guard = option(preceded(IF, expr)) FAT_ARROW body = expr
    { { pattern; guard; because = None; body } }

(* Arms separated by terminators or commas, with an optional comma at the
   end. *)
arms(ARM):
  | { [] }
  | a = ARM { [ a ] }
  | a = ARM SEP rest = arms(ARM) { a :: rest }
  | a = ARM COMMA rest = arms(ARM) { a :: rest }

(* A postfix expression is a path of identifiers, such as [fs.read], or is
   built on another primary. Keeping the two apart lets a struct literal accept
   only a path before its [{] (expressions.struct-literals). *)
postfix(PRIMARY):
  | p = dotted { path_expr p }
  | e = built(PRIMARY) { e }

%inline dotted:
  | p = dotted_lower | p = dotted_upper { p }

(* A path that ends in a [lower] name: one of [lower] names only, which a
   macro's use names (macros.uses), or one with an [Upper] name. *)
%inline dotted_lower:
  | p = lower_dotted | p = mixed_lower { p }

lower_dotted:
  | n = lower_name { [ n ] }
  | p = lower_dotted DOT n = lower_name { p @ [ n ] }

mixed_lower:
  | p = dotted_upper DOT n = lower_name { p @ [ n ] }
  | p = mixed_lower DOT n = lower_name { p @ [ n ] }

dotted_upper:
  | n = upper_name { [ n ] }
  | p = dotted DOT n = upper_name { p @ [ n ] }

built(PRIMARY):
  | e = PRIMARY { e }
  | p = dotted DOT n = INT { node (Field (path_expr p, node n $startpos(n))) $startpos }
  (* tasks.task-functions: [t.await()], whose [t] is a path. *)
  | p = dotted DOT AWAIT
    { node (Field (path_expr p, node "await" $startpos($3))) $startpos }
  | e = built(PRIMARY) DOT m = member { node (Field (e, m)) $startpos }
  (* macros.splices and macros.spreads: in a quote, a member that a splice names. *)
  | p = dotted DOT s = q_splice { node (Q_member (path_expr p, s)) $startpos }
  | e = built(PRIMARY) DOT s = q_splice { node (Q_member (e, s)) $startpos }
  | f = postfix(PRIMARY) LPAREN args = comma_list(arg) RPAREN
    { node (Call (f, args)) $startpos }
  | e = postfix(PRIMARY) LBRACKET i = expr RBRACKET { node (Index (e, i)) $startpos }

(* [await] is a keyword, read as a member's name after [.]. *)
member:
  | n = LIDENT | n = UIDENT | n = INT { node n $startpos }
  | AWAIT { node "await" $startpos }

arg:
  | value = expr { { inout = false; value } }
  | INOUT value = expr { { inout = true; value } }
  | value = spread { { inout = false; value } }
  | value = q_spread { { inout = false; value } }

(* An element of a tuple or a list, which may be a spread (variadics.spread-expressions),
   or in a quote a spliced list (macros.splices and macros.spreads). *)
elem:
  | e = expr { e }
  | e = spread { e }
  | e = q_spread { e }

spread:
  | DOT_DOT e = expr { node (Spread e) $startpos }

(* The fields of a literal after its first, or after an update's base. *)
record_rest:
  | { [] }
  | COMMA { [] }
  | COMMA f = record_field rest = record_rest { f :: rest }

field_init:
  | field = lower_name COLON value = expr { { field; value } }
  | field = lower_name { { field; value = node (Name field.desc) $startpos } }

(* A field of a literal, or in a quote one that a splice names, or a spread
   of fields (macros.splices and macros.spreads). *)
record_field:
  | f = field_init { Field_init f }
  | s = q_splice COLON value = expr { Spliced_field (s, value) }
  | s = q_spread { Spread_fields s }

primary:
  | e = head_primary { e }
  | p = dotted_upper LBRACE fields = comma_list(record_field) RBRACE
    { struct_literal p None fields $startpos }
  | SELF_TYPE LBRACE fields = comma_list(record_field) RBRACE
    { struct_literal [ node "Self" $startpos ] None fields $startpos }
  (* records.update *)
  | p = dotted_upper LBRACE DOT_DOT base = expr fields = record_rest RBRACE
    { struct_literal p (Some base) fields $startpos }
  | SELF_TYPE LBRACE DOT_DOT base = expr fields = record_rest RBRACE
    { struct_literal [ node "Self" $startpos ] (Some base) fields $startpos }
  (* records.anonymous-literals and records.update: a [{] followed by a field name and a [:], or by
     [..], begins a record, where a block would otherwise begin, and in a
     quote so does one followed by a splice and a [:], or by a spread
     (macros.splices and macros.spreads). *)
  | LBRACE n = lower_name COLON v = expr fields = record_rest RBRACE
    { record_literal None (Field_init { field = n; value = v } :: fields) $startpos }
  | LBRACE s = q_splice COLON v = expr fields = record_rest RBRACE
    { record_literal None (Spliced_field (s, v) :: fields) $startpos }
  | LBRACE s = q_spread fields = record_rest RBRACE
    { record_literal None (Spread_fields s :: fields) $startpos }
  | LBRACE DOT_DOT base = expr fields = record_rest RBRACE
    { record_literal (Some base) fields $startpos }
  | b = block { node (Block b) $startpos }
  (* macros.quote *)
  | q = quote { q }
  | e = if_expr { e }
  | MATCH scrutinee = head LBRACE arms = arms(match_arm) RBRACE
    { node (Match (scrutinee, arms)) $startpos }
  | LOOP body = block { node (Loop body) $startpos }
  | WHILE cond = head body = block { node (While (cond, body)) $startpos }
  | FOR p = pattern IN it = iterable body = block { node (For (p, it, body)) $startpos }
  (* macros.uses: a use's trailing block, which a head leaves out. *)
  | p = lower_dotted g = macro_group b = macro_block
    { node (Macro_use (p, [ g; b ])) $startpos }
  (* handlers.handler-literals and handlers.with: forms with blocks of their own, which no head
     holds. *)
  | HANDLER e = effect_ref ret = option(preceded(ARROW, ty))
    LBRACE fs = separated_list(SEP, fn_decl) RBRACE
    { node (Handler (e, ret, fs)) $startpos }
  | WITH hs = nonempty_comma_list(head) body = block { node (With (hs, body)) $startpos }
  (* shared.when *)
  | WHEN names = nonempty_comma_list(lower_name) body = block
    { node (When (names, body)) $startpos }
  (* c.unsafe-because: a block that runs unsafe code, with its reason. *)
  | UNSAFE BECAUSE reason = STRING body = block
    { node (Unsafe (node reason $startpos(reason), body)) $startpos }
  (* meta.staging-annotations: a staging annotation, written once before the [if] of a
     chain, a [match] or a [for]. *)
  | COMPTIME e = if_expr { node (Comptime e) $startpos }
  | COMPTIME MATCH scrutinee = head LBRACE arms = arms(match_arm) RBRACE
    { node (Comptime (node (Match (scrutinee, arms)) $startpos($2))) $startpos }
  | COMPTIME FOR p = pattern IN it = iterable body = block
    { node (Comptime (node (For (p, it, body)) $startpos($2))) $startpos }

if_expr:
  | IF cond = head body = block %prec below_else
    { node (If (cond, body, None)) $startpos }
  | IF cond = head body = block ELSE e = else_branch
    { node (If (cond, body, Some e)) $startpos }
  (* meta.bound-tests: a bound test, the whole condition of its [if]. *)
  | IF t = upper_name COLON bs = bounds body = block %prec below_else
    { node (If (node (Bound_test (t, bs)) $startpos(t), body, None)) $startpos }
  | IF t = upper_name COLON bs = bounds body = block ELSE e = else_branch
    { node (If (node (Bound_test (t, bs)) $startpos(t), body, Some e)) $startpos }
  | IF LET p = pattern EQ e = head body = block %prec below_else
    { node (If_let (p, e, body, None)) $startpos }
  | IF LET p = pattern EQ e = head body = block ELSE alt = else_branch
    { node (If_let (p, e, body, Some alt)) $startpos }

else_branch:
  | b = block { node (Block b) $startpos }
  | e = if_expr { e }

iterable:
  | e = head { Iter e }
  | a = head DOT_DOT b = head { Range (a, b, Exclusive) }
  | a = head DOT_DOT_EQ b = head { Range (a, b, Inclusive) }

(* The primaries other than paths of identifiers. *)
head_primary:
  | i = INT { node (Int i) $startpos }
  | f = FLOAT { node (Float f) $startpos }
  | s = STRING { node (Str s) $startpos }
  | s = interpolated { node (Interpolated s) $startpos }
  | TRUE { node (Bool true) $startpos }
  | FALSE { node (Bool false) $startpos }
  | SELF { node Self_value $startpos }
  | SELF_TYPE { node Self_type $startpos }
  | QUESTION { node Hole $startpos }
  | DOT m = key_member
    { node (Field (node Key_root $startpos, m)) $startpos }
  | LPAREN es = comma_list_t(elem) RPAREN
    { parenthesized ~spread:is_spread ~tuple:(fun es -> Tuple es) es $startpos }
  | LBRACKET es = comma_list(elem) RBRACKET { node (List es) $startpos }
  (* macros.uses *)
  | p = lower_dotted g = macro_group { node (Macro_use (p, [ g ])) $startpos }
  (* macros.splices *)
  | s = q_splice { s }

key_member:
  | n = LIDENT | n = INT { node n $startpos }

interpolated:
  | head = STRING_HEAD splices = splices { segments head splices }

splices:
  | s = splice tail = STRING_TAIL { [ (s, tail) ] }
  | s = splice mid = STRING_MID rest = splices { (s, mid) :: rest }

splice:
  | e = expr spec = option(FORMAT) { Splice (e, spec) }

(* Quotes (macros.quote and macros.splices). A quote keeps its contents as tokens
   beside its tree. Its splices and spreads stand only inside a quote, where
   the driver offers [$] as [SPLICE]. *)

quote:
  | QUOTE b = block
    { quote (Quote_block b) $startpos(b) $endpos(b) $startpos }
  | QUOTE TYPE LBRACE t = ty RBRACE
    { quote (Quote_type t) $startpos($3) $startpos($5) $startpos }
  | QUOTE PATTERN LBRACE p = pattern RBRACE
    { quote (Quote_pattern p) $startpos($3) $startpos($5) $startpos }
  | QUOTE FIELD LBRACE f = record_field RBRACE
    { quote (Quote_field f) $startpos($3) $startpos($5) $startpos }

%public q_splice:
  | SPLICE n = lower_name
    { node (Q_splice (node (Name n.desc) $startpos(n))) $startpos }
  | SPLICE LPAREN e = expr RPAREN { node (Q_splice e) $startpos }

q_spread:
  | SPLICE DOT_DOT n = lower_name
    { node (Q_spread (node (Name n.desc) $startpos(n))) $startpos }
  | SPLICE DOT_DOT LPAREN e = expr RPAREN { node (Q_spread e) $startpos }
