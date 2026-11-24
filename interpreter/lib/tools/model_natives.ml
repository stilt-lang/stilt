(* The natives of std that the calculus writes in its own terms: writing the output and
   standard error, reading stdin, the natives that give an [Option] as the calculus's list
   of none or one value, parsing numbers, and the prelude's functions that panic. *)

open Model_json
open Model_types
open Model_ops
open Model_forms

(* [io.read_line()] and [io.poll_line()]: the line at the start of the input, which the
   read takes from it, or [None] at its end (std.read-line). The model has the whole input
   when the program starts, so a line is always waiting for [poll_line] (std.io). *)
let rec read_line cx (e : Tast.expr) =
  cx.reads_input <- true;
  option_of_list cx e (tag "list" [ Str "str" ])
    (on_world "readLine" [] [])
    Fun.id

(* A native that gives an [Option] as the calculus's list of none or one value [l], of
   type [l_ty]: [None] for an empty list, else [Some] of its element, with [around]
   given the choice, to run what comes between. *)
and option_of_list cx (e : Tast.expr) l_ty l around =
  let n = temp "option" e.loc and i64 = prelude_ty "i64" in
  let zero = int_lit i64 "0" ~negated:false in
  let none =
    binary Eq i64 i64 (op (tag "list" [ Str "len" ]) [ var_e n ]) zero
  in
  let some = option cx e.ty "Some" [ tag "index" [ var_e n; zero ] ] in
  let pick = tag "if" [ none; ty cx e.ty; option cx e.ty "None" []; some ] in
  tag "letIn" [ Str n; l_ty; l; around pick ]

(* [io.read_all()]: the rest of the input, which the read takes (std.io). *)
let read_all cx (_ : Tast.expr) =
  cx.reads_input <- true;
  on_world "readAll" [] []

(* A native of [str] that gives an [Option], as the calculus's list of none or one value:
[s.find(sub)] and [s.rfind(sub)], the byte offset of the first or the last occurrence
(std.str-search), and [str.from_utf8(bytes)] and [str.from_code_point(p)], the string
they stand for (std.code-points). *)
let option_native cx (e : Tast.expr) name args =
  let calculus =
    match name with
    | "from_utf8" -> "fromUtf8"
    | "from_code_point" -> "fromCodePoint"
    | name -> name
  in
  let list = tag "list" [ Model_types.ty cx (option_payload e.ty) ] in
  option_of_list cx e list (op (tag "list" [ Str calculus ]) args) Fun.id

(* [s.strip_prefix(p)] and [s.strip_suffix(p)]: the rest of [s] when it starts or ends
   with [p], and [None] otherwise (std.str-search), [s] and [p] evaluated in order. *)
let strip cx (e : Tast.expr) name args =
  let s = temp "strip" e.loc and p = temp "strip-affix" e.loc in
  let i64 = prelude_ty "i64" and str = prelude_ty "str" in
  let len x = op (Str "len") [ x ] in
  let prefix = name = "strip_prefix" in
  let test =
    op
      (tag "search" [ Str (if prefix then "startsWith" else "endsWith") ])
      [ var_e s; var_e p ]
  in
  let from, upto =
    if prefix then (len (var_e p), len (var_e s))
    else
      ( int_lit i64 "0" ~negated:false,
        binary Sub i64 i64 (len (var_e s)) (len (var_e p)) )
  in
  let rest = op (Str "slice") [ var_e s; from; upto ] in
  let pick =
    tag "if"
      [
        test;
        ty cx e.ty;
        option cx e.ty "Some" [ rest ];
        option cx e.ty "None" [];
      ]
  in
  match args with
  | [ a; b ] ->
      tag "letIn"
        [ Str s; ty cx str; a; tag "letIn" [ Str p; ty cx str; b; pick ] ]
  | _ -> outside "the function str.%s" name

(* The natives of [str] that give an [Option], by name. *)
(* [s.split_once(sep)] and [s.rsplit_once(sep)]: the text before and after the
   occurrence that [find] or [rfind] finds, or [None] (std.str-search). *)
let split_once cx (e : Tast.expr) name args =
  let s = temp "split" e.loc and sep = temp "split-sep" e.loc in
  let at = temp "split-at" e.loc and hits = temp "split-hits" e.loc in
  let i64 = prelude_ty "i64" in
  let found =
    op
      (tag "list" [ Str (if name = "split_once" then "find" else "rfind") ])
      [ var_e s; var_e sep ]
  in
  let zero = int_lit i64 "0" ~negated:false in
  let len x = op (Str "len") [ x ] in
  let after = binary Add i64 i64 (var_e at) (len (var_e sep)) in
  let parts =
    op (Str "tuple")
      [
        op (Str "slice") [ var_e s; zero; var_e at ];
        op (Str "slice") [ var_e s; after; len (var_e s) ];
      ]
  in
  let none =
    binary Eq i64 i64 (op (tag "list" [ Str "len" ]) [ var_e hits ]) zero
  in
  let first = tag "index" [ var_e hits; zero ] in
  let some =
    option cx e.ty "Some" [ tag "letIn" [ Str at; ty cx i64; first; parts ] ]
  in
  let pick = tag "if" [ none; ty cx e.ty; option cx e.ty "None" []; some ] in
  let str = ty cx (prelude_ty "str") in
  match args with
  | [ a; b ] ->
      tag "letIn"
        [
          Str s;
          str;
          a;
          tag "letIn"
            [
              Str sep;
              str;
              b;
              tag "letIn" [ Str hits; tag "list" [ ty cx i64 ]; found; pick ];
            ];
        ]
  | _ -> outside "the function str.%s" name

let optional_natives =
  [
    "find";
    "rfind";
    "from_utf8";
    "from_code_point";
    "strip_prefix";
    "strip_suffix";
    "split_once";
    "rsplit_once";
  ]

let optional cx e name args =
  match name with
  | "strip_prefix" | "strip_suffix" -> strip cx e name args
  | "split_once" | "rsplit_once" -> split_once cx e name args
  | _ -> option_native cx e name args

(* An integer type's natives that give an [Option]: [checked_add], [checked_sub] and
   [checked_mul], the exact result when it fits (std.integers), [x.to_T()] to a type
   that doesn't hold every value, the value when it fits, and [x.to_T()] from a float,
   its truncation when it fits (numbers.conversions), as the calculus's list of none or
   one integer. *)
let int_optional cx (e : Tast.expr) source name args =
  let payload = option_payload e.ty in
  let target =
    match int_kind payload with
    | Some k -> k
    | None -> outside "the function %s.%s" source name
  in
  let list =
    match name with
    | "checked_add" | "checked_sub" | "checked_mul" ->
        let o = String.sub name 8 (String.length name - 8) in
        op (tag "list" [ tag "checked" [ Str o; Str source ] ]) args
    | _ when source = "f32" || source = "f64" ->
        op (tag "list" [ tag "truncate" [ Str target ] ]) args
    | _ -> op (tag "list" [ tag "narrow" [ Str target ] ]) args
  in
  option_of_list cx e (tag "list" [ Model_types.ty cx payload ]) list Fun.id

(* Whether a native of an integer type gives an [Option] that {!int_optional} exports. *)
let int_optional_native name (result : Types.ty) =
  List.mem name [ "checked_add"; "checked_sub"; "checked_mul" ]
  || String.starts_with ~prefix:"to_" name
     &&
     match norm result with
     | Types.Con (i, [ p ]) -> i = option_item && int_kind p <> None
     | _ -> false

(* [s.to_T()] for a numeric type [T]: an integer or a float type's test of whether the
   string parses, then its value (numbers.parsing), of the exported string [s] evaluated
   once. *)
let parse cx (e : Tast.expr) s =
  let parses, parsed, k =
    match int_kind (option_payload e.ty) with
    | Some k -> ("parses", "parsed", k)
    | None ->
        ("fparses", "fparsed", Option.get (float_kind (option_payload e.ty)))
  in
  let n = temp "parse" e.loc in
  let parsed = op (tag parsed [ Str k ]) [ var_e n ] in
  let pick =
    tag "if"
      [
        op (tag parses [ Str k ]) [ var_e n ];
        ty cx e.ty;
        option cx e.ty "Some" [ parsed ];
        option cx e.ty "None" [];
      ]
  in
  tag "letIn" [ Str n; Str "str"; s; pick ]

(* The prelude's functions that panic, with the kind each panics with: [panic(msg)],
   [unreachable()], and [unwrap] and [expect] of a [None] or an [Err]
   (effects.panic-kinds, std.option-result-and-ordering). *)
let panicking =
  [
    ("panic", "explicit");
    ("unreachable", "unreachable");
    ("unwrap_failed", "unwrap");
    ("expect_failed", "unwrap");
  ]

(* Whether a native of std gives an [Option] that {!option_call} exports, by its owner,
   its name and the call's type: [s.to_T()] for a numeric [T] (numbers.parsing), an
   integer type's [checked_*] and narrowing [to_T()], a float's [to_T()] to an integer
   type, and the natives of [str] in
   {!optional_natives}. *)
let gives_option (owner : Hir.item) name t =
  match owner with
  | { home = "std.prelude"; name = "str" } ->
      String.starts_with ~prefix:"to_" name
      && (int_kind (option_payload t) <> None
         || float_kind (option_payload t) <> None)
      || List.mem name optional_natives
  | { home = "std.prelude"; name = k } ->
      (List.mem k Types.integer_types || k = "f32" || k = "f64")
      && int_optional_native name t
  | _ -> false

(* A call [e] of a native that {!gives_option}, of its exported operands. *)
let option_call cx (e : Tast.expr) (owner : Hir.item) name args =
  match (owner.name, args) with
  | "str", [ s ] when String.starts_with ~prefix:"to_" name -> parse cx e s
  | "str", _ -> optional cx e name args
  | k, _ -> int_optional cx e k name args

(* A call [e] of a native of std that the calculus writes in its own terms, of its
   operands exported by [exported ()]: [print], [eprint], [io.write] and [io.ewrite], which
   append to the output or to standard error (std.io); [io.flush()], which changes only
   when the output reaches stdout, never what it holds, all that a run shows
   (program.output-flushing); the reads of the input; [cli.args()], the program's
   arguments, of which the model's runner gives none (std.cli); and the prelude's
   functions that panic, their message or detail evaluated first (effects.panic-kinds).
   None for any other function. *)
let std_call cx (e : Tast.expr) (i : Hir.item) exported =
  match (i.home, i.name) with
  | "std.prelude", ("print" | "eprint") | "std.io", ("write" | "ewrite") -> (
      let err = i.name = "eprint" || i.name = "ewrite" in
      match exported () with
      | [ s ] -> Some (written ~err ~newline:(i.home = "std.prelude") s)
      | _ -> outside "%s" i.name)
  | "std.io", "flush" -> Some unit_e
  | "std.io", ("read_line" | "poll_line") -> Some (read_line cx e)
  | "std.io", "read_all" -> Some (read_all cx e)
  | "std.cli", "args" -> Some (tag "list" [ Str "str"; Arr [] ])
  | "std.prelude", name when List.mem_assoc name panicking ->
      Some (op (tag "panic" [ Str (List.assoc name panicking) ]) (exported ()))
  | _ -> None
