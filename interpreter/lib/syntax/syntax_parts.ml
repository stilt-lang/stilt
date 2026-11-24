(* The parts of a file with a syntax error, each read alone, and what a part
   that breaks declares (errors.broken-parts), and the extent of each item, which
   tells which body an error lies in (program.errors-in-bodies). *)

open Ast

type token = Lexer.token

type kind =
  | Fn
  | Const
  | Type
  | Test
  | Impl
  | Trait
  | Syntax
  | Effect
  | Macro
  | Other

type extent = {
  kind : kind;
  first : loc;
  last : loc;
  name : loc;
  block : loc option;
  members : extent list;
}

let loc_of (t : token) = { line = t.line; col = t.col }
let synthetic token (at : token) = { at with token }

(* The tokens that begin a part, given the token after them: [macro] and a
   [meta] that [use] follows among them (errors.parts, macros.procedural-declarations and
   macros.meta-use). [meta] is a contextual keyword, so the lexer gives it as a name
   (lexical.contextual-keywords). *)
let item_start (token : Token.t) (next : Token.t option) =
  Syntax_foreign.starts ~block:false token next
  ||
  match (token, next) with
  | ( ( USE | IMPL | PUB | EXTERN | FN | TYPE | TRAIT | CONST | TEST | SYNTAX
      | EFFECT | MACRO | DOC _ | MISPLACED_DOC ),
      _ )
  | (META | LIDENT "meta"), Some USE ->
      true
  | _ -> false

let member_start (token : Token.t) (next : Token.t option) =
  Syntax_foreign.starts ~block:true token next
  ||
  match token with
  | FN | CONST | PUB | DOC _ | MISPLACED_DOC -> true
  | _ -> false

(* The bracket depth after [t]: a closing bracket closes the innermost open
   bracket, whatever its kind. *)
let step depth (t : token) =
  match t.token with
  | LPAREN | LBRACKET | LBRACE -> depth + 1
  | RPAREN | RBRACKET | RBRACE -> max 0 (depth - 1)
  | _ -> depth

(* The parts of the tokens from [lo] to [hi], as ranges: a part ends at each
   separator outside brackets that a token accepted by [starts] follows. *)
let cut ~starts (ts : token array) lo hi =
  let rec go i depth start acc =
    if i >= hi then List.rev ((start, hi) :: acc)
    else
      let t = ts.(i) in
      let next j = if j < hi then Some ts.(j).token else None in
      if
        t.token = SEP && depth = 0
        && i + 1 < hi
        && starts ts.(i + 1).token (next (i + 2))
      then go (i + 1) depth (i + 1) ((start, i) :: acc)
      else go (i + 1) (step depth t) start acc
  in
  if lo >= hi then [] else go lo 0 lo []

(* The first token from [lo] to [hi] outside brackets that [opens] accepts,
   given the token before it. *)
let opener (ts : token array) lo hi opens =
  let rec go i depth previous =
    if i >= hi then None
    else
      let t = ts.(i) in
      if depth = 0 && opens previous t.token then Some i
      else go (i + 1) (step depth t) (Some t.token)
  in
  go lo 0 None

let body_opener ts lo hi =
  opener ts lo hi (fun previous token ->
      token = EQ || (token = LBRACE && previous <> Some SLASH))

let block_opener ts lo hi = opener ts lo hi (fun _ token -> token = LBRACE)

(* The index of the bracket that closes the [{] at [b], or [hi]. *)
let block_close (ts : token array) b hi =
  let rec go i depth =
    if i >= hi then hi
    else
      let d = step depth ts.(i) in
      if d = 0 then i else go (i + 1) d
  in
  go (b + 1) 1

(* The first token after the doc comments from [lo]. *)
let rec after_docs (ts : token array) lo hi =
  if lo < hi then
    match ts.(lo).token with
    | DOC _ | MISPLACED_DOC -> after_docs ts (lo + 1) hi
    | _ -> lo
  else lo

(* The token after the [pub] of the item from [first], if it has one. *)
let after_pub (ts : token array) first hi =
  if first < hi && ts.(first).token = PUB then first + 1 else first

(* Whether the item from [first] is written [extern] (c.exported-functions; c.foreign-functions). *)
let written_extern (ts : token array) first hi =
  let i = after_pub ts first hi in
  i < hi && ts.(i).token = EXTERN

(* The keyword of the item from [first], after its [pub] and its [extern]. *)
let keyword (ts : token array) first hi =
  let i = after_pub ts first hi in
  if written_extern ts first hi then i + 1 else i

(* What the item from [lo] to [hi] is, with its name: an identifier of the
   right case after [fn], [const] and [trait], and the keyword of a test or an
   impl. *)
let classify (ts : token array) lo hi =
  let first = after_docs ts lo hi in
  let kw = keyword ts first hi in
  let next = if kw + 1 < hi then Some ts.(kw + 1).token else None in
  match if kw < hi then Syntax_foreign.kind ts kw hi else None with
  | Some (kw, foreign) ->
      ( first,
        kw,
        match foreign with `Fn -> Fn | `Type -> Type | `Trait -> Trait )
  | None ->
      let kind =
        if kw >= hi then Other
        else
          match (ts.(kw).token, next) with
          | FN, Some (LIDENT _ | UIDENT _) -> Fn
          | CONST, Some (UIDENT _ | LIDENT _) -> Const
          | TYPE, Some (UIDENT _) -> Type
          | TRAIT, Some (UIDENT _) -> Trait
          | SYNTAX, Some (LIDENT _) -> Syntax
          | EFFECT, Some (UIDENT _) -> Effect
          | MACRO, Some (LIDENT _) -> Macro
          | TEST, _ -> Test
          | IMPL, _ -> Impl
          | _ -> Other
      in
      (first, kw, kind)

let rec extent (ts : token array) (lo, hi) =
  let first, kw, kind = classify ts lo hi in
  let name =
    match kind with
    | Fn | Const | Type | Trait | Syntax | Effect | Macro -> loc_of ts.(kw + 1)
    | Test | Impl -> loc_of ts.(kw)
    | Other -> loc_of ts.(min first (hi - 1))
  in
  let block, members =
    match kind with
    | Impl | Trait -> (
        match block_opener ts kw hi with
        | Some b ->
            let close = block_close ts b hi in
            ( Some (loc_of ts.(b)),
              List.map (extent ts) (cut ~starts:member_start ts (b + 1) close)
            )
        | None -> (None, []))
    | Fn | Const | Type | Test | Syntax | Effect | Macro | Other -> (None, [])
  in
  {
    kind;
    first = loc_of ts.(min first (hi - 1));
    last = loc_of ts.(hi - 1);
    name;
    block;
    members;
  }

(* The tokens of a file, and where its code ends: before its [EOF], or at
   its end after a lexical error. *)
let code (lexed : Lexer.output) =
  let ts = Array.of_list lexed.tokens in
  let n = Array.length ts in
  let hi = if n > 0 && ts.(n - 1).token = EOF then n - 1 else n in
  (ts, hi)

let extents (lexed : Lexer.output) =
  let ts, hi = code lexed in
  List.map (extent ts) (cut ~starts:item_start ts 0 hi)

(* {1 Reading parts} *)

type reader = {
  file : string;
  ts : token array;
  lexical : Diagnostic.t option;
  mutable broken : loc list;
}

let slice (ts : token array) lo hi = Array.to_list (Array.sub ts lo (hi - lo))

(* The token after the tokens that end at [hi], where a part's synthetic end
   sits: the separator after it, the file's [EOF], or after a lexical error
   its last token. *)
let at_end r hi = r.ts.(min hi (Array.length r.ts - 1))

(* Parses tokens as a file, giving it or its error. *)
let parse r tokens =
  match Syntax.parse_part ~file:r.file tokens with
  | Ok m -> Ok m
  | Error (Some d) -> Error d
  | Error None -> Error (Option.get r.lexical)

let after (d : Diagnostic.t) (t : token) =
  compare (d.line, d.col) (t.line, t.col) > 0

(* A type that no name resolves to, which leaves a signature unknown. *)
let unknown at =
  { desc = Ty_named ([ { desc = "<unknown>"; loc = at } ], []); loc = at }

let name_of (t : token) =
  match t.token with
  | LIDENT s | UIDENT s | STRING s -> { desc = s; loc = loc_of t }
  | _ -> invalid_arg "Syntax_parts.name_of"

(* Where an item is parsed: alone as a file, or as the only member of a block
   whose header is given. [wrap at tokens] makes a file of the item's tokens,
   with synthetic tokens at [at], and [opened tokens] puts them in their place
   with no synthetic end, as a lexical error leaves them. *)
type place = {
  wrap : token -> token list -> token list;
  opened : token list -> token list;
  extract : module_ -> decl node option;
  member : bool;  (** Whether the item is a member, a function or constant. *)
}

let alone =
  {
    wrap = (fun at tokens -> tokens @ [ synthetic EOF at ]);
    opened = Fun.id;
    extract =
      (fun m ->
        match m.items with
        | [ { desc = Decl d; loc } ] -> Some { desc = d; loc }
        | _ -> None);
    member = false;
  }

let in_block header (lbrace : token) =
  {
    wrap =
      (fun at tokens ->
        header @ (lbrace :: tokens) @ [ synthetic RBRACE at; synthetic EOF at ]);
    opened = (fun tokens -> header @ (lbrace :: tokens));
    extract =
      (fun m ->
        match m.items with
        | [ { desc = Impl { members = [ d ]; _ }; _ } ]
        | [ { desc = Decl { kind = Trait { members = [ d ]; _ }; _ }; _ } ] ->
            Some d
        | _ -> None);
    member = true;
  }

(* Parses the part from [lo] to [hi] in its place. A part that the lexical
   error ends has that error, even if its tokens parse: what follows them is
   unknown. Its tokens are parsed in their place as they are, with no
   synthetic end, so that the error is the lexical one when the parser
   accepts every token, as for a file, even for a member whose body the
   error leaves open (errors.part-reports). *)
let parse_part r place lo hi =
  let ended = hi = Array.length r.ts && Option.is_some r.lexical in
  if ended then
    match parse r (place.opened (slice r.ts lo hi)) with
    | Ok _ -> Error (Option.get r.lexical)
    | result -> result
  else parse r (place.wrap (at_end r hi) (slice r.ts lo hi))

(* A function or a constant whose signature is unknown, so that every use of
   it is an error. *)
let unknown_signature name : fn_decl =
  {
    name;
    generics = [];
    params = [];
    ret = Some (unknown name.loc);
    projection = false;
    row = [];
    where_ = None;
    without = None;
    body = Some (Body ([], name.loc));
  }

let unknown_fn name : decl_kind = Fn (unknown_signature name)

let unknown_const name : decl_kind =
  Const
    {
      name;
      ty = unknown name.loc;
      value = Some { desc = Int "0"; loc = name.loc };
    }

let empty_block at = [ synthetic LBRACE at; synthetic RBRACE at ]
let zero at = [ synthetic EQ at; synthetic (INT "0") at ]
let equals ts lo hi = opener ts lo hi (fun _ t -> t = EQ)

(* errors.broken-parts: a constant whose part breaks after its [=] has the type
   written before it and no value, so a value argument that names it gives the
   error type (generics.constant-arguments). The [0] that completes it for
   parsing is no value of it. *)
let without_value (decl : decl node) =
  match decl.desc.kind with
  | Const c ->
      {
        decl with
        desc = { decl.desc with kind = Const { c with value = None } };
      }
  | Fn _ | Test _ | Type _ | Trait _ | Syntax _ | Effect _ | Macro _ -> decl

let mark_broken r (decl : decl node) =
  match decl.desc.kind with
  | Fn f -> r.broken <- f.name.loc :: r.broken
  | Const c -> r.broken <- c.name.loc :: r.broken
  | Test _ -> r.broken <- decl.loc :: r.broken
  | Type _ | Trait _ | Syntax _ | Effect _ | Macro _ -> ()

(* The declaration that the part from [lo] to [hi], which breaks at [d],
   declares with an error (errors.declarations-with-errors), whose name is marked broken. An
   [unknown] one declares only its name. *)
let rec recovered r place lo hi (d : Diagnostic.t) =
  let first, kw, kind = classify r.ts lo hi in
  let exported = kind = Fn && written_extern r.ts first hi in
  let declare ?(unknown = false) kind =
    let pub = r.ts.(first).token = PUB in
    Some
      {
        desc = { pub; exported; foreign = false; doc = []; kind; unknown };
        loc = loc_of r.ts.(first);
      }
  in
  (* The item written before the token that [opens] finds, completed by
     [filler], if the error comes after that token. *)
  let written opens filler =
    match opens r.ts kw hi with
    | Some o when after d r.ts.(o) -> (
        let at = r.ts.(o) in
        match parse r (place.wrap at (slice r.ts first o @ filler at)) with
        | Ok m -> place.extract m
        | Error _ -> None)
    | _ -> None
  in
  let name () = name_of r.ts.(kw + 1) in
  let either given unknown =
    match given with
    | Some _ -> given
    | None -> declare ~unknown:true (unknown (name ()))
  in
  let found =
    match kind with
    | (Type | Trait | Test | Syntax | Effect | Macro) when place.member -> None
    | Fn -> either (written body_opener empty_block) unknown_fn
    | Const ->
        either (Option.map without_value (written equals zero)) unknown_const
    | Type ->
        declare ~unknown:true
          (Type { name = name (); params = []; def = Variants [] })
    | Trait -> recovered_trait r first kw hi d (name ())
    | Syntax -> declare ~unknown:true (Syntax { name = name (); arms = [] })
    (* macros.expansion-order: a macro that breaks expands no use, as its module has
       an error. *)
    | Macro -> declare ~unknown:true (Macro (unknown_signature (name ())))
    (* handlers.declaring-effect: an effect that breaks declares its name, every use of which
       has the error type. *)
    | Effect ->
        declare ~unknown:true (Effect { name = name (); params = []; ops = [] })
    | Test -> (
        match if kw + 1 < hi then Some r.ts.(kw + 1).token else None with
        | Some (STRING s) -> declare (Test (s, []))
        | _ -> None)
    | Impl | Other -> None
  in
  Option.iter (mark_broken r) found;
  found

(* The members that the parts of a block declare, from [lo] to [hi]. *)
and members r header (lbrace : token) lo hi =
  let place = in_block header lbrace in
  List.filter_map
    (fun (ml, mh) ->
      match parse_part r place ml mh with
      | Ok m -> place.extract m
      | Error d -> recovered r place ml mh d)
    (cut ~starts:member_start r.ts lo hi)

(* A trait or an impl whose error comes after the [{] of its block: its
   header, completed by an empty block, then the members of its block. *)
and with_block r first kw hi (d : Diagnostic.t) =
  match block_opener r.ts kw hi with
  | Some b when after d r.ts.(b) -> (
      let lbrace = r.ts.(b) in
      let header = slice r.ts first b in
      let members = members r header lbrace (b + 1) (block_close r.ts b hi) in
      let empty = header @ [ lbrace; synthetic RBRACE lbrace ] in
      match parse r (empty @ [ synthetic EOF lbrace ]) with
      | Ok { items = [ item ]; _ } -> Some (item, members)
      | _ -> None)
  | _ -> None

and recovered_trait r first kw hi d name =
  match with_block r first kw hi d with
  | Some ({ desc = Decl ({ kind = Trait t; _ } as decl); loc }, members) ->
      Some { desc = { decl with kind = Trait { t with members } }; loc }
  | _ ->
      let pub = r.ts.(first).token = PUB in
      Some
        {
          desc =
            {
              pub;
              exported = false;
              foreign = false;
              doc = [];
              kind = Trait { name; params = []; members = [] };
              unknown = true;
            };
          loc = loc_of r.ts.(first);
        }

let reader ~file (lexed : Lexer.output) =
  { file; ts = fst (code lexed); lexical = lexed.error; broken = [] }

let tokens r = r.ts
let broken r = List.rev r.broken

type parsed = Parsed of module_ | Breaks of Diagnostic.t * bool

let parse_alone r (lo, hi) =
  match parse_part r alone lo hi with
  | Ok m -> Parsed m
  | Error d ->
      Breaks (d, match r.lexical with Some l -> d == l | None -> false)

let declare_broken r (lo, hi) (d : Diagnostic.t) : item list =
  let first, kw, kind = classify r.ts lo hi in
  match kind with
  | Impl -> (
      match with_block r first kw hi d with
      | Some ({ desc = Impl i; loc }, members) ->
          [ { desc = Ast.Impl { i with members }; loc } ]
      | _ -> [])
  | _ -> (
      match recovered r alone lo hi d with
      | Some decl -> [ { desc = Decl decl.desc; loc = decl.loc } ]
      | None -> [])

(* A part that holds only doc comments, which a lexical error ends, starts at
   its first one, as it does for the compiler. *)
let declared_at r lo hi =
  let first = after_docs r.ts lo hi in
  r.ts.(if first < hi then first else lo)
