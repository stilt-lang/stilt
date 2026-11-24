(* Programs with planted syntax errors, made by editing the tokens of other
   programs, which check that a parser reports each file's first syntax error
   where the reference interpreter does (goal compiler-checks-like-interpreter). Most edits break
   the program somewhere; some leave it valid, which checks the trees too.

   The tokenizer is crude on purpose. It shares nothing with either parser,
   and only needs to split text finely enough that each edit lands between
   tokens, as a programmer's mistake does. *)

let is_ident c =
  (c >= 'a' && c <= 'z')
  || (c >= 'A' && c <= 'Z')
  || c = '_'
  || (c >= '0' && c <= '9')

(* The operators of lexical.tokens that are longer than one character, longest
   first. *)
let operators =
  [
    "+%=";
    "-%=";
    "*%=";
    "<<=";
    ">>=";
    "..=";
    "+%";
    "-%";
    "*%";
    "==";
    "!=";
    "<=";
    ">=";
    "&&";
    "||";
    "<<";
    ">>";
    "+=";
    "-=";
    "*=";
    "/=";
    "%=";
    "&=";
    "|=";
    "^=";
    "->";
    "=>";
    "..";
  ]

(* The length of the token at [i]: a string literal or a comment up to the end
   of its line, a word or a number, an operator, or one character. *)
let token_length text i =
  let n = String.length text in
  let rec until stop j =
    if j < n && not (stop j) then until stop (j + 1) else j
  in
  let c = text.[i] in
  if c = '"' then
    let rec close j =
      if j >= n || text.[j] = '\n' then j
      else if text.[j] = '\\' && j + 1 < n then close (j + 2)
      else if text.[j] = '"' then j + 1
      else close (j + 1)
    in
    close (i + 1) - i
  else if c = '/' && i + 1 < n && text.[i + 1] = '/' then
    until (fun j -> text.[j] = '\n') i - i
  else if c >= '0' && c <= '9' then
    (* A number may hold a dot, as in [1.5]. *)
    until (fun j -> not (is_ident text.[j] || text.[j] = '.')) i - i
  else if is_ident c then until (fun j -> not (is_ident text.[j])) i - i
  else if c = ' ' || c = '\t' then
    until (fun j -> not (text.[j] = ' ' || text.[j] = '\t')) i - i
  else
    match
      List.find_opt
        (fun op ->
          let k = String.length op in
          i + k <= n && String.sub text i k = op)
        operators
    with
    | Some op -> String.length op
    | None -> Uchar.utf_decode_length (String.get_utf_8_uchar text i)

let tokenize text =
  let rec go i acc =
    if i >= String.length text then List.rev acc
    else
      let k = token_length text i in
      go (i + k) (String.sub text i k :: acc)
  in
  go 0 []

(* Punctuation and operators, and a line break. *)
let punctuation =
  [|
    "{";
    "}";
    "(";
    ")";
    "[";
    "]";
    ",";
    ";";
    ".";
    "..";
    "=";
    "==";
    "<";
    ">";
    ">>";
    "|";
    "||";
    "=>";
    "->";
    "?";
    "-";
    "!";
    ":";
    "\n";
  |]

(* Keywords, and the names that mean something in some places. *)
let keywords =
  [|
    "fn";
    "let";
    "if";
    "else";
    "match";
    "try";
    "catch";
    "raise";
    "return";
    "for";
    "in";
    "while";
    "type";
    "trait";
    "impl";
    "pub";
    "use";
    "module";
    "test";
    "because";
    "io";
    "without";
    "panic";
    "alloc";
    "escaping";
    "Self";
    "self";
  |]

(* The rest: names, literals, comments, more keywords, and bits of text that
   are lexical errors. *)
let others =
  [|
    "x";
    "X";
    "1";
    "1.5";
    "\"s\"";
    "\"a{x}b\"";
    "/// doc\n";
    "/// ex: 1 +\n";
    "// c\n";
    "`";
    "@";
    "_";
    "inout";
    "var";
    "const";
    "assert";
    "true";
    "loop";
    "break";
    "continue";
    "{x:>3}";
    "\"\\q\"";
    "007";
    "1__0";
    "\"{{\"";
  |]

(* Text that the edits insert: tokens of every kind, and bits of text that are
   lexical errors or doc comments. *)
let inserts = Array.concat [ punctuation; keywords; others ]

(* Applies one to three edits to the tokens: deleting, duplicating or swapping
   tokens, and inserting or replacing them with text from [inserts]. *)
let edit st tokens =
  let pick () = inserts.(Random.State.int st (Array.length inserts)) in
  let tokens = ref (Array.of_list tokens) in
  let edits = [| 1; 1; 1; 2; 3 |].(Random.State.int st 5) in
  for _ = 1 to edits do
    let ts = !tokens in
    let n = Array.length ts in
    if n > 0 then
      let i = Random.State.int st n in
      let before = Array.sub ts 0 i and after = Array.sub ts i (n - i) in
      let from j = Array.sub ts j (n - j) in
      let r = Random.State.float st 1.0 in
      tokens :=
        if r < 0.3 then Array.append before (from (i + 1))
        else if r < 0.45 then Array.concat [ before; [| ts.(i) |]; after ]
        else if r < 0.55 && i + 1 < n then
          Array.concat [ before; [| ts.(i + 1); ts.(i) |]; from (i + 2) ]
        else if r < 0.85 then Array.concat [ before; [| pick () |]; after ]
        else Array.concat [ before; [| pick () |]; from (i + 1) ]
  done;
  String.concat "" (Array.to_list !tokens)

(* The program of [seed]: an edit of one of [sources], which the seed picks. *)
let mutant sources seed =
  let st = Random.State.make [| seed |] in
  let text = sources.(Random.State.int st (Array.length sources)) in
  edit st (tokenize text)

(* Whether [text] names one of [words]. *)
let names words text =
  let n = String.length text in
  List.exists
    (fun w ->
      let k = String.length w in
      let rec at i = i + k <= n && (String.sub text i k = w || at (i + 1)) in
      at 0)
    words

(* Whether a run of [text] can be compared with another: one that draws from the system's
   randomness or reads a clock prints what no other run need print, so an edit that leaves it
   valid would be compared with a run that drew or read something else. *)
let reproducible text =
  not
    (names [ "entropy"; "now()"; "elapsed()"; "monotonic_ns"; "unix_ms" ] text)

(* The texts of the [.lt] files under [dirs] whose runs are [reproducible], sorted by path,
   outside any [_pending] directory. *)
let sources dirs =
  let rec files dir =
    Sys.readdir dir |> Array.to_list
    |> List.concat_map (fun entry ->
        let path = Filename.concat dir entry in
        if Sys.is_directory path then
          if entry = "_pending" then [] else files path
        else if Filename.check_suffix entry ".lt" then [ path ]
        else [])
  in
  List.concat_map files dirs |> List.sort compare
  |> List.map (fun path -> In_channel.with_open_bin path In_channel.input_all)
  |> List.filter reproducible |> Array.of_list
