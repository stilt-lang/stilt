(* TOML 1.0, which manifests are written in (packages.manifest). *)

open Toml_scan

type defined = Implicitly | Header | Dotted | Inline

type value = { at : int; end_ : int; kind : kind }

and kind =
  | String of string
  | Integer
  | Float
  | Bool
  | Datetime
  | Array of value list
  | Table of table
  | Tables of table list

and table = {
  mutable defined : defined;
  mutable entries : entry list;
  mutable last : int;
}

and entry = { key : string; key_at : int; mutable value : value }

let describe = function
  | String _ -> "a string"
  | Integer -> "an integer"
  | Float -> "a float"
  | Bool -> "a boolean"
  | Datetime -> "a date"
  | Array _ -> "an array"
  | Table _ -> "a table"
  | Tables _ -> "an array of tables"

let new_table defined last = { defined; entries = []; last }
let get t key = List.find_opt (fun e -> e.key = key) t.entries
let add t e = t.entries <- t.entries @ [ e ]

let is_bare = function
  | 'A' .. 'Z' | 'a' .. 'z' | '0' .. '9' | '_' | '-' -> true
  | _ -> false

(* A key, with the spaces after it, as its parts and where each starts. *)
let key c =
  let rec part acc =
    let at = c.pos in
    let p =
      match peek c with
      | Some (('"' | '\'') as q)
        when peek_at c 1 = Some q && peek_at c 2 = Some q ->
          fail c "a key isn't a multi-line string"
      | Some ('"' | '\'') -> Toml_strings.string c
      | _ ->
          while Option.fold ~none:false ~some:is_bare (peek c) do
            bump c
          done;
          if c.pos = at then fail c "expected a key";
          String.sub c.text at (c.pos - at)
    in
    let acc = (p, at) :: acc in
    ws c;
    if eat c '.' then (
      ws c;
      part acc)
    else List.rev acc
  in
  part []

(* Defines [key] as [v] in [t], through the tables its dotted parts name. *)
let define t key v =
  let start = snd (List.hd key) in
  let twice () = raise (Syntax (start, "this key is already defined")) in
  let rec go t = function
    | [ (last, at) ] ->
        if Option.is_some (get t last) then twice ();
        add t { key = last; key_at = at; value = v }
    | (p, at) :: rest -> (
        if Option.is_none (get t p) then
          add t
            {
              key = p;
              key_at = at;
              value =
                { at; end_ = v.end_; kind = Table (new_table Dotted v.end_) };
            };
        match (Option.get (get t p)).value.kind with
        | Table sub when sub.defined = Dotted || sub.defined = Implicitly ->
            sub.defined <- Dotted;
            sub.last <- v.end_;
            go sub rest
        | _ -> twice ())
    | [] -> ()
  in
  go t key

(* Opens the table of a header, or a new table of an array of tables. *)
let open_ root key ~array ~end_ =
  let start = snd (List.hd key) in
  let twice () = raise (Syntax (start, "this table is already defined")) in
  let rec go t = function
    | [ (last, at) ] -> (
        let fresh = new_table Header end_ in
        match Option.map (fun e -> e.value.kind) (get t last) with
        | None ->
            let kind = if array then Tables [ fresh ] else Table fresh in
            add t { key = last; key_at = at; value = { at; end_; kind } }
        | Some (Table sub) when (not array) && sub.defined = Implicitly ->
            sub.defined <- Header;
            sub.last <- end_
        | Some (Tables ts) when array ->
            (Option.get (get t last)).value <-
              { at; end_; kind = Tables (ts @ [ fresh ]) }
        | Some _ -> twice ())
    | (p, at) :: rest -> (
        if Option.is_none (get t p) then
          add t
            {
              key = p;
              key_at = at;
              value = { at; end_; kind = Table (new_table Implicitly end_) };
            };
        match (Option.get (get t p)).value.kind with
        | Table sub when sub.defined <> Inline -> go sub rest
        | Tables ts -> go (List.nth ts (List.length ts - 1)) rest
        | _ -> twice ())
    | [] -> ()
  in
  go root key

(* The table at [path], which earlier headers made. *)
let rec table_at t = function
  | [] -> t
  | p :: rest -> (
      match (Option.get (get t p)).value.kind with
      | Table sub -> table_at sub rest
      | Tables ts -> table_at (List.nth ts (List.length ts - 1)) rest
      | _ -> invalid_arg "Toml.table_at")

let rec value c =
  let at = c.pos in
  let kind =
    match peek c with
    | Some ('"' | '\'') -> String (Toml_strings.string c)
    | Some 't' ->
        word c "true";
        Bool
    | Some 'f' ->
        word c "false";
        Bool
    | Some '[' -> array c
    | Some '{' -> inline_table c
    | Some ('0' .. '9' | '+' | '-' | 'i' | 'n') -> (
        match number c with
        | Int_number -> Integer
        | Float_number -> Float
        | Date_number -> Datetime)
    | _ -> fail c "expected a value"
  in
  { at; end_ = c.pos; kind }

and blank c =
  ws c;
  comment c;
  if newline c then blank c

and array c =
  bump c;
  let rec go acc =
    blank c;
    if eat c ']' then Array (List.rev acc)
    else
      let v = value c in
      blank c;
      if eat c ']' then Array (List.rev (v :: acc))
      else (
        expect c ',' "`,` or `]`";
        go (v :: acc))
  in
  go []

and key_value c =
  let k = key c in
  expect c '=' "`=`";
  ws c;
  (k, value c)

and inline_table c =
  bump c;
  ws c;
  let t = new_table Dotted c.pos in
  if eat c '}' then (
    t.defined <- Inline;
    Table t)
  else
    let rec go () =
      let k, v = key_value c in
      t.last <- v.end_;
      define t k v;
      ws c;
      if eat c '}' then (
        t.defined <- Inline;
        Table t)
      else (
        expect c ',' "`,` or `}`";
        ws c;
        go ())
    in
    go ()

let header c root =
  bump c;
  let array = eat c '[' in
  ws c;
  let k = key c in
  expect c ']' "`]`";
  if array then expect c ']' "`]]`";
  open_ root k ~array ~end_:c.pos;
  List.map fst k

let document c =
  let root = new_table Header 0 in
  let current = ref [] in
  let rec go () =
    ws c;
    (match peek c with
    | None -> ()
    | Some '#' -> comment c
    | Some ('\n' | '\r') -> ()
    | Some '[' -> current := header c root
    | Some _ ->
        let k, v = key_value c in
        let t = table_at root !current in
        t.last <- v.end_;
        define t k v);
    ws c;
    comment c;
    if peek c <> None then (
      if not (newline c) then fail c "expected the end of the line";
      go ())
  in
  go ();
  root

(* The offset of the first byte that isn't part of valid UTF-8, if any. *)
let invalid_utf8 text =
  let rec go i =
    if i >= String.length text then None
    else
      let d = String.get_utf_8_uchar text i in
      if Uchar.utf_decode_is_valid d then go (i + Uchar.utf_decode_length d)
      else Some i
  in
  go 0

let parse text =
  match invalid_utf8 text with
  | Some at -> Error (at, "the file isn't UTF-8")
  | None -> (
      try Ok (document { text; pos = 0 }) with Syntax (at, m) -> Error (at, m))
