(* Matching a use's tokens against a macro's arms (macros.matching). The
   tokens are an array, in which each opening bracket knows where it
   closes. *)

open Ast

type binding = One of string * Lexer.token list | Many of binding list
type bindings = (string * binding) list

exception Mismatch

type state = {
  ts : Lexer.token array;
  close : int array;  (** For each opening bracket, its closing one. *)
  mutable furthest : int;
  mutable expected : string;
}

(* The closing bracket of each opening one, a closing bracket closing the
   innermost open one. *)
let closes (ts : Lexer.token array) =
  let close = Array.make (Array.length ts) (-1) in
  let stack = ref [] in
  Array.iteri
    (fun i (t : Lexer.token) ->
      match t.token with
      | LPAREN | LBRACKET | LBRACE -> stack := i :: !stack
      | RPAREN | RBRACKET | RBRACE -> (
          match !stack with
          | o :: rest ->
              close.(o) <- i;
              stack := rest
          | [] -> ())
      | _ -> ())
    ts;
  close

(* Every arm that fails reports the token where it failed, and the furthest
   one is the use's error. *)
let fail st i expected =
  if i > st.furthest then (
    st.furthest <- i;
    st.expected <- expected);
  raise Mismatch

let same (a : Token.t) (b : Token.t) =
  match (a, b) with
  | LIDENT x, LIDENT y | UIDENT x, UIDENT y ->
      Macro_marks.base x = Macro_marks.base y
  | _ -> a = b

let slice st i j = Array.to_list (Array.sub st.ts i (j - i))

let noun = function
  | "expr" -> "an expression"
  | "block" -> "a block"
  | "pattern" -> "a pattern"
  | "type" -> "a type"
  | "name" -> "a `lower` name"
  | _ -> "an `Upper` name"

let parse_entry kind tokens =
  let length start = Option.map fst (Parse_run.longest ~file:"" start tokens) in
  match kind with
  | "expr" -> length Parser.Incremental.example
  | "pattern" -> length Parser.Incremental.pattern_example
  | "type" -> length Parser.Incremental.type_example
  | _ -> length Parser.Incremental.block_example

(* The number of tokens from [i] that the fragment of [kind] matches: the
   longest form of its kind. *)
let fragment st kind i hi =
  let token = if i < hi then Some st.ts.(i).token else None in
  match (kind, token) with
  | "name", Some (LIDENT _) | "Name", Some (UIDENT _) -> 1
  | "block", Some LBRACE -> (
      let j = st.close.(i) + 1 in
      match parse_entry kind (slice st i j) with
      | Some n when n = j - i -> n
      | _ -> fail st i (noun kind))
  | ("expr" | "pattern" | "type"), Some _ -> (
      match parse_entry kind (slice st i hi) with
      | Some n when n > 0 -> n
      | _ -> fail st i (noun kind))
  | _ -> fail st i (noun kind)

let is_separator (t : Token.t) = function "," -> t = COMMA | _ -> t = SEP

let rec seq st (ms : tree list) i hi env =
  match ms with
  | [] -> (i, env)
  | m :: rest ->
      let i, env = one st m i hi env in
      seq st rest i hi env

and one st (m : tree) i hi env =
  match m.desc with
  | Token a ->
      let t = Macro_tokens.token a in
      if i < hi && same st.ts.(i).token t then (i + 1, env)
      else fail st i (Macro_tokens.describe t)
  | Group (d, ms, _) ->
      if i < hi && st.ts.(i).token = Macro_tokens.opener d then
        let j = st.close.(i) in
        let k, env = seq st ms (i + 1) j env in
        if k = j then (j + 1, env)
        else fail st k (Macro_tokens.describe (Macro_tokens.closer d))
      else fail st i (Macro_tokens.describe (Macro_tokens.opener d))
  | Fragment (n, Some k) ->
      let length = fragment st k.desc i hi in
      (i + length, (n.desc, One (k.desc, slice st i (i + length))) :: env)
  | Fragment (_, None) -> invalid_arg "Macro_match.one"
  | Repeat (ms, sep, op) -> repeat st ms sep op i hi env

(* A repetition matches as many rounds as it can, each after its separator,
   and binds each of its fragments to what it matched in each round. *)
and repeat st ms sep op i hi env =
  let attempt j =
    match seq st ms j hi [] with
    | k, round when k > j -> Some (k, round)
    | _ -> None
    | exception Mismatch -> None
  in
  let rec rounds i found first =
    let start =
      match sep with
      | Some s when not first ->
          if i < hi && is_separator st.ts.(i).token s then Some (i + 1)
          else None
      | _ -> Some i
    in
    match Option.bind start attempt with
    | Some (k, round) -> rounds k (round :: found) false
    | None -> (i, List.rev found)
  in
  let i, found = rounds i [] true in
  if op = "+" && found = [] then raise Mismatch;
  let many name = Many (List.map (List.assoc name) found) in
  ( i,
    List.rev_append
      (List.map (fun name -> (name, many name)) (Macro_check.names ms))
      env )

(* An arm matches the use's group, and its trailing block matches the use's,
   if it has one. *)
let arm st (a : macro_arm) =
  let n = Array.length st.ts in
  let group_end = st.close.(0) + 1 in
  match one st a.pattern 0 group_end [] with
  | exception Mismatch -> None
  | _, env -> (
      match (a.block, group_end < n) with
      | None, false -> Some env
      | Some ((b : name), _), true -> (
          match parse_entry "block" (slice st group_end n) with
          | Some k when k = n - group_end ->
              Some ((b.desc, One ("block", slice st group_end n)) :: env)
          | _ -> ( try fail st group_end "a block" with Mismatch -> None))
      | None, true -> (
          try fail st group_end "the end of the use" with Mismatch -> None)
      | Some _, false -> (
          try fail st (group_end - 1) "a trailing block after the group"
          with Mismatch -> None))

let first arms ts =
  let st = { ts; close = closes ts; furthest = -1; expected = "an arm" } in
  match
    List.find_map (fun a -> Option.map (fun env -> (a, env)) (arm st a)) arms
  with
  | Some found -> Ok found
  | None ->
      let i = min (max st.furthest 0) (Array.length ts - 1) in
      Error (ts.(i), st.expected)
