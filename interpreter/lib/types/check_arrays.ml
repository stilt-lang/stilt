(* Arrays of [std.array] (generics.arrays, generics.array-literals and generics.array-patterns): their literals, their sizes
   and the list patterns that match them. *)

module T = Types
module A = Tast
open Check_state
open Check_expect

let item : Hir.item = { home = "std.array"; name = "Array" }

let parts ty =
  match T.resolve ty with
  | Con (i, [ elem; size ]) when i = item -> Some (elem, size)
  | _ -> None

(* generics.constant-arguments: a size known while the program is checked, in decimal. *)
let known_size size =
  match T.resolve size with Value text -> int_of_string_opt text | _ -> None

(* generics.array-literals: a list literal where [Array<elem, size>] is expected. Its
   length is exactly the size, which a value parameter never is (generics.constant-arguments), and
   none of its elements is a spread. A size that inference hasn't found yet
   is its length. *)
let literal ctx loc elem size (es : Hir.expr list) =
  let st = ctx.st in
  let ty = T.Con (item, [ elem; size ]) in
  let element (e : Hir.expr) =
    match e.desc with
    | Spread inner ->
        error st Code.e0311 e.loc
          "an array's literal has a length known where it is written, so it \
           spreads nothing";
        ignore (abandon ctx inner);
        error_node e.loc
    | _ -> check ctx elem e
  in
  let items = List.map element es in
  let length = List.length es in
  let spread =
    List.exists
      (fun (e : Hir.expr) -> match e.desc with Spread _ -> true | _ -> false)
      es
  in
  (if not spread then
     match T.resolve size with
     | Value text when int_of_string_opt text = Some length -> ()
     | Value text ->
         error st Code.e0311 loc
           "expected `%s`, an array of %s element%s, found a literal of %d"
           (show ty) text
           (if text = "1" then "" else "s")
           length
     | Param p ->
         error st Code.e0311 loc
           "expected `%s`, whose size is the value parameter `%s`, which no \
            literal's length is; found a literal of %d element%s"
           (show ty) p.name length
           (if length = 1 then "" else "s")
     | Var _ -> expect st loc ~expected:size (T.Value (string_of_int length))
     | _ -> ());
  node (List items) ty loc

(* generics.array-patterns: whether a list pattern of [length] patterns, with a rest
   or not, fits an array of [size]: of exactly its length, or of at most its
   length with a rest that binds nothing. Against a value parameter, only
   [[..]] fits. *)
let pattern_fits size length (rest : Hir.list_rest) =
  match (known_size size, rest) with
  | _, Rest_bind _ -> false
  | Some n, Exact -> length = n
  | Some n, Rest -> length <= n
  | None, Rest -> length = 0 || T.resolve size = Error
  | None, Exact -> T.resolve size = Error
