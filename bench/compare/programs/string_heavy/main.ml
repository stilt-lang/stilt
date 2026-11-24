(* string-heavy: builds a text of words, then splits, searches, replaces, changes the case of and
   joins it. The standard library has no search or replacement of substrings, so both are
   written here. *)

(* The first index at or after [from] where [sub] occurs in [s]. *)
let find_from s sub from =
  let n = String.length s and m = String.length sub in
  let rec go i =
    if i + m > n then None
    else if String.sub s i m = sub then Some i
    else go (i + 1)
  in
  go from

let replace_all s sub by =
  let b = Buffer.create (String.length s) in
  let rec go i =
    match find_from s sub i with
    | Some j ->
        Buffer.add_substring b s i (j - i);
        Buffer.add_string b by;
        go (j + String.length sub)
    | None -> Buffer.add_substring b s i (String.length s - i)
  in
  go 0;
  Buffer.contents b

let () =
  let x = ref 7 in
  let words =
    List.init 200000 (fun _ ->
        x := ((!x * 1103515245) + 12345) mod 2147483648;
        Printf.sprintf "w%d" (!x mod 1000))
  in
  let text = String.concat " " words in
  let parts = String.split_on_char ' ' text in
  let lengths = List.fold_left (fun n p -> n + String.length p) 0 parts in
  let sevens = List.length (List.filter (String.ends_with ~suffix:"7") parts) in
  let replaced = replace_all text "w1" "one-" in
  let upper = String.uppercase_ascii replaced in
  let digits = ref 0 in
  String.iter (fun c -> if c >= '0' && c <= '9' then incr digits) upper;
  let found = Option.value (find_from upper "ONE-99 " 0) ~default:(-1) in
  let lines = String.split_on_char '\n' (replace_all text " w5" "\nw5") in
  let longest =
    List.fold_left (fun n line -> max n (String.length line)) 0 lines
  in
  Printf.printf "%d bytes, %d words, %d letters, %d sevens\n"
    (String.length text) (List.length parts) lengths sevens;
  Printf.printf "%d replaced, %d digits, found at %d\n" (String.length replaced)
    !digits found;
  Printf.printf "%d lines, longest %d, trimmed %s\n" (List.length lines) longest
    (String.trim ("  " ^ String.sub upper 0 20 ^ "  "))
