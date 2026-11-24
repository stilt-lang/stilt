(* json: writes a JSON document of 20000 records, parses it back into a tree with a
   recursive-descent parser, and sums what the tree holds. *)

type json =
  | Null
  | Bool of bool
  | Num of int
  | Text of string
  | Array of json list
  | Object of (string * json) list

let document n =
  let record i =
    let active = if i mod 3 = 0 then "true" else "false" in
    let note =
      if i mod 5 = 0 then "null" else Printf.sprintf {|"line\none \"%d\""|} i
    in
    Printf.sprintf
      {|{"id": %d, "name": "item%d", "active": %s, "tags": ["a", "b%d"], "point": {"x": %d, "y": [1, 2, %d]}, "note": %s}|}
      i i active (i mod 4) (i mod 7) (i mod 11) note
  in
  "[" ^ String.concat ", " (List.init n record) ^ "]"

let skip_space text pos =
  while
    !pos < String.length text && (text.[!pos] = ' ' || text.[!pos] = '\n')
  do
    incr pos
  done

let string text pos =
  incr pos;
  let b = Buffer.create 16 in
  let start = ref !pos in
  while text.[!pos] <> '"' do
    if text.[!pos] = '\\' then begin
      Buffer.add_substring b text !start (!pos - !start);
      Buffer.add_char b
        (if text.[!pos + 1] = 'n' then '\n' else text.[!pos + 1]);
      pos := !pos + 2;
      start := !pos
    end
    else incr pos
  done;
  Buffer.add_substring b text !start (!pos - !start);
  incr pos;
  Buffer.contents b

let number text pos =
  let n = ref 0 in
  while !pos < String.length text && text.[!pos] >= '0' && text.[!pos] <= '9' do
    n := (!n * 10) + Char.code text.[!pos] - 48;
    incr pos
  done;
  !n

(* The items of an object or an array up to [close], each read by [item]. *)
let items text pos close item =
  incr pos;
  skip_space text pos;
  let rec go acc =
    if text.[!pos] = close then begin
      incr pos;
      List.rev acc
    end
    else begin
      let x = item () in
      skip_space text pos;
      if text.[!pos] = ',' then incr pos;
      go (x :: acc)
    end
  in
  go []

let rec value text pos =
  skip_space text pos;
  match text.[!pos] with
  | '{' ->
      Object
        (items text pos '}' (fun () ->
             skip_space text pos;
             let key = string text pos in
             skip_space text pos;
             incr pos;
             (key, value text pos)))
  | '[' -> Array (items text pos ']' (fun () -> value text pos))
  | '"' -> Text (string text pos)
  | 't' ->
      pos := !pos + 4;
      Bool true
  | 'f' ->
      pos := !pos + 5;
      Bool false
  | 'n' ->
      pos := !pos + 4;
      Null
  | _ -> Num (number text pos)

type totals = {
  mutable numbers : int;
  mutable texts : int;
  mutable trues : int;
  mutable nulls : int;
  mutable nodes : int;
}

let rec add t json =
  t.nodes <- t.nodes + 1;
  match json with
  | Null -> t.nulls <- t.nulls + 1
  | Bool b -> if b then t.trues <- t.trues + 1
  | Num n -> t.numbers <- t.numbers + n
  | Text s -> t.texts <- t.texts + String.length s
  | Array xs -> List.iter (add t) xs
  | Object fields ->
      List.iter
        (fun (key, x) ->
          t.texts <- t.texts + String.length key;
          add t x)
        fields

let () =
  let source = document 20000 in
  let json = value source (ref 0) in
  let t = { numbers = 0; texts = 0; trues = 0; nulls = 0; nodes = 0 } in
  add t json;
  Printf.printf "%d bytes, %d nodes\n" (String.length source) t.nodes;
  Printf.printf "numbers %d, text %d, true %d, null %d\n" t.numbers t.texts
    t.trues t.nulls
