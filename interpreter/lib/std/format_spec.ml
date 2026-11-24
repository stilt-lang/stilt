(* The grammar of a spec is lexical.format-specs: [[fill]align][width][.precision]
   [kind]. Its meaning is std.width-fill-and-alignment, std.precision, std.integer-kinds, std.scientific-notation and std.format-special-values. *)

type t = {
  fill : string;
  align : char option;
  width : int;
  precision : int option;
  kind : char option;
}

let limit = 65535
let is_align c = c = '<' || c = '^' || c = '>'

exception Invalid

let parse text =
  let n = String.length text in
  let first =
    if n = 0 then 0 else Uchar.utf_decode_length (String.get_utf_8_uchar text 0)
  in
  (* A fill of [{] would read as the start of an interpolation. *)
  let fill, align, i =
    if n > first && is_align text.[first] && text.[0] <> '{' then
      (String.sub text 0 first, Some text.[first], first + 1)
    else if n > 0 && is_align text.[0] then (" ", Some text.[0], 1)
    else (" ", None, 0)
  in
  (* A number up to [limit], from [i], and the position after it. A number
     has no leading zero, so [05] is no width. *)
  let number i =
    if i + 1 < n && text.[i] = '0' && text.[i + 1] >= '0' && text.[i + 1] <= '9'
    then raise Invalid;
    let rec go j value =
      if j < n && text.[j] >= '0' && text.[j] <= '9' then
        let value = (value * 10) + Char.code text.[j] - Char.code '0' in
        if value > limit then raise Invalid else go (j + 1) value
      else (value, j)
    in
    go i 0
  in
  match
    let width, i = number i in
    let precision, i =
      if i < n && text.[i] = '.' then
        match number (i + 1) with
        | _, j when j = i + 1 -> raise Invalid
        | p, j -> (Some p, j)
      else (None, i)
    in
    let kind, i =
      if i < n && String.contains "xXobe" text.[i] then (Some text.[i], i + 1)
      else (None, i)
    in
    if i < n then raise Invalid else { fill; align; width; precision; kind }
  with
  | spec -> Some spec
  | exception Invalid -> None

type number = Int of Ints.kind * int64 | Float of bool * float | Not_a_number

let length text =
  let rec go i count =
    if i >= String.length text then count
    else
      go
        (i + Uchar.utf_decode_length (String.get_utf_8_uchar text i))
        (count + 1)
  in
  go 0 0

let apply spec number shown =
  (* std.precision, std.integer-kinds, std.scientific-notation and std.format-special-values *)
  let body =
    match (number, spec.kind, spec.precision) with
    | Int (k, v), Some 'x', _ -> Ints.to_base k ~base:16 ~upper:false v
    | Int (k, v), Some 'X', _ -> Ints.to_base k ~base:16 ~upper:true v
    | Int (k, v), Some 'o', _ -> Ints.to_base k ~base:8 ~upper:false v
    | Int (k, v), Some 'b', _ -> Ints.to_base k ~base:2 ~upper:false v
    | Float (f32, x), Some 'e', precision -> Floats.scientific ~f32 ?precision x
    | Float (_, x), None, Some precision -> Floats.fixed ~precision x
    | _ -> shown
  in
  (* std.width-fill-and-alignment. Centred text puts the odd fill character on the right. *)
  let pad = spec.width - length body in
  if pad <= 0 then body
  else
    let fill k = String.concat "" (List.init k (fun _ -> spec.fill)) in
    let align =
      match (spec.align, number) with
      | Some a, _ -> a
      | None, (Int _ | Float _) -> '>'
      | None, Not_a_number -> '<'
    in
    match align with
    | '>' -> fill pad ^ body
    | '^' -> fill (pad / 2) ^ body ^ fill (pad - (pad / 2))
    | _ -> body ^ fill pad
