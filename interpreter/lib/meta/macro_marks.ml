(* The marks of hygiene (macros.hygiene): [tmp#1] is the [tmp] that the
   expansion numbered 1 writes, and [x#hole] stands for the fragment [x] while
   the template is checked. *)

let mark n name = name ^ "#" ^ string_of_int n
let hole name = name ^ "#hole"

let suffix name =
  match String.index_opt name '#' with
  | Some i ->
      Some
        ( String.sub name 0 i,
          String.sub name (i + 1) (String.length name - i - 1) )
  | None -> None

let split name =
  match suffix name with
  | Some (base, n) -> Option.map (fun n -> (base, n)) (int_of_string_opt n)
  | None -> None

let base name = match suffix name with Some (base, _) -> base | None -> name

let is_hole name =
  match suffix name with Some (_, "hole") -> true | _ -> false
