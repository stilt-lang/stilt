(* map-heavy: inserts, finds, overwrites and removes integer and string keys in hash maps. *)

let next x = ((x * 1103515245) + 12345) mod 2147483648

let () =
  let n = 300000 in
  let numbers = Hashtbl.create 16 in
  let x = ref 42 in
  for i = 0 to n - 1 do
    x := next !x;
    Hashtbl.replace numbers (!x mod 100000) i
  done;
  let hits = ref 0 in
  for _ = 1 to n do
    x := next !x;
    if Hashtbl.mem numbers (!x mod 200000) then incr hits
  done;
  for k = 0 to 49999 do
    Hashtbl.remove numbers (k * 2)
  done;
  let sum = Hashtbl.fold (fun k v sum -> sum + (k lxor v)) numbers 0 in
  Printf.printf "%d numbers, %d hits, checksum %d\n" (Hashtbl.length numbers)
    !hits sum;
  let words = Hashtbl.create 16 in
  for _ = 1 to n do
    x := next !x;
    let w = Printf.sprintf "w%d" (!x mod 5000) in
    Hashtbl.replace words w
      (1 + Option.value (Hashtbl.find_opt words w) ~default:0)
  done;
  let longest, most =
    Hashtbl.fold
      (fun w count (longest, most) ->
        (max longest (String.length w), max most count))
      words (0, 0)
  in
  Printf.printf "%d words, longest %d, most %d\n" (Hashtbl.length words) longest
    most
