(* sort: sorts a list of integers with the standard library's sort and with a quicksort that works
   in place. *)

let rec quicksort xs lo hi =
  if lo < hi then begin
    let pivot = xs.((lo + hi) / 2) in
    let i = ref lo and j = ref hi in
    while !i <= !j do
      while xs.(!i) < pivot do
        incr i
      done;
      while xs.(!j) > pivot do
        decr j
      done;
      if !i <= !j then begin
        let t = xs.(!i) in
        xs.(!i) <- xs.(!j);
        xs.(!j) <- t;
        incr i;
        decr j
      end
    done;
    quicksort xs lo !j;
    quicksort xs !i hi
  end

let checksum xs =
  Array.fold_left (fun sum x -> ((sum * 31) + x) mod 1000000007) 0 xs

let () =
  let x = ref 1 in
  let xs =
    Array.init 400000 (fun _ ->
        x := ((!x * 1103515245) + 12345) mod 2147483648;
        !x mod 1000000)
  in
  let sorted = Array.copy xs in
  Array.sort Int.compare sorted;
  let quick = Array.copy xs in
  quicksort quick 0 (Array.length quick - 1);
  let by_digit = Array.copy xs in
  Array.stable_sort (fun a b -> Int.compare (a mod 10) (b mod 10)) by_digit;
  Printf.printf "%d %d %d\n" (checksum sorted) (checksum quick)
    (checksum by_digit)
