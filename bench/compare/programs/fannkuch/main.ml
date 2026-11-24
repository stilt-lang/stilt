(* fannkuch-redux: the most pancake flips over the permutations of 1 to n, and a checksum of them,
   as the Benchmarks Game's program counts them, on one thread. *)

exception Done of int * int

let flips_of perm =
  let flips = ref 0 in
  while perm.(0) <> 0 do
    let i = ref 0 and j = ref perm.(0) in
    while !i < !j do
      let t = perm.(!i) in
      perm.(!i) <- perm.(!j);
      perm.(!j) <- t;
      incr i;
      decr j
    done;
    incr flips
  done;
  !flips

let fannkuch n =
  let perm1 = Array.init n Fun.id and count = Array.make n 0 in
  let max_flips = ref 0
  and checksum = ref 0
  and permutations = ref 0
  and r = ref n in
  try
    while true do
      while !r <> 1 do
        count.(!r - 1) <- !r;
        decr r
      done;
      let flips = flips_of (Array.copy perm1) in
      max_flips := max !max_flips flips;
      checksum :=
        if !permutations mod 2 = 0 then !checksum + flips else !checksum - flips;
      let rotating = ref true in
      while !rotating do
        if !r = n then raise (Done (!checksum, !max_flips));
        let first = perm1.(0) in
        Array.blit perm1 1 perm1 0 !r;
        perm1.(!r) <- first;
        count.(!r) <- count.(!r) - 1;
        if count.(!r) > 0 then rotating := false else incr r
      done;
      incr permutations
    done;
    (!checksum, !max_flips)
  with Done (checksum, flips) -> (checksum, flips)

let () =
  let n = 10 in
  let checksum, flips = fannkuch n in
  Printf.printf "%d\nPfannkuchen(%d) = %d\n" checksum n flips
