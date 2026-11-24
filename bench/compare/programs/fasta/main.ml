(* fasta: writes random DNA sequences, from cumulative probabilities and a linear congruential
   generator, and a repeated one, as the Benchmarks Game's program does, in lines of 60. *)

let alu =
  "GGCCGGGCGCGGTGGCTCACGCCTGTAATCCCAGCACTTTGGGAGGCCGAGGCGGGCGGATCACCTGAGGTCAGGAGTTCGAGACCAGCCTGGCCAACATGGTGAAACCCCGTCTCTACTAAAAATACAAAAATTAGCCGGGCGTGGTGGCGCGCGCCTGTAATCCCAGCTACTCGGGAGGCTGAGGCAGGAGAATCGCTTGAACCCGGGAGGCGGAGGTTGCAGTGAGCCGAGATCGCGCCACTGCACTCCAGCCTGGGCGACAGAGCGAGACTCCGTCTCAAAAA"

let random seed =
  seed := ((!seed * 3877) + 29573) mod 139968;
  float_of_int !seed /. 139968.0

let repeat n =
  let len = String.length alu in
  let start = ref 0 and left = ref n in
  while !left > 0 do
    let width = min !left 60 in
    print_endline (String.init width (fun i -> alu.[(!start + i) mod len]));
    start := (!start + width) mod len;
    left := !left - width
  done

let randomly symbols chances n seed =
  let sum = ref 0.0 in
  let cumulative =
    Array.map
      (fun c ->
        sum := !sum +. c;
        !sum)
      chances
  in
  let last = Array.length cumulative - 1 in
  let left = ref n in
  while !left > 0 do
    let width = min !left 60 in
    let symbol _ =
      let r = random seed in
      let k = ref 0 in
      while !k < last && r >= cumulative.(!k) do
        incr k
      done;
      symbols.[!k]
    in
    print_endline (String.init width symbol);
    left := !left - width
  done

let () =
  let n = 100000 and seed = ref 42 in
  print_endline ">ONE Homo sapiens alu";
  repeat (n * 2);
  print_endline ">TWO IUB ambiguity codes";
  let iub =
    [|
      0.27;
      0.12;
      0.12;
      0.27;
      0.02;
      0.02;
      0.02;
      0.02;
      0.02;
      0.02;
      0.02;
      0.02;
      0.02;
      0.02;
      0.02;
    |]
  in
  randomly "acgtBDHKMNRSVWY" iub (n * 3) seed;
  print_endline ">THREE Homo sapiens frequency";
  let sapiens =
    [| 0.3029549426680; 0.1979883004921; 0.1975473066391; 0.3015094502008 |]
  in
  randomly "acgt" sapiens (n * 5) seed
