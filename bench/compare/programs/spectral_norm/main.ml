(* spectral-norm: the spectral norm of an infinite matrix, by the power method, as the Benchmarks
   Game's program computes it. *)

let a i j = 1.0 /. float_of_int (((i + j) * (i + j + 1) / 2) + i + 1)

let times v =
  let n = Array.length v in
  Array.init n (fun i ->
      let sum = ref 0.0 in
      for j = 0 to n - 1 do
        sum := !sum +. (a i j *. v.(j))
      done;
      !sum)

let times_transposed v =
  let n = Array.length v in
  Array.init n (fun i ->
      let sum = ref 0.0 in
      for j = 0 to n - 1 do
        sum := !sum +. (a j i *. v.(j))
      done;
      !sum)

let times_both v = times_transposed (times v)

let () =
  let n = 1000 in
  let u = ref (Array.make n 1.0) and v = ref [||] in
  for _ = 1 to 10 do
    v := times_both !u;
    u := times_both !v
  done;
  let vbv = ref 0.0 and vv = ref 0.0 in
  for i = 0 to n - 1 do
    vbv := !vbv +. (!u.(i) *. !v.(i));
    vv := !vv +. (!v.(i) *. !v.(i))
  done;
  Printf.printf "%.9f\n" (sqrt (!vbv /. !vv))
