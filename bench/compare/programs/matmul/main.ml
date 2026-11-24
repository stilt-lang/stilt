(* matmul: multiplies two square matrices of floats, held as lists of rows. *)

let matrix n seed =
  Array.init n (fun i ->
      Array.init n (fun j -> float_of_int (((i * j) + seed) mod 17) /. 17.0))

let multiply a b =
  let n = Array.length a in
  Array.init n (fun i ->
      let ai = a.(i) in
      Array.init n (fun j ->
          let sum = ref 0.0 in
          for k = 0 to n - 1 do
            sum := !sum +. (ai.(k) *. b.(k).(j))
          done;
          !sum))

let () =
  let n = 250 in
  let c = multiply (matrix n 1) (matrix n 2) in
  let trace = ref 0.0 in
  for i = 0 to n - 1 do
    trace := !trace +. c.(i).(i)
  done;
  Printf.printf "%.6f %.6f\n" c.(n / 2).(n / 3) !trace
