(* nsieve: counts the primes below three bounds with the sieve of Eratosthenes, as the Benchmarks
   Game's former program does. *)

let primes m =
  let flags = Array.make (m + 1) true and count = ref 0 in
  for i = 2 to m do
    if flags.(i) then begin
      incr count;
      let k = ref (i + i) in
      while !k <= m do
        flags.(!k) <- false;
        k := !k + i
      done
    end
  done;
  !count

let () =
  for shift = 0 to 2 do
    let m = (1 lsl (22 - shift)) * 10000 / 4096 in
    Printf.printf "Primes up to %8d %8d\n" m (primes m)
  done
