(* life: runs Conway's Game of Life on a grid that wraps around, held as one list of cells. *)

let step cells n =
  Array.init (n * n) (fun i ->
      let y = i / n and x = i mod n in
      let alive = ref 0 in
      for dy = 0 to 2 do
        for dx = 0 to 2 do
          if dy <> 1 || dx <> 1 then begin
            let yy = (y + dy + n - 1) mod n and xx = (x + dx + n - 1) mod n in
            if cells.((yy * n) + xx) then incr alive
          end
        done
      done;
      !alive = 3 || (cells.(i) && !alive = 2))

let () =
  let n = 256 in
  let x = ref 11 in
  let cells =
    Array.init (n * n) (fun _ ->
        x := ((!x * 1103515245) + 12345) mod 2147483648;
        !x mod 3 = 0)
  in
  let cells = ref cells in
  for _ = 1 to 60 do
    cells := step !cells n
  done;
  let alive =
    Array.fold_left (fun count c -> if c then count + 1 else count) 0 !cells
  in
  Printf.printf "%d cells alive\n" alive
