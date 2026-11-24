(* mandelbrot: counts the points of a grid that stay in the Mandelbrot set for 50 iterations, and
   the iterations of those that escape. *)

let () =
  let size = 600 in
  let scale = float_of_int size in
  let inside = ref 0 and escapes = ref 0 in
  for y = 0 to size - 1 do
    let ci = (2.0 *. float_of_int y /. scale) -. 1.0 in
    for x = 0 to size - 1 do
      let cr = (2.0 *. float_of_int x /. scale) -. 1.5 in
      let zr = ref 0.0 and zi = ref 0.0 and i = ref 0 and escaped = ref false in
      while !i < 50 && not !escaped do
        let next = (!zr *. !zr) -. (!zi *. !zi) +. cr in
        zi := (2.0 *. !zr *. !zi) +. ci;
        zr := next;
        if (!zr *. !zr) +. (!zi *. !zi) > 4.0 then escaped := true;
        incr i
      done;
      if !escaped then escapes := !escapes + !i else incr inside
    done
  done;
  Printf.printf "%d points inside, %d iterations to escape\n" !inside !escapes
