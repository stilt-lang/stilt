(* n-body: simulates the orbits of the Jovian planets with a symplectic integrator, as the
   Benchmarks Game's program does. *)

type body = {
  mutable x : float;
  mutable y : float;
  mutable z : float;
  mutable vx : float;
  mutable vy : float;
  mutable vz : float;
  mass : float;
}

let solar_mass = 4.0 *. Float.pi *. Float.pi
let days_per_year = 365.24

let body x y z vx vy vz mass =
  {
    x;
    y;
    z;
    vx = vx *. days_per_year;
    vy = vy *. days_per_year;
    vz = vz *. days_per_year;
    mass = mass *. solar_mass;
  }

let system () =
  [|
    body 0.0 0.0 0.0 0.0 0.0 0.0 1.0;
    body 4.84143144246472090 (-1.16032004402742839) (-0.103622044471123109)
      0.00166007664274403694 0.00769901118419740425 (-0.0000690460016972063023)
      0.000954791938424326609;
    body 8.34336671824457987 4.12479856412430479 (-0.403523417114321381)
      (-0.00276742510726862411) 0.00499852801234917238 0.0000230417297573763929
      0.000285885980666130812;
    body 12.8943695621391310 (-15.1111514016986312) (-0.223307578892655734)
      0.00296460137564761618 0.00237847173959480950 (-0.0000296589568540237556)
      0.0000436624404335156298;
    body 15.3796971148509165 (-25.9193146099879641) 0.179258772950371181
      0.00268067772490389322 0.00162824170038242295 (-0.0000951592254519715870)
      0.0000515138902046611451;
  |]

let offset_momentum bodies =
  let px = ref 0.0 and py = ref 0.0 and pz = ref 0.0 in
  Array.iter
    (fun b ->
      px := !px +. (b.vx *. b.mass);
      py := !py +. (b.vy *. b.mass);
      pz := !pz +. (b.vz *. b.mass))
    bodies;
  bodies.(0).vx <- -. !px /. solar_mass;
  bodies.(0).vy <- -. !py /. solar_mass;
  bodies.(0).vz <- -. !pz /. solar_mass

let energy bodies =
  let e = ref 0.0 and n = Array.length bodies in
  for i = 0 to n - 1 do
    let b = bodies.(i) in
    e :=
      !e
      +. (0.5 *. b.mass *. ((b.vx *. b.vx) +. (b.vy *. b.vy) +. (b.vz *. b.vz)));
    for j = i + 1 to n - 1 do
      let c = bodies.(j) in
      let dx = b.x -. c.x and dy = b.y -. c.y and dz = b.z -. c.z in
      e :=
        !e -. (b.mass *. c.mass /. sqrt ((dx *. dx) +. (dy *. dy) +. (dz *. dz)))
    done
  done;
  !e

let advance bodies dt =
  let n = Array.length bodies in
  for i = 0 to n - 1 do
    let bi = bodies.(i) in
    for j = i + 1 to n - 1 do
      let bj = bodies.(j) in
      let dx = bi.x -. bj.x and dy = bi.y -. bj.y and dz = bi.z -. bj.z in
      let d2 = (dx *. dx) +. (dy *. dy) +. (dz *. dz) in
      let mag = dt /. (d2 *. sqrt d2) in
      let mi = bi.mass *. mag and mj = bj.mass *. mag in
      bi.vx <- bi.vx -. (dx *. mj);
      bi.vy <- bi.vy -. (dy *. mj);
      bi.vz <- bi.vz -. (dz *. mj);
      bj.vx <- bj.vx +. (dx *. mi);
      bj.vy <- bj.vy +. (dy *. mi);
      bj.vz <- bj.vz +. (dz *. mi)
    done
  done;
  Array.iter
    (fun b ->
      b.x <- b.x +. (dt *. b.vx);
      b.y <- b.y +. (dt *. b.vy);
      b.z <- b.z +. (dt *. b.vz))
    bodies

let () =
  let bodies = system () in
  offset_momentum bodies;
  Printf.printf "%.9f\n" (energy bodies);
  for _ = 1 to 1000000 do
    advance bodies 0.01
  done;
  Printf.printf "%.9f\n" (energy bodies)
