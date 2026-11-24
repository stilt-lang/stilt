(* pipeline: records through closures: maps, filters, folds and sorts by key, and groups in a
   map. *)

type item = { id : int; group : int; score : int; name : string }

let items n =
  let x = ref 3 in
  List.init n (fun i ->
      x := ((!x * 1103515245) + 12345) mod 2147483648;
      {
        id = i;
        group = !x mod 13;
        score = !x mod 1000;
        name = Printf.sprintf "n%d" (!x mod 97);
      })

let () =
  let all = items 100000 in
  let total = ref 0 in
  for round = 0 to 9 do
    let boosted =
      List.map (fun it -> { it with score = it.score + round }) all
    in
    let kept = List.filter (fun it -> it.score mod 3 <> 0) boosted in
    total :=
      !total
      + List.fold_left
          (fun acc it -> (acc + (it.score * it.group)) mod 1000000007)
          0 kept;
    let sorted = List.stable_sort (fun a b -> compare b.score a.score) kept in
    let best =
      List.map (fun it -> it.id) (List.filteri (fun i _ -> i < 5) sorted)
    in
    total := !total + List.fold_left ( + ) 0 best
  done;
  let groups = Hashtbl.create 16 in
  List.iter
    (fun it ->
      let sum = Option.value (Hashtbl.find_opt groups it.group) ~default:0 in
      Hashtbl.replace groups it.group (sum + it.score))
    all;
  let named =
    List.length
      (List.filter (fun it -> String.ends_with ~suffix:"7" it.name) all)
  in
  let top =
    match List.find_opt (fun it -> it.score = 999) all with
    | Some it -> it.id
    | None -> -1
  in
  Printf.printf "%d %d %d %d %b\n" !total
    (Option.value (Hashtbl.find_opt groups 4) ~default:0)
    named top
    (List.exists (fun it -> it.score > 998) all)
