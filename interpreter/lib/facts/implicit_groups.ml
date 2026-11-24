(* Recursive groups (facts.div): the strongly connected components of the
   graph of what each body names (facts.inference), found by Tarjan's
   algorithm. *)

type 'k node = {
  mutable index : int;
  mutable low : int;
  mutable on_stack : bool;
  edges : 'k list;
}

let groups (graph : ('k * 'k list) list) =
  let nodes = Hashtbl.create 64 in
  List.iter
    (fun (k, edges) ->
      Hashtbl.replace nodes k { index = -1; low = 0; on_stack = false; edges })
    graph;
  let counter = ref 0 and stack = ref [] and found = Hashtbl.create 64 in
  let rec visit k n =
    n.index <- !counter;
    n.low <- !counter;
    incr counter;
    stack := k :: !stack;
    n.on_stack <- true;
    List.iter
      (fun j ->
        match Hashtbl.find_opt nodes j with
        | Some m when m.index < 0 ->
            visit j m;
            n.low <- min n.low m.low
        | Some m when m.on_stack -> n.low <- min n.low m.index
        | _ -> ())
      n.edges;
    if n.low = n.index then pop k []
  and pop k members =
    match !stack with
    | j :: rest ->
        stack := rest;
        (Hashtbl.find nodes j).on_stack <- false;
        let members = j :: members in
        if j = k then record members else pop k members
    | [] -> ()
  and record members =
    let recursive =
      match members with
      | [ k ] -> List.mem k (Hashtbl.find nodes k).edges
      | _ -> true
    in
    if recursive then
      List.iter (fun k -> Hashtbl.replace found k members) members
  in
  List.iter
    (fun (k, _) ->
      let n = Hashtbl.find nodes k in
      if n.index < 0 then visit k n)
    graph;
  fun k -> Option.value (Hashtbl.find_opt found k) ~default:[]
