(* Step 4 of name resolution: modules can't depend on one another in a cycle
   (program.no-cycles). *)

open Resolve_context

(* The modules that each module references, by [references]. *)
let targets_of references =
  let targets =
    List.fold_left
      (fun graph r ->
        Smap.update r.from
          (fun ts ->
            Some (Sset.add r.target (Option.value ts ~default:Sset.empty)))
          graph)
      Smap.empty references
  in
  fun m -> Option.value (Smap.find_opt m targets) ~default:Sset.empty

(* The strongly connected components of the graph of [modules] whose edges
   are [targets], found with Tarjan's algorithm. *)
let components modules targets =
  let index = Hashtbl.create 16 and low = Hashtbl.create 16 in
  let stack = ref [] and on_stack = Hashtbl.create 16 in
  let components = ref [] in
  let rec connect m =
    let i = Hashtbl.length index in
    Hashtbl.replace index m i;
    Hashtbl.replace low m i;
    stack := m :: !stack;
    Hashtbl.replace on_stack m ();
    Sset.iter
      (fun t ->
        if not (Hashtbl.mem index t) then (
          connect t;
          Hashtbl.replace low m (min (Hashtbl.find low m) (Hashtbl.find low t)))
        else if Hashtbl.mem on_stack t then
          Hashtbl.replace low m
            (min (Hashtbl.find low m) (Hashtbl.find index t)))
      (targets m);
    if Hashtbl.find low m = i then
      let rec pop component =
        match !stack with
        | [] -> invalid_arg "Resolve.check_cycles"
        | n :: rest ->
            stack := rest;
            Hashtbl.remove on_stack n;
            if n = m then Sset.add n component else pop (Sset.add n component)
      in
      components := pop Sset.empty :: !components
  in
  Sset.iter (fun m -> if not (Hashtbl.mem index m) then connect m) modules;
  !components

(* The shortest route of references from [a] to [b] inside [component],
   where every module reaches every other. *)
let route targets component a b =
  if a = b then [ a ]
  else
    let previous = Hashtbl.create 16 and queue = Queue.create () in
    Queue.add a queue;
    while not (Hashtbl.mem previous b) do
      let n = Queue.pop queue in
      Sset.iter
        (fun t ->
          if Sset.mem t component && t <> a && not (Hashtbl.mem previous t) then (
            Hashtbl.replace previous t n;
            Queue.add t queue))
        (targets n)
    done;
    let rec back n route =
      if n = a then a :: route else back (Hashtbl.find previous n) (n :: route)
    in
    back b []

(* Step 4: program.no-cycles. The references between [modules] form a graph,
   and each of its strongly connected components that holds a cycle is one
   error, at the last reference inside it (errors.primary-spans). *)
let check_cycles st modules =
  let references =
    List.filter
      (fun r -> Sset.mem r.from modules && Sset.mem r.target modules)
      st.references
  in
  let targets = targets_of references in
  let later (a : reference) (b : reference) =
    compare (a.file, a.loc.line, a.loc.col) (b.file, b.loc.line, b.loc.col) > 0
  in
  List.iter
    (fun component ->
      let inside =
        List.filter
          (fun r -> Sset.mem r.from component && Sset.mem r.target component)
          references
      in
      match inside with
      | [] -> ()
      | first :: _ ->
          let r =
            List.fold_left (fun a b -> if later b a then b else a) first inside
          in
          let cycle = r.from :: route targets component r.target r.from in
          report st ~file:r.file Code.e0206 r.loc
            "modules depend on one another in a cycle: %s"
            (String.concat " -> " cycle))
    (components modules targets)
