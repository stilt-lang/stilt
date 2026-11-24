(* The sites of every body of a program, with the facts that cross bodies:
   the parameters each function consumes (values.consumed-parameters), its in-place
   parameters (facts.in-place-parameters) and its recursive group (facts.div). *)

open Tast
module N = Implicit_names

type body = { key : N.key; def : fn_def; block : block; last : Modes_last.t }

let code_bodies bodies =
  List.filter_map
    (fun (key, (def : fn_def)) ->
      match def.body with
      | Code block -> Some { key; def; block; last = Modes_last.compute block }
      | Native | Broken -> None)
    bodies

(* A least fixed point over the bodies: [step] gives each body's answer, from
   the answers so far, which start empty. Two bodies of one key, as a method
   that one type declares twice (E0208), would each replace the other's answer
   forever: the first declared answers for the key. *)
let fixed_point bodies step =
  let seen = Hashtbl.create 64 in
  let bodies =
    List.filter
      (fun b ->
        let fresh = not (Hashtbl.mem seen b.key) in
        Hashtbl.replace seen b.key ();
        fresh)
      bodies
  in
  let table = Hashtbl.create 64 in
  let find k = Option.value (Hashtbl.find_opt table k) ~default:[] in
  let rec go () =
    let changed =
      List.fold_left
        (fun changed b ->
          let next = step find b in
          if next = find b.key then changed
          else (
            Hashtbl.replace table b.key next;
            true))
        false bodies
    in
    if changed then go ()
  in
  go ();
  find

let flow env consumed b =
  let calls =
    {
      Modes_flow.consumed =
        (fun c -> Option.fold ~none:[] ~some:consumed (N.callee_key env c));
      may_store = Modes_cow.may_store env;
      cow = Modes_cow.is_cow env;
    }
  in
  Modes_flow_walk.walk calls ~params:b.def.params b.block

(* values.consumed-parameters: the positions of the parameters that a body consumes. *)
let consumption env bodies =
  fixed_point bodies (fun consumed b ->
      let kept = (flow env consumed b).kept in
      List.concat
        (List.mapi
           (fun i (_, (v : Hir.var)) ->
             if List.mem v.id kept then [ i ] else [])
           b.def.params))

let in_place_run env ~limited ~shared in_place b =
  Implicit_in_place.run
    {
      env;
      params = b.def.params;
      limited = limited Ast.Alloc b.def;
      last = b.last;
      shared = shared b.key;
      in_place;
    }
    b.block

(* facts.in-place-parameters: the in-place parameters of each function limited by
   [without alloc], with their modes, starting from none. *)
let in_place_params env ~limited ~shared bodies =
  fixed_point bodies (fun in_place b ->
      if not (limited Ast.Alloc b.def) then []
      else
        List.map
          (fun i -> (i, fst (List.nth b.def.params i)))
          (in_place_run env ~limited ~shared in_place b).reached)

(* facts.copy: each modification that modes.shared-writes makes shared, unless
   the copy at a call of facts.copy-at-call is the same site already. *)
let shared_sites copies (shared : Modes_shared.shared list) =
  List.filter_map
    (fun (s : Modes_shared.shared) ->
      if List.mem_assq s.place copies then None
      else
        let target =
          match (s.binding, Modes_places.place s.place) with
          | Some v, _ -> "`" ^ v.name ^ "`"
          | None, Some p -> "`" ^ p.root.name ^ "`"
          | None, None -> "a value"
        and whom =
          Option.fold ~none:"made in this loop"
            ~some:(fun (h : Hir.var) -> Printf.sprintf "that `%s` holds" h.name)
            s.holder
        in
        let fact =
          match s.place.desc with
          | When _ ->
              let whom =
                Option.fold ~none:"that leaves the `when`"
                  ~some:(fun (h : Hir.var) ->
                    Printf.sprintf "that `%s` holds" h.name)
                  s.holder
              in
              Printf.sprintf
                "this gives %s back to its handle while a copy of it %s lasts, \
                 which a later write copies"
                target whom
          | Call
              (Member ({ home = "std.sync"; name = "Shared" }, "new"), _, _, _)
            ->
              Printf.sprintf
                "this gives %s to a handle while %s may still read it, which a \
                 later write copies"
                target target
          | _ ->
              Printf.sprintf
                "this modifies %s while a copy of it %s lasts, which copies it"
                target whom
        in
        Some (Implicit_sites.site ~facts:[ (Ast.Copy, fact) ] s.place.loc))
    shared

let extra_sites env b (ip : Implicit_in_place.result) shared ~group ~proofs =
  List.map
    (fun ((arg : expr), why) ->
      Implicit_sites.site ~facts:[ (Ast.Alloc, why); (Copy, why) ] arg.loc)
    ip.copies
  @ shared_sites ip.copies shared
  @ List.map
      (fun ((e : expr), why, note) ->
        Implicit_sites.site
          ~facts:[ (Ast.Div, why) ]
          ~notes:
            (Option.fold ~none:[]
               ~some:(fun n -> [ ((Ast.Div : Ast.limit), n) ])
               note)
          e.loc)
      (Implicit_div.sites
         {
           env;
           self = Some b.key;
           group = group b.key;
           params = b.def.params;
           through = b.def.through;
           proofs;
         }
         b.block)

(* The proofs of the Reference's rules of acceptance change only the facts `panic`
   and `div`, which only the limits read: those of the bodies limited by
   `panic` or `div`, and through the names a body's sites hold, which a proof
   keeps, those of the bodies they reach. The rules read those bodies, and the
   others keep every operation's facts, which no limit reads. *)
let verified ~limited unproved =
  let names = Hashtbl.create 64 and needed = Hashtbl.create 64 in
  List.iter
    (fun (b, _, ss) ->
      Hashtbl.replace names b.key
        (List.concat_map (fun (s : Implicit_sites.site) -> s.names) ss))
    unproved;
  let rec reach k =
    if not (Hashtbl.mem needed k) then (
      Hashtbl.replace needed k ();
      List.iter reach (Option.value (Hashtbl.find_opt names k) ~default:[]))
  in
  List.iter
    (fun (b, _, _) ->
      if limited Ast.Panic b.def || limited Ast.Div b.def then reach b.key)
    unproved;
  needed

let sites env ~limited ~verify bodies =
  let bodies = code_bodies bodies in
  let consumed = consumption env bodies in
  let shared_of = Hashtbl.create 64 in
  List.iter
    (fun b ->
      Hashtbl.replace shared_of b.key
        (Modes_shared.shared (flow env consumed b)))
    bodies;
  let shared k = Option.value (Hashtbl.find_opt shared_of k) ~default:[] in
  let in_place = in_place_params env ~limited ~shared bodies in
  let unproved =
    List.map
      (fun b ->
        let ip = in_place_run env ~limited ~shared in_place b in
        (b, ip, Implicit_sites.sites env ip b.block))
      bodies
  in
  let needed = verified ~limited unproved in
  let base =
    List.map
      (fun (b, ip, ss) ->
        if Hashtbl.mem needed b.key then
          let proofs = verify b.key b.def b.block in
          (b, ip, Some proofs, Implicit_sites.sites ~proofs env ip b.block)
        else (b, ip, None, ss))
      unproved
  in
  let group =
    Implicit_groups.groups
      (List.map
         (fun (b, _, _, ss) ->
           (b.key, List.concat_map (fun (s : Implicit_sites.site) -> s.names) ss))
         base)
  in
  List.map
    (fun (b, ip, proofs, ss) ->
      (b.key, ss @ extra_sites env b ip (shared b.key) ~group ~proofs))
    base
