(* tests.generable-types and tests.growth-test. *)

module T = Types

(* A type parameter of a declaration: the declaration and the place. *)
type node = Hir.item * int

let rec occurs (p : Hir.var) ty =
  match T.resolve ty with
  | T.Param q -> q.id = p.id
  | Con (_, ts) | Tuple ts -> List.exists (occurs p) ts
  | Record fields -> List.exists (fun (_, t) -> occurs p t) fields
  | App (h, ts) -> List.exists (occurs p) (h :: ts)
  | Spread (h, t) -> occurs p h || occurs p t
  | Fn (params, ret, _) ->
      List.exists (fun (_, t) -> occurs p t) params || occurs p ret
  | Forall f -> occurs p f.body
  | Handler h -> List.exists (occurs p) (h.hargs @ Option.to_list h.answer)
  | Var _ | Value _ | Error -> false

let is_param p ty =
  match T.resolve ty with T.Param q -> q.id = (p : Hir.var).id | _ -> false

let declared env item =
  match Env.type_info env item with
  | Some { def = Record _ | Variants _; _ } -> true
  | _ -> false

(* What a declaration holds, in terms of its parameters. *)
let held (info : Env.type_info) =
  match info.def with
  | Record fields -> List.map snd fields
  | Variants vs -> List.concat_map snd vs
  | Builtin -> []

(* The edges that [ty] gives when a declaration [owner] with parameters
   [params] holds it, and the declarations it names. *)
let rec holds env ~edges ~names owner params ty =
  match T.resolve ty with
  | T.Tuple ts -> List.iter (holds env ~edges ~names owner params) ts
  | Con (item, args) ->
      if declared env item then begin
        names := item :: !names;
        Option.iter
          (fun from ->
            List.iteri
              (fun j a ->
                List.iteri
                  (fun i p ->
                    if occurs p a then
                      edges :=
                        ((from, i), (item, j), not (is_param p a)) :: !edges)
                  params)
              args)
          owner
      end;
      List.iter (holds env ~edges ~names owner params) args
  | _ -> ()

let edges env roots =
  let edges = ref [] and seen = Hashtbl.create 16 in
  let rec drain names =
    List.iter
      (fun (item : Hir.item) ->
        let k = (item.home, item.name) in
        if not (Hashtbl.mem seen k) then begin
          Hashtbl.add seen k ();
          match Env.type_info env item with
          | None -> ()
          | Some info ->
              let found = ref [] in
              List.iter
                (holds env ~edges ~names:found (Some item) info.params)
                (held info);
              drain !found
        end)
      names
  in
  let found = ref [] in
  List.iter (holds env ~edges ~names:found None []) roots;
  drain !found;
  !edges

let key ((item : Hir.item), i) = (item.home, item.name, i)

(* Whether some growing edge lies on a cycle: its target reaches its source. *)
let infinite env roots =
  let edges = edges env roots in
  let next = Hashtbl.create 16 in
  List.iter (fun (from, to_, _) -> Hashtbl.add next (key from) (key to_)) edges;
  let reaches target start =
    let seen = Hashtbl.create 16 in
    let rec go n =
      n = target
      || (not (Hashtbl.mem seen n))
         && begin
           Hashtbl.add seen n ();
           List.exists go (Hashtbl.find_all next n)
         end
    in
    go start
  in
  List.exists
    (fun (from, to_, grows) -> grows && reaches (key from) (key to_))
    edges
