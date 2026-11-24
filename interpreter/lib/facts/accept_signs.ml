(* Known signs (facts.known-signs): the integer expressions known non-negative,
   and those known positive, each in the body it is evaluated in. A binding is
   known non-negative by the greatest fixed point: the bindings count on one
   another and on themselves, so [a = a + 1] keeps [a] known non-negative, as
   [a += 1] does. *)

open Tast
module C = Accept_code
module W = Accept_walk

type t = { w : W.t; known : (int, unit) Hashtbl.t }

let rec nonneg t (e : expr) body =
  match C.number t.w.reader e with
  | Some n -> C.sign n >= 0
  | None -> (
      match e.desc with
      | Call (c, _, [ _ ], _) -> C.method_name c = Some "len"
      | Local v -> (
          match Hashtbl.find_opt t.w.decls v.id with
          | Some (b, W.Range_start start) when b = body -> nonneg t start body
          | Some (b, _) when b = body -> Hashtbl.mem t.known v.id
          | _ -> false)
      | Binary ((Add | Mul), a, b) -> nonneg t a body && nonneg t b body
      | _ -> false)

let rec positive t (e : expr) body =
  match C.number t.w.reader e with
  | Some n -> C.sign n > 0
  | None -> (
      match e.desc with
      | Local v -> (
          match Hashtbl.find_opt t.w.decls v.id with
          | Some (b, W.Range_start start) when b = body -> positive t start body
          | _ -> false)
      | _ -> false)

(* Whether a [let] or a [var] binding is known non-negative: its initial value
   is, and its body writes it only by [=] or [+=] of known non-negative
   expressions. *)
let binding t id body = function
  | W.Range_start _ -> false
  | Let_init init | Var_init init ->
      nonneg t init body
      && Dynarray.for_all
           (fun (x : W.write) ->
             x.body <> body || x.root <> id
             || x.fields = [] && (not x.indexed)
                && (x.kind = Assign None || x.kind = Assign (Some Add))
                && Option.fold ~none:false
                     ~some:(fun v -> nonneg t v body)
                     x.value)
           t.w.log

let of_walk (w : W.t) =
  let t = { w; known = Hashtbl.create 16 } in
  Hashtbl.iter (fun id _ -> Hashtbl.replace t.known id ()) w.decls;
  let rec fix () =
    let lost =
      Hashtbl.fold
        (fun id (body, d) acc ->
          if Hashtbl.mem t.known id && not (binding t id body d) then id :: acc
          else acc)
        w.decls []
    in
    if lost <> [] then (
      List.iter (Hashtbl.remove t.known) lost;
      fix ())
  in
  fix ();
  t
