(* tests.shrinking and tests.shrink-candidates. *)

open Value
module P = Prop_types

(* [seq] without the candidates identical to [value] or to an earlier one. *)
let distinct value seq =
  let seen = Hashtbl.create 16 in
  Hashtbl.replace seen (Prop_show.identity value) ();
  Seq.filter
    (fun c ->
      let k = Prop_show.identity c in
      (not (Hashtbl.mem seen k))
      &&
      (Hashtbl.replace seen k ();
       true))
    seq

let ints (k : Ints.kind) x =
  if x = 0L then []
  else
    let negative = Ints.compare k x 0L < 0 in
    let negated =
      if negative && x <> Ints.min_value k then [ Int64.neg x ] else []
    in
    let step = if negative then Int64.add x 1L else Ints.sub k x 1L in
    [ 0L ] @ negated @ [ Ints.div k x 2L; step ] |> List.map (fun x -> Int x)

let floats f32 x =
  if not (Float.is_finite x) then [ Float 0.0 ]
  else
    let whole = Float.trunc x = x in
    ([ 0.0 ]
    @ (if x < 0.0 then [ -.x ] else [])
    @ [ Float.trunc x ]
    @ if whole then [ Float.trunc (Floats.result ~f32 (x /. 2.0)) ] else [])
    |> List.map (fun x -> Float x)

(* The candidates of a sequence of [n] elements, as tests.shrink-candidates gives them for a
   list: shorter sequences, then each element replaced by each of its
   candidates, which [elem] gives. *)
let sequence xs elem =
  let n = Array.length xs in
  let sub a b = Array.sub xs a (b - a) in
  let without i = Array.append (sub 0 i) (sub (i + 1) n) in
  let with_ i c =
    let ys = Array.copy xs in
    ys.(i) <- c;
    ys
  in
  List.to_seq [ [||]; sub (n / 2) n; sub 0 (n / 2) ]
  |> Fun.flip Seq.append (Seq.init n without)
  |> Fun.flip Seq.append
       (Seq.concat (Seq.init n (fun i -> Seq.map (with_ i) (elem xs.(i)))))

let chars s =
  let rec go i acc =
    if i >= String.length s then List.rev acc
    else
      let d = String.get_utf_8_uchar s i in
      go
        (i + Uchar.utf_decode_length d)
        (Uchar.to_int (Uchar.utf_decode_uchar d) :: acc)
  in
  Array.of_list (go 0 [])

let of_chars cs =
  let b = Buffer.create (Array.length cs) in
  Array.iter (fun c -> Buffer.add_utf_8_uchar b (Uchar.of_int c)) cs;
  Str (Buffer.contents b)

let a = Char.code 'a'

let strings s =
  let cs = chars s in
  let n = Array.length cs in
  let shorter = Seq.take (3 + n) (sequence cs (fun _ -> Seq.empty)) in
  let replaced =
    Seq.filter_map
      (fun i ->
        if cs.(i) = a then None
        else
          let ys = Array.copy cs in
          ys.(i) <- a;
          Some ys)
      (Seq.init n Fun.id)
  in
  Seq.map of_chars (Seq.append shorter replaced)

(* The value with component [j] of [xs] replaced by each of its candidates,
   for each [j] in order, rebuilt by [make]. *)
let components xs elem make =
  let xs = Array.of_list xs in
  Seq.concat
    (Seq.init (Array.length xs) (fun j ->
         Seq.map
           (fun c ->
             let ys = Array.copy xs in
             ys.(j) <- c;
             make (Array.to_list ys))
           (elem j xs.(j))))

let rec candidates insert (g : P.graph) i v =
  let inner = candidates insert g in
  let all =
    match (g.nodes.(i), v) with
    | Bool, Bool true -> Seq.return (Bool false)
    | Int k, Int x -> List.to_seq (ints k x)
    | Float f32, Float x -> List.to_seq (floats f32 x)
    | Str, Str s -> strings s
    | List s, List xs ->
        Seq.map
          (fun ys -> List (Vec.of_list (Array.to_list ys)))
          (sequence (Array.of_list (Vec.to_list xs)) (inner s))
    | Map (_, vs), Map d ->
        (* A key has no candidates: only values shrink in place. *)
        let entry (k, x) = Seq.map (fun c -> (k, c)) (inner vs x) in
        let kty = Prop_gen.key_type g.tys.(i) in
        Seq.map
          (fun es -> Prop_gen.build_map insert kty (Array.to_list es))
          (sequence (Array.of_list (Dict.entries d)) entry)
    | Tuple slots, Tuple xs ->
        components xs (fun j -> inner (List.nth slots j)) (fun ys -> Tuple ys)
    | Record (item, fields), Record (_, xs) ->
        components (List.map snd xs)
          (fun j -> inner (snd (List.nth fields j)))
          (fun ys -> Record (item, List.combine (List.map fst fields) ys))
    | Variants vs, Variant (item, xs) ->
        let payload = List.assoc item vs in
        let own = List.filteri (fun j _ -> List.nth payload j = i) xs in
        Seq.append
          (List.to_seq (Prop_gen.minimal g i :: own))
          (components xs
             (fun j -> inner (List.nth payload j))
             (fun ys -> Variant (item, ys)))
    | _ -> Seq.empty
  in
  distinct v all

let limit = 1000

type 'f shrunk = { values : value list; failure : 'f; shrinks : int }

exception Spent

let shrink ~candidates ~run ~same values failure =
  let runs = ref 0 in
  (* The first candidate of a parameter, from [j] on, whose run fails as
     [failure] did, with the values it gives and its failure. *)
  let rec search values failure j =
    if j >= List.length values then None
    else
      let tried c =
        if !runs >= limit then raise Spent;
        incr runs;
        let ys = List.mapi (fun k x -> if k = j then c else x) values in
        match run ys with
        | Some f when same failure f -> Some (ys, f)
        | _ -> None
      in
      match Seq.find_map tried (candidates j (List.nth values j)) with
      | Some found -> Some found
      | None -> search values failure (j + 1)
  in
  let rec go values failure shrinks =
    match search values failure 0 with
    | Some (ys, f) -> go ys f (shrinks + 1)
    | None -> { values; failure; shrinks }
    | exception Spent -> { values; failure; shrinks }
  in
  go values failure 0
