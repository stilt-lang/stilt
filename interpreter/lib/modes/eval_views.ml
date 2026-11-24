(* The native items of std.view (views.making-view, views.functions-of-views, views.making-iterator and views.adapters). A view's
   value is the part of its source that it views: nothing can change the
   source while the view lives (views.change-while-viewed), so a copy of the part can't be told
   from a window into it (reference/rationale/13-modes.md, Views). *)

open Value

let int = function Int a -> a | _ -> invalid_arg "Eval_views.int"

(* The part of a string or a list from [start] up to [stop], which [slice]
   gives (std.lists and std.str) and a view views, counted as [slice] counts (std.lists and std.str). *)
let slice v start stop =
  let length, what =
    match v with
    | Str s ->
        let n = String.length s in
        (n, Printf.sprintf "a string of %d bytes" n)
    | List xs ->
        let n = Vec.length xs in
        (n, Printf.sprintf "a list of length %d" n)
    | _ -> invalid_arg "Eval_views.slice"
  in
  if not (0L <= start && start <= stop && stop <= Int64.of_int length) then
    Fault.panic "bounds" "the range %Ld..%Ld is out of bounds for %s" start stop
      what
  else
    let start = Int64.to_int start and stop = Int64.to_int stop in
    match v with
    | Str s ->
        if not (Strings.is_boundary s start && Strings.is_boundary s stop) then
          Fault.panic "utf8-boundary" "the range %d..%d splits a UTF-8 sequence"
            start stop
        else Str (String.sub s start (stop - start))
    | List xs -> List (Vec.sub xs start stop)
    | _ -> invalid_arg "Eval_views.slice"

let length = function
  | Str s -> String.length s
  | List xs -> Vec.length xs
  | _ -> invalid_arg "Eval_views.length"

(* [impl<T> View<T>] (views.making-view and views.functions-of-views). *)
let view_native name args =
  match name with
  | "of" -> slice args.(0) (int args.(1)) (int args.(2))
  | "all" | "copy" -> args.(0)
  | "len" -> Int (Int64.of_int (length args.(0)))
  | "is_empty" -> Bool (length args.(0) = 0)
  | "view" -> slice args.(0) (int args.(1)) (int args.(2))
  | _ -> invalid_arg ("Eval_views.view_native: " ^ name)

(* The functions of the module: [get], [chars] and [bytes] (views.functions-of-views), and
   the iterators [range] and [of_map] (views.making-iterator). *)
let function_native name args =
  match (name, args) with
  | "get", [| List xs; Int i |] ->
      if 0L <= i && i < Int64.of_int (Vec.length xs) then
        some (Vec.get xs (Int64.to_int i))
      else none
  | "chars", [| Str s |] ->
      Iter (Elements (List.map (fun c -> Str c) (Strings.chars s)))
  | "bytes", [| Str s |] ->
      let byte c = Int (Int64.of_int (Char.code c)) in
      Iter (Elements (List.map byte (List.of_seq (String.to_seq s))))
  | "range", [| Int first; Int last |] -> Iter (Range (first, last))
  | "of_map", [| Map d |] ->
      Iter (Elements (List.map (fun (k, v) -> Tuple [ k; v ]) (Dict.entries d)))
  | _ -> invalid_arg ("Eval_views.function_native: " ^ name)

(* [impl<T> Iter<T>]: the makers of views.making-iterator that take a list or a view of
   one, and the adapters of views.adapters, which run nothing, and the consumers of
   views.consumers. *)
let iter_native t fr loc name targs args =
  let it () =
    match args.(0) with Iter it -> it | _ -> invalid_arg "Eval_views.iter"
  in
  let fn i =
    match args.(i) with Fn f -> f | _ -> invalid_arg "Eval_views.fn"
  in
  let other () =
    match args.(1) with Iter it -> it | _ -> invalid_arg "Eval_views.other"
  in
  match (name, args.(0)) with
  | ("of" | "of_view"), List xs -> Iter (Elements (Vec.to_list xs))
  | "map", _ -> Iter (Mapped (it (), fn 1))
  | "filter", _ -> Iter (Filtered (it (), fn 1))
  | "take", _ -> Iter (Taken (it (), int args.(1)))
  | "skip", _ -> Iter (Skipped (it (), int args.(1)))
  | "take_while", _ -> Iter (Taken_while (it (), fn 1))
  | "skip_while", _ -> Iter (Skipped_while (it (), fn 1))
  | "enumerate", _ -> Iter (Enumerated (it (), int args.(1)))
  | "zip", _ -> Iter (Zipped (it (), other ()))
  | "chain", _ -> Iter (Chained (it (), other ()))
  | _ -> Eval_iters.consume t fr loc name targs (it ()) args

let native t fr loc (callee : Tast.callee) targs args =
  match callee with
  | Function { name; _ } -> function_native name args
  | Member ({ name = "View"; _ }, name) -> view_native name args
  | Member ({ name = "Iter"; _ }, name) -> iter_native t fr loc name targs args
  | Member _ | Trait_method _ | Operation _ -> invalid_arg "Eval_views.native"
