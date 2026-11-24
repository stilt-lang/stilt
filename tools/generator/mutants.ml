(* Csmith programs with exactly one planted mistake, annotated with the
   diagnostic the Reference requires for it. *)

open Code

(* The mistakes that [mutant] plants: the lines that make one, and the code of
   the one diagnostic the Reference requires for it, which is on the last of
   those lines. Each holds in any function body, whatever precedes it there,
   since the lines name nothing but what they declare. [in_context] holds
   those that name the function's parameters. *)
let mistakes =
  [
    ("E0311", [ "let planted: str = true" ]);
    ("E0211", [ "let planted = missing" ]);
    ("E0313", [ "let planted = (1, 2).2" ]);
    ("E0314", [ "let planted = \"text\".shout()" ]);
    ("E0315", [ "let planted = \"text\".contains()" ]);
    ("E0317", [ "let planted = \"a\" * \"b\"" ]);
    ("E0320", [ "let planted: u8 = 256" ]);
    ("E0329", [ "let planted = match true { true => 1 }" ]);
    ("E0323", [ "let planted = if true { 1 }" ]);
    ("E0312", [ "let planted = []" ]);
    ("E0208", [ "let (planted, planted) = (1, 2)" ]);
    ("E0210", [ "let i64 = 1" ]);
    ("E0324", [ "let planted = .len()" ]);
    ("E0401", [ "(1, 2).0 = 3" ]);
    ("E0403", [ "let planted = 1"; "planted = 2" ]);
    ( "E0404",
      [ "var planted = [1, 2]"; "for item in planted { planted.push(item) }" ]
    );
    ("E0216", [ "if true { break }" ]);
    ("E0322", [ "\"text\".len()" ]);
  ]

(* The parameters of the function whose first line is [signature], each as
   its name and type, written [name: Type]: the text between the parentheses
   after its name and type parameters, split at the commas outside brackets. *)
let parameters signature =
  match String.index_opt signature '(' with
  | None -> []
  | Some start ->
      let depth = ref 0 and current = Buffer.create 16 and out = ref [] in
      let stop = ref false in
      String.iteri
        (fun i c ->
          if i > start && not !stop then
            match c with
            | ')' when !depth = 0 ->
                out := Buffer.contents current :: !out;
                stop := true
            | ',' when !depth = 0 ->
                out := Buffer.contents current :: !out;
                Buffer.clear current
            | '(' | '<' | '[' ->
                incr depth;
                Buffer.add_char current c
            | '>' when signature.[i - 1] = '-' -> Buffer.add_char current c
            | ')' | '>' | ']' ->
                decr depth;
                Buffer.add_char current c
            | c -> Buffer.add_char current c)
        signature;
      List.rev !out
      |> List.filter_map (fun p ->
          match String.split_on_char ':' (String.trim p) with
          | name :: (_ :: _ as ty) when not (String.contains name ' ') ->
              Some (name, String.trim (String.concat ":" ty))
          | _ -> None)

(* The mistakes that depend on the function they are planted in, each from a
   [let] parameter [(name, type)] of it: modifying the parameter, which only
   [inout] ones allow (modes.what-can-be-modified), and binding it at a type
   it doesn't have (types.mismatch). *)
let in_context =
  [
    (fun (name, _) -> ("E0403", [ Printf.sprintf "%s = %s" name name ]));
    (fun (name, ty) ->
      let other = if ty = "str" then "bool" else "str" in
      ("E0311", [ Printf.sprintf "let planted: %s = %s" other name ]));
  ]

(* The lines of the mistake of [kind] in the function whose first line is
   [signature], the last annotated with the diagnostic the Reference requires
   for it. A mistake that depends on the function takes the turn of a fixed one
   when the function has a parameter to make it from, and a body that opens on
   its first line. *)
let annotated ?(signature = "") kind =
  let all = List.length mistakes + List.length in_context in
  let k = kind mod all in
  let fixed = List.length mistakes in
  let code, lines =
    match parameters signature with
    | p :: _ when k >= fixed && String.ends_with ~suffix:"{" signature ->
        (List.nth in_context (k - fixed)) p
    | _ -> List.nth mistakes (k mod fixed)
  in
  List.mapi
    (fun i text ->
      if i = List.length lines - 1 then text ^ " //~ ERROR " ^ code else text)
    lines

(* [n] of the functions among [items], picked by [seed], or all of them if
   they are fewer. *)
let targets items seed n =
  let functions =
    List.filter
      (function
        | (_, text) :: _ -> String.starts_with ~prefix:"fn " text | [] -> false)
      items
  in
  let r = Pick.make seed in
  let rec pick chosen = function
    | 0 -> List.rev chosen
    | n ->
        let left = List.filter (fun f -> not (List.memq f chosen)) functions in
        if left = [] then List.rev chosen
        else
          pick
            (List.nth left (Pick.below r (List.length left)) :: chosen)
            (n - 1)
  in
  pick [] n

(* The files of the program from [seed] whose text is [text], and whose module
   of macros, if it has one, holds the mistake [place] if it is there. *)
let files seed m place text =
  match (m, place) with
  | Some (m : Macro_kinds.t), Some place ->
      let edit =
        match place with
        | Macro_mistakes.Module edit -> edit
        | Use _ -> fun _ -> None
      in
      let dir = Printf.sprintf "seed_%d" seed in
      [
        (Filename.concat dir "main.lt", text);
        (Filename.concat dir (m.module_name ^ ".lt"), Macro_module.text ~edit m);
      ]
  | _ -> [ (Printf.sprintf "seed_%d.lt" seed, text) ]

(* A program from [seed] with [count] planted mistakes, or one in each of its
   functions if it has fewer, each at the top of a different function, and
   each annotated with the diagnostic the Reference requires for it (conformance.diagnostic-lines). Each body reports its own mistake, and no mistake reaches
   another body, since the lines name nothing but what they declare and the
   parameters of their own function. The
   mistakes take turns, so that each kind is planted as often as the others.
   The planted lines come first in the body, so a statement always follows
   them, which the unused value of [E0322] needs (expressions.unused-values). A program
   with macros is a directory program, whose first mistake is one of
   Macro_mistakes: in a use, among the uses of its macros, or in its module of
   macros, whose macros it then doesn't use, since a failed type use leaves
   the value it annotates to be typed alone, and a literal deep in it to the
   type its kind defaults to, where it may not fit (macros.failed-uses; numbers.literal-defaults). *)
let mutant ?(count = 1) seed =
  let m =
    if Csmith_macros.wanted seed then Some (Macro_module.make seed) else None
  in
  let macro = Option.map (fun m -> Macro_mistakes.plant m (seed * count)) m in
  let used = match macro with Some (Macro_mistakes.Use _) -> m | _ -> None in
  let items =
    Option.fold ~none:[]
      ~some:(fun (m : Macro_kinds.t) -> [ line ("meta use " ^ m.module_name) ])
      m
    @ Csmith.items ?macros:used seed
  in
  let lines signature i =
    match (i, macro) with
    | 0, Some (Macro_mistakes.Use lines) -> lines
    | _ -> annotated ~signature ((seed * count) + i)
  in
  let first, targets =
    match macro with
    | Some (Macro_mistakes.Module _) -> (1, targets items seed (count - 1))
    | _ -> (0, targets items seed count)
  in
  let plant item =
    let rec find i = function
      | [] -> None
      | t :: rest -> if t == item then Some i else find (i + 1) rest
    in
    match (find 0 targets, item) with
    | Some i, signature :: body ->
        signature
        :: List.map (fun text -> (1, text)) (lines (snd signature) (first + i))
        @ body
    | _ -> item
  in
  files seed m macro
    (String.concat "\n" (List.map render (List.map plant items)))
