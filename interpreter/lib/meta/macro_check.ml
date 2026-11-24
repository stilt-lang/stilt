(* The checks of a macro's patterns and templates (macros.patterns, macros.pattern-checks and macros.templates). *)

open Ast

type error = { code : Code.t; loc : loc; message : string }

let kinds = [ "expr"; "block"; "pattern"; "type"; "name"; "Name" ]

let error code loc fmt =
  Printf.ksprintf (fun message -> { code; loc; message }) fmt

(* The fragments of trees, each with its kind, if a pattern gives one, and
   the repetitions it is inside, outermost first, known by the positions of
   their [$]. *)
let rec bound_in reps acc (t : tree) =
  match t.desc with
  | Fragment (n, k) -> (n, k, reps) :: acc
  | Group (_, ts, _) -> List.fold_left (bound_in reps) acc ts
  | Repeat (ts, _, _) -> List.fold_left (bound_in (reps @ [ t.loc ])) acc ts
  | Token _ -> acc

let bound trees = List.rev (List.fold_left (bound_in []) [] trees)

let fragments pattern =
  List.filter_map
    (fun ((n : name), k, _) ->
      Option.map (fun (k : name) -> (n.desc, k.desc)) k)
    (bound [ pattern ])

let names trees =
  List.fold_left
    (fun names ((n : name), _, _) ->
      if List.mem n.desc names then names else names @ [ n.desc ])
    [] (bound trees)

let rec has_fragment (t : tree) =
  match t.desc with
  | Fragment _ -> true
  | Group (_, ts, _) | Repeat (ts, _, _) -> List.exists has_fragment ts
  | Token _ -> false

(* macros.pattern-checks: each fragment named once, with a kind, and each repetition with a
   fragment. *)
let named_errors (arm : macro_arm) =
  let seen = Hashtbl.create 8 in
  let errors = ref [] in
  let add e = errors := e :: !errors in
  let fragment (n : name) loc =
    if Hashtbl.mem seen n.desc then
      add
        (error Code.e0220 loc
           "the fragment `$%s` is already named in this pattern" n.desc)
    else Hashtbl.add seen n.desc ()
  in
  let rec walk (t : tree) =
    match t.desc with
    | Fragment (n, k) ->
        fragment n t.loc;
        Option.iter
          (fun (k : name) ->
            if not (List.mem k.desc kinds) then
              add
                (error Code.e0220 t.loc
                   "`%s` is no kind of fragment: a fragment is an `expr`, a \
                    `block`, a `pattern`, a `type`, a `name` or a `Name`"
                   k.desc))
          k
    | Group (_, ts, _) -> List.iter walk ts
    | Repeat (ts, _, _) ->
        if not (List.exists has_fragment ts) then
          add
            (error Code.e0220 t.loc
               "this repetition holds no fragment, so nothing tells how many \
                times it matches");
        List.iter walk ts
    | Token _ -> ()
  in
  walk arm.pattern;
  Option.iter
    (fun ((n : name), (k : name)) ->
      fragment n n.loc;
      if k.desc <> "block" then
        add
          (error Code.e0220 k.loc
             "a trailing block's fragment is a `block`, written `$%s: block`"
             n.desc))
    arm.block;
  List.rev !errors

(* macros.pattern-checks: what an [expr], [pattern] or [type] fragment may be followed by,
   which [None], the end of its group, is too. *)
let ends_fragment : tree option -> bool = function
  | None | Some { desc = Token (A_punct ("," | "=>") | A_sep); _ } -> true
  | Some _ -> false

(* What may follow the matchers before [rest], whose group ends with what
   [after] holds. A repetition may match nothing only with [*]. *)
let rec follow_of (rest : tree list) after =
  match rest with
  | [] -> after
  | { desc = Repeat (first :: _, _, "*"); _ } :: rest ->
      Some first :: follow_of rest after
  | { desc = Repeat (first :: _, _, _); _ } :: _ -> [ Some first ]
  | t :: _ -> [ Some t ]

let rec followed add (ms : tree list) after =
  match ms with
  | [] -> ()
  | m :: rest ->
      let follow = follow_of rest after in
      (match m.desc with
      | Fragment (n, Some k) when List.mem k.desc [ "expr"; "pattern"; "type" ]
        ->
          if not (List.for_all ends_fragment follow) then
            add
              (error Code.e0220 m.loc
                 "the %s fragment `$%s` is followed only by `,`, `;`, `=>` or \
                  the end of its group, since it could read on into anything \
                  else"
                 k.desc n.desc)
      | Group (_, ts, _) -> followed add ts [ None ]
      | Repeat (ts, sep, _) ->
          (* In a repetition, what follows its last matcher is its
             separator, or else its first matcher. *)
          let between =
            match sep with
            | Some s ->
                let atom = if s = "," then A_punct "," else A_sep in
                [ Some { desc = Token atom; loc = m.loc } ]
            | None -> follow_of ts []
          in
          followed add ts (between @ follow)
      | Fragment _ | Token _ -> ());
      followed add rest after

let pattern_errors (arm : macro_arm) =
  let errors = ref (List.rev (named_errors arm)) in
  followed (fun e -> errors := e :: !errors) [ arm.pattern ] [ None ];
  List.rev !errors

(* macros.templates: the repetitions of the pattern, at depth [depth], that the
   fragments inside a repetition of the template come from, among those
   whose outer repetitions are [chosen]. *)
let repeated bounds depth chosen ts =
  List.fold_left
    (fun found ((n : name), _, _) ->
      match List.assoc_opt n.desc bounds with
      | Some reps
        when List.length reps > depth
             && List.filteri (fun i _ -> i < depth) reps = chosen ->
          let r = List.nth reps depth in
          if List.mem r found then found else found @ [ r ]
      | _ -> found)
    [] (bound ts)

let template_errors (arm : macro_arm) =
  let bounds =
    List.map
      (fun ((n : name), _, reps) -> (n.desc, reps))
      (bound [ arm.pattern ])
    @ Option.to_list
        (Option.map (fun ((n : name), _) -> (n.desc, [])) arm.block)
  in
  let errors = ref [] in
  let add e = errors := e :: !errors in
  let rec item depth chosen (t : tree) =
    match t.desc with
    | Fragment (n, _) -> (
        match List.assoc_opt n.desc bounds with
        | None ->
            add
              (error Code.e0221 t.loc "the pattern binds no fragment `$%s`"
                 n.desc)
        | Some reps when List.length reps <> depth ->
            add
              (error Code.e0221 t.loc
                 "`$%s` is bound inside %d repetitions of the pattern, so it \
                  is named inside as many here, not %d"
                 n.desc (List.length reps) depth)
        | Some _ -> ())
    | Group (_, ts, _) -> List.iter (item depth chosen) ts
    | Repeat (ts, _, _) -> (
        match repeated bounds depth chosen ts with
        | [ r ] -> List.iter (item (depth + 1) (chosen @ [ r ])) ts
        | [] when not (List.exists has_fragment ts) ->
            add
              (error Code.e0221 t.loc
                 "this repetition names no fragment, so nothing tells how many \
                  times it repeats")
        | [] -> List.iter (item (depth + 1) chosen) ts
        | _ ->
            add
              (error Code.e0221 t.loc
                 "this repetition names fragments of two repetitions of the \
                  pattern, which may match different numbers of times"))
    | Token _ -> ()
  in
  List.iter (item 0 []) arm.template;
  List.rev !errors

let check_arm arm =
  match pattern_errors arm with [] -> template_errors arm | errors -> errors
