(* The stress suite: bodies built to stress inference (Goals,
   Workloads). Each program holds a function of one of four kinds, which
   [main] calls and prints: deep nesting, a long method chain, a large [match]
   or [if] tree, and literals whose type is known only at the end of the body.
   The kinds take turns from one seed to the next, so a run of seeds holds as
   many of each.

   Like csmith programs, these are well-typed and terminating by construction.
   Their arithmetic wraps and divides only by positive constants, so they run
   to their end. Every random choice is bound with [let] before the next one,
   since OCaml leaves the order of evaluating arguments open, and a seed must
   fix its program. *)

open Code

(* The name [prefix] numbered [n]. No prefix here is [i], [u] or [f], whose
   numbered names can be primitive type names. *)
let var prefix n = prefix ^ string_of_int n

(* A small constant, which fits every integer type. *)
let small r = string_of_int (Pick.between r 0 9)

(* Wrapping arithmetic on two of [vars] or small constants. *)
let arith r vars =
  let operand () =
    if vars = [] || Pick.chance r 0.3 then small r else Pick.one r vars
  in
  let a = operand () in
  let op = Pick.one r [ "+%"; "-%"; "*%" ] in
  let b = operand () in
  Printf.sprintf "%s %s %s" a op b

(* Deep nesting *)

(* An [i64] expression nested as deep as [open_] more brackets allow, at
   most three a level. Each level is a block that binds a variable, then goes
   on in itself, in an [if], in a [match], or in a closure that it calls; a
   level opens its block's brace and the [if]'s, the [match]'s and its arm's,
   or the closure's, so a program nests as deep as lexical.nesting lets it. *)
let rec nesting r ~open_ ~level vars =
  if open_ < 3 then line (arith r vars)
  else
    let v = var "v" level in
    let inside = v :: vars in
    let kind = Pick.below r 4 in
    let opens = match kind with 0 -> 1 | 2 -> 3 | _ -> 2 in
    let deeper vars =
      nesting r ~open_:(open_ - opens) ~level:(level + 1) vars
    in
    let rest =
      match kind with
      | 0 -> deeper inside
      | 1 ->
          let yes = deeper inside in
          let no = arith r inside in
          block_lines (Printf.sprintf "if %s %% 2 == 0 {" v) yes "} else {"
          @ nest (line no)
          @ line "}"
      | 2 ->
          let zero = deeper inside in
          let one = arith r inside in
          let other = arith r inside in
          block_lines
            (Printf.sprintf "match %s %% 3 {" v)
            (block_lines "0 => {" zero "}"
            @ line ("1 => " ^ one)
            @ line ("_ => " ^ other))
            "}"
      | _ ->
          let g = var "g" level and w = var "w" level in
          block_lines
            (Printf.sprintf "let %s = |%s: i64| {" g w)
            (deeper (w :: inside))
            "}"
          @ line (Printf.sprintf "%s(%s)" g v)
    in
    let value = arith r vars in
    block_lines "{" (line (Printf.sprintf "let %s = %s" v value) @ rest) "}"

let nested r =
  (* The function's body opens one level, and a call [g(v)] one more at the
     deepest, so 250 leaves room under the limit of 256. *)
  let open_ = Pick.between r 100 250 in
  ( block_lines "fn nested(n: i64) -> i64 {"
      (nesting r ~open_ ~level:0 [ "n" ])
      "}",
    "nested(3)} {nested(-7)} {nested(100)" )

(* Long method chains *)

(* The element types of a chain's lists. *)
type element = Int | Text | Flag | Pair (* [(i64, str)] *)

(* A link of a chain on a list of [element]s, and the element type after it.
   No link lengthens a list, and a string grows by one character at most. *)
let link r element =
  let k = string_of_int (Pick.between r 2 9) in
  Pick.one r
    (match element with
    | Int ->
        [
          (".map(|x| x +% " ^ k ^ ")", Int);
          (".map(|x| x *% " ^ k ^ ")", Int);
          (".filter(|x| x % " ^ k ^ " != 0)", Int);
          (".map(|x| x % 2 == 0)", Flag);
          (".map(|x| \"{x}\")", Text);
          (".reversed()", Int);
          (".skip(1)", Int);
        ]
    | Text ->
        [
          (".map(.len())", Int);
          (".map(|s| s.ascii_upper())", Text);
          (".filter(|s| s.len() > 1)", Text);
          (".map(|s| \"{s}!\")", Text);
          (".enumerate(" ^ k ^ ")", Pair);
          (".map(.is_empty())", Flag);
        ]
    | Flag ->
        [
          (".map(|b| !b)", Flag);
          (".map(|b| if b { " ^ k ^ " } else { 1 })", Int);
          (".filter(|b| b)", Flag);
          (".map(|b| \"{b}\")", Text);
        ]
    | Pair ->
        [
          (".map(.0)", Int);
          (".map(.1)", Text);
          (".map(|p| p.0 +% p.1.len())", Int);
          (".filter(|p| p.0 % 2 == 0)", Pair);
        ])

(* The link that ends a chain with an [i64]. *)
let total = function
  | Int -> ".fold(0, |a, x| a +% x)"
  | Text -> ".fold(0, |a, s| a +% s.len())"
  | Flag -> ".filter(|b| b).len()"
  | Pair -> ".fold(0, |a, p| a +% p.0)"

let chain r =
  let rec links n element =
    if n = 0 then [ total element ]
    else
      let text, next = link r element in
      text :: links (n - 1) next
  in
  let lines = links (Pick.between r 50 200) Int in
  ( block_lines "fn chain(xs: List<i64>) -> i64 {"
      (line "xs" @ List.map (fun text -> (1, text)) lines)
      "}",
    "chain([3, 1, 4, 1, 5, 9, 2, 6, 5, 3])" )

(* Large [match] and [if] trees *)

(* A [match] on an integer, with literal, or-pattern and guarded arms. The
   first arm's body fixes the type of the others. *)
let int_match r =
  let arms = Pick.between r 100 400 in
  let values = List.init (3 * arms) Fun.id in
  let unused = ref values in
  let take () =
    let v = Pick.one r !unused in
    unused := List.filter (( <> ) v) !unused;
    string_of_int v
  in
  let ty, body =
    Pick.one r
      [
        ("i64", fun () -> "n +% " ^ small r);
        ("str", fun () -> Printf.sprintf "\"{n}%s\"" (small r));
        ("bool", fun () -> "n % " ^ string_of_int (Pick.between r 2 9) ^ " == 0");
      ]
  in
  let arm _ =
    let pattern =
      match Pick.below r 6 with
      | 0 ->
          let a = take () in
          a ^ " | " ^ take ()
      | 1 -> "m if m > " ^ string_of_int (Pick.below r (3 * arms))
      | _ -> take ()
    in
    pattern ^ " => " ^ body ()
  in
  let arms = List.init arms arm in
  let last = "_ => " ^ body () in
  ( block_lines
      ("fn pick(n: i64) -> " ^ ty ^ " {")
      (block_lines "let r = match n {"
         (List.map (fun a -> (0, a)) (arms @ [ last ]))
         "}"
      @ line "r")
      "}",
    "pick(5)} {pick(17)} {pick(250)} {pick(-1)" )

(* A [match] on a type of many variants, without a catch-all, so that
   exhaustiveness must be shown variant by variant. *)
let variant_match r =
  let n = Pick.between r 50 150 in
  let variants =
    List.init n (fun i ->
        match i mod 3 with
        | 0 -> (var "V" i, None, string_of_int i)
        | 1 -> (var "V" i, Some "i64", Printf.sprintf "x +%% %d" i)
        | _ -> (var "V" i, Some "str", Printf.sprintf "x.len() +%% %d" i))
  in
  let decl =
    "type Big = "
    ^ String.concat " "
        (List.map
           (fun (c, payload, _) ->
             match payload with
             | None -> "| " ^ c
             | Some t -> Printf.sprintf "| %s(%s)" c t)
           variants)
  in
  let arm (c, payload, body) =
    (0, (if payload = None then c else c ^ "(x)") ^ " => " ^ body)
  in
  let value i =
    match List.nth variants (i mod n) with
    | c, None, _ -> c
    | c, Some "i64", _ -> c ^ "(" ^ string_of_int i ^ ")"
    | c, _, _ -> c ^ "(\"abc\")"
  in
  ( line decl @ line ""
    @ block_lines "fn size(b: Big) -> i64 {"
        (block_lines "match b {" (List.map arm variants) "}")
        "}",
    String.concat "} {"
      (List.map
         (fun i -> "size(" ^ value i ^ ")")
         [ 0; 1; 2; n - 1; Pick.below r n ]) )

(* A [match] on a pair of variant types, with an arm for every pair of
   variants and no catch-all. *)
let pair_match r =
  let n = Pick.between r 10 14 in
  let names prefix = List.init n (var prefix) in
  let decl name prefix =
    "type " ^ name ^ " = "
    ^ String.concat " " (List.map (fun c -> "| " ^ c) (names prefix))
  in
  let arms =
    List.concat_map
      (fun a ->
        List.map
          (fun b -> (0, Printf.sprintf "(%s, %s) => %s" a b (small r)))
          (names "B"))
      (names "A")
  in
  ( line (decl "Left" "A")
    @ line (decl "Right" "B")
    @ line ""
    @ block_lines "fn cell(a: Left, b: Right) -> i64 {"
        (block_lines "match (a, b) {" arms "}")
        "}",
    Printf.sprintf "cell(A0, B0)} {cell(A%d, B%d)} {cell(A%d, B0)" (n - 1)
      (n - 1) (Pick.below r n) )

(* An [if] … [else if] chain of many branches. *)
let if_chain r =
  let branches = Pick.between r 100 400 in
  let cond () =
    let k = string_of_int (Pick.below r 1000) in
    Pick.one r
      [
        "n < " ^ k;
        "n == " ^ k;
        "n % " ^ string_of_int (Pick.between r 2 50) ^ " == 0";
      ]
  in
  let branch i =
    let opening = if i = 0 then "if " else "} else if " in
    let c = cond () in
    (0, opening ^ c ^ " {") :: nest (line (arith r [ "n" ]))
  in
  let branches = List.concat (List.init branches branch) in
  let otherwise = arith r [ "n" ] in
  ( block_lines "fn grade(n: i64) -> i64 {"
      (branches @ line "} else {" @ nest (line otherwise) @ line "}")
      "}",
    "grade(0)} {grade(17)} {grade(999)} {grade(-5)" )

(* A balanced tree of [if]s, [depth] levels deep, splitting the integers at
   each level. *)
let if_tree r =
  let depth = Pick.between r 7 9 in
  let rec tree level lo hi =
    if level = depth then line (arith r [ "n" ])
    else
      let mid = (lo + hi) / 2 in
      let below = tree (level + 1) lo mid in
      let above = tree (level + 1) mid hi in
      block_lines (Printf.sprintf "if n < %d {" mid) below "} else {"
      @ nest above @ line "}"
  in
  ( block_lines "fn split(n: i64) -> i64 {" (tree 0 0 1024) "}",
    "split(0)} {split(511)} {split(512)} {split(2000)" )

let trees r =
  (Pick.one r [ int_match; variant_match; pair_match; if_chain; if_tree ]) r

(* Literals whose type is known late *)

(* A statement of a late body. It reads the integers in [ints], adds those it
   binds, and names its variables with [fresh]. *)
let late_statement r ints fresh =
  let pick () = Pick.one r !ints in
  match Pick.below r 8 with
  | 0 | 1 -> line (Printf.sprintf "a = %s" (arith r !ints))
  | 2 -> line (Printf.sprintf "b = %s" (arith r !ints))
  | 3 ->
      let d = fresh "d" in
      let l = line (Printf.sprintf "let %s = %s" d (arith r !ints)) in
      ints := d :: !ints;
      l
  | 4 ->
      let x = pick () in
      line (Printf.sprintf "xs.push(%s %% %d)" x (Pick.between r 2 9))
  | 5 ->
      let x = pick () in
      let bound = small r in
      block_lines
        (Printf.sprintf "if %s > %s {" x bound)
        (line (Printf.sprintf "b = b +%% %s" (small r)))
        "}"
  | 6 ->
      let o = fresh "o" in
      let test = pick () in
      let value = pick () in
      let l =
        line
          (Printf.sprintf "let %s = if %s %% 2 == 0 { Some(%s) } else { None }"
             o test value)
      in
      ints := Printf.sprintf "(%s else %s)" o (small r) :: !ints;
      l
  | _ -> line (Printf.sprintf "f = f * 0.5 + %s.25" (small r))

(* A body whose integer and float literals stay open until its last
   statements fix their types with annotations. Until then, every operation
   on them is an operator, since a method call would need its receiver's
   type, which would make it [i64] or [f64] (types.known-types). *)
let late r =
  let int_ty = Ty.int_name (Pick.one r Ty.int_kinds) in
  let float_ty = Ty.float_name (Pick.one r Ty.float_kinds) in
  let ints = ref [ "a"; "b" ] in
  let count = ref 0 in
  let fresh prefix =
    incr count;
    var prefix !count
  in
  let body =
    List.concat
      (List.init (Pick.between r 100 300) (fun _ -> late_statement r ints fresh))
  in
  ( block_lines
      (Printf.sprintf "fn late() -> (%s, %s) {" int_ty float_ty)
      (line "var a = 3" @ line "var b = 5" @ line "var xs = []"
     @ line "var f = 0.5"
      @ block_lines "for i in 0..12 {"
          (line "a = a +% i" @ line "xs.push(b % 7)")
          "}"
      @ body
      @ line
          (Printf.sprintf "let total: %s = xs.fold(0, |s, x| s +%% x) +%% %s"
             int_ty
             (String.concat " +% " !ints))
      @ line (Printf.sprintf "let g: %s = f" float_ty)
      @ line "(total, g)")
      "}",
    "late()" )

(* Programs *)

let kinds = [ nested; chain; trees; late ]

(* The program of [seed]: its function, then [main], which prints what the
   function returns for a few arguments. *)
let program seed =
  let r = Pick.make seed in
  let items, calls = (List.nth kinds (seed mod List.length kinds)) r in
  render items ^ "\n"
  ^ render
      (block_lines "fn main() / io {" (line ("print(\"{" ^ calls ^ "}\")")) "}")
