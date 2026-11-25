(* Csmith-style programs: well-typed, terminating [core] programs that print
   what they compute, for differential testing.

   Generation is type-directed. Each expression is made for the type its
   context expects, from the variables, functions and types in scope, so a
   program checks by construction. It terminates by construction too: every
   loop runs a bounded number of times, a function calls only the functions
   declared before it, and the work of each body is estimated and kept under
   a budget. Operands that could make an operator panic are masked so that
   they can't, so a program runs to its end and prints what it computes. Its
   tests, doc examples and properties, which come last, may fail. *)

open Code
open Context
open Ty

(* A record or variant type, whose fields and payloads use only the types
   declared before it, so that no type contains itself. *)
let type_decl p ~pub =
  let r = p.r in
  let name = fresh p "T" in
  let d =
    if Pick.chance r 0.5 then
      Record
        (Pick.times (Pick.between r 1 4) (fun () ->
             (fresh p "fd", random_ty p 2)))
    else
      Variants
        (Pick.times (Pick.between r 1 4) (fun () ->
             ( fresh p "C",
               Pick.times (Pick.between r 0 2) (fun () -> random_ty p 1) )))
  in
  let text =
    match d with
    | Record fields ->
        let fields = List.map (fun (f, t) -> f ^ ": " ^ to_string t) fields in
        "type " ^ name ^ " = { " ^ String.concat ", " fields ^ " }"
    | Variants cases ->
        let case (c, payload) =
          if payload = [] then c
          else c ^ "(" ^ String.concat ", " (List.map to_string payload) ^ ")"
        in
        "type " ^ name ^ " = "
        ^ String.concat " " (List.map (fun c -> "| " ^ case c) cases)
  in
  p.decls <- p.decls @ [ (name, d) ];
  line ((if pub then "pub " else "") ^ text)

let signature p f names ~pub =
  let params =
    List.map2
      (fun (inout, t) name ->
        (if inout then "inout " else "") ^ name ^ ": " ^ to_string t)
      f.params names
  in
  let ret = if f.ret = Unit then "" else " -> " ^ to_string f.ret in
  let row = if f.raises then " / raise<" ^ p.fault ^ ">" else "" in
  (if pub then "pub " else "")
  ^ "fn " ^ f.fname ^ "(" ^ String.concat ", " params ^ ")" ^ ret ^ row ^ " {"

let function_ p ~budget ~pub =
  let r = p.r in
  let fname = fresh p "g" in
  let params =
    Pick.times (Pick.between r 0 3) (fun () ->
        (Pick.chance r 0.2, random_ty p 2))
  in
  let names = List.map (fun _ -> fresh p "p") params in
  let ret = if Pick.chance r 0.2 then Unit else random_ty p 2 in
  let raises = Pick.chance r 0.25 in
  let b = { p; budget; spent = 0 } in
  let sc =
    {
      vars =
        List.rev_map2
          (fun (inout, ty) name -> { name; ty; mutable_ = inout })
          params names;
      frozen = [];
      loop = false;
      may_raise = raises;
      io = false;
      returns = Some ret;
      weight = 1;
    }
  in
  let sc, body = Statements.stmts b sc ~depth:3 (Pick.between r 1 5) in
  let result =
    if ret = Unit then []
    else line (Expr.expr b sc ~depth:3 ~known:false ret).text
  in
  let f = { fname; params; ret; raises; cost = max 1 b.spent } in
  p.fns <- p.fns @ [ f ];
  (f, block_lines (signature p f names ~pub) (body @ result) "}")

(* The arguments that [main] passes [f], with the lines that declare a
   variable for each [inout] one, and the scope after them. *)
let arguments b sc f =
  List.fold_left
    (fun (sc, setup, args) (inout, t) ->
      let e = Expr.expr b sc ~depth:2 ~known:false t in
      if inout then
        let a = fresh b.p "a" in
        ( declare sc a t ~mutable_:true,
          setup
          @ [ (0, Printf.sprintf "var %s: %s = %s" a (to_string t) e.text) ],
          args @ [ (Some a, "inout " ^ a) ] )
      else (sc, setup, args @ [ (None, e.text) ]))
    (sc, [], []) f.params

(* The lines that make [call] and print what [f] returns or raises. *)
let shown b sc f call =
  let result = fresh b.p "r" in
  match (f.ret, f.raises) with
  | Unit, false -> [ (0, call) ]
  | Unit, true ->
      line
        (Printf.sprintf
           "try %s catch e because \"main shows it\" => print(\"%s raised \
            {e}\")"
           call f.fname)
  | ty, false ->
      [
        (0, Printf.sprintf "let %s: %s = %s" result (to_string ty) call);
        (0, Printf.sprintf "print(\"%s: {%s}\")" f.fname result);
      ]
  | ty, true ->
      let fallback = Expr.expr b sc ~depth:2 ~known:false ty in
      [
        ( 0,
          Printf.sprintf
            "let %s: %s = try %s catch e because \"main shows it\" => { \
             print(\"%s raised {e}\"); %s }"
            result (to_string ty) call f.fname fallback.text );
        (0, Printf.sprintf "print(\"%s: {%s}\")" f.fname result);
      ]

(* [lines], then the lines that call [f] and print what it returns, raises, or
   leaves in its [inout] arguments. *)
let exercise b (sc, lines) f =
  let sc, setup, args = arguments b sc f in
  let call = call_text f.fname (List.map snd args) in
  let shown = shown b sc f call in
  let changed =
    List.filter_map
      (fun (slot, _) ->
        Option.map (fun a -> (0, Printf.sprintf "print(\"%s: {%s}\")" a a)) slot)
      args
  in
  (sc, lines @ setup @ shown @ changed)

(* [main] computes some values of its own, then calls every function and
   prints what each returns, raises, or leaves in its [inout] arguments, then,
   given the seed [arrays], uses that seed's arrays, and given the seed
   [reflect], reflects on values of that seed's types, then, given a module of
   macros and its seed, uses its macros, then, given the seed [effects],
   handles that seed's effects, the items of each of these coming back beside
   it, then, given the seed [par], makes that seed's calls of [std.par], and
   given the seeds [views], [unicode] and [deep], views the fields of that
   seed's records, uses its text beyond ASCII, and makes its deep recursions
   and large lists. *)
(* [main]'s first statements, drawn again, up to [tries] times, while one of
   them would leave [main] with [return]: they come before the calls of every
   function and every feature's lines, which would then never run. *)
let rec staying b sc tries =
  let spent = b.spent in
  let sc', lines = Statements.stmts b sc ~depth:3 (Pick.between b.p.r 2 6) in
  if tries = 0 || not (List.exists (fun (_, l) -> mentions "return" l) lines)
  then (sc', lines)
  else (
    b.spent <- spent;
    staying b sc (tries - 1))

let main_with ?(pub = false) ?(redraw = true) ?arrays ?reflect ?macros ?par
    ?cycles ?effects ?views ?unicode ?deep ?generics p =
  let b = { p; budget = 20_000; spent = 0 } in
  let sc =
    {
      vars = [];
      frozen = [];
      loop = false;
      may_raise = false;
      io = true;
      returns = Some Unit;
      weight = 1;
    }
  in
  let sc, setup = staying b sc (if redraw then 10 else 0) in
  let sc, calls = List.fold_left (exercise b) (sc, []) p.fns in
  let items, arrays =
    Option.fold ~none:([], []) ~some:(Csmith_arrays.uses p sc) arrays
  in
  let reflected, reflection =
    Option.fold ~none:([], []) ~some:(Csmith_reflect.uses p sc) reflect
  in
  let functions, uses =
    Option.fold ~none:([], [])
      ~some:(fun (m, seed) -> Csmith_macros.uses m p sc seed)
      macros
  in
  let handled, handling =
    Option.fold ~none:([], []) ~some:(Csmith_effects.uses p sc) effects
  in
  let parallel = Option.fold ~none:[] ~some:(Csmith_par.calls p sc) par in
  let linked, links =
    Option.fold ~none:([], []) ~some:(Csmith_cycles.uses p sc) cycles
  in
  let viewed, viewing =
    Option.fold ~none:([], []) ~some:(Csmith_views.uses p sc) views
  in
  let texts, text =
    Option.fold ~none:([], []) ~some:(Csmith_text.uses p) unicode
  in
  let recursive, recursion =
    Option.fold ~none:([], []) ~some:Csmith_deep.uses deep
  in
  let traits, generic =
    Option.fold ~none:([], []) ~some:(Csmith_generics.uses p sc) generics
  in
  ( items @ reflected @ functions @ handled @ linked @ viewed @ texts
    @ recursive @ traits,
    block_lines
      ((if pub then "pub " else "") ^ "fn main() / io {")
      (setup @ calls @ arrays @ reflection @ uses @ handling @ parallel @ links
     @ viewing @ text @ recursion @ generic)
      "}" )

(* The [main] of a program in which [main]'s statements are drawn once, as the
   scale mode's port to Stilt draws them. *)
let main ?pub ?par p = snd (main_with ?pub ~redraw:false ?par p)

(* A property (tests.property-form): a closure of one or two parameters, of types of at
   most one level, whose body is a condition that may fail and may raise, and
   performs no [io]. It runs up to 1,100 times, so its body's work has a small
   budget. *)
let property p =
  let r = p.r in
  let b = { p; budget = 200; spent = 0 } in
  let params =
    Pick.times (Pick.between r 1 2) (fun () ->
        { name = fresh p "q"; ty = random_ty p 1; mutable_ = false })
  in
  let sc =
    {
      vars = List.rev params;
      frozen = [];
      loop = false;
      may_raise = true;
      io = false;
      returns = None;
      weight = 1;
    }
  in
  let typed v = v.name ^ ": " ^ Ty.to_string v.ty in
  "/// prop: |"
  ^ String.concat ", " (List.map typed params)
  ^ "| " ^ (Expr.cond b sc ~depth:2).text

(* A test, documented by doc examples (program.test-declarations and program.doc-examples) and perhaps a
   property (tests.property-form): statements, then an [assert], which may fail, in a body
   that may raise, as each example may. The examples' and the property's names
   resolve at module level, so they see no variable. *)
let test_decl p =
  let r = p.r in
  let b = { p; budget = 2_000; spent = 0 } in
  let sc =
    {
      vars = [];
      frozen = [];
      loop = false;
      may_raise = true;
      io = true;
      returns = Some Unit;
      weight = 1;
    }
  in
  let name = fresh p "t" in
  let examples =
    Pick.times (Pick.between r 0 2) (fun () ->
        "/// ex: " ^ (Expr.cond b sc ~depth:2).text)
  in
  let examples = examples @ if Pick.chance r 0.25 then [ property p ] else [] in
  let sc', body = Statements.stmts b sc ~depth:2 (Pick.between r 0 3) in
  let claim = "assert " ^ (Expr.cond b sc' ~depth:2).text in
  (if examples = [] then []
   else line ("/// Checks " ^ name ^ ".") @ List.concat_map line examples)
  @ block_lines ("test \"" ^ name ^ "\" {") (body @ line claim) "}"

(* The tests of a program whose items [p] holds, from a stream of their own,
   so that the items before them are those of the program without tests. *)
let tests p seed =
  let p = { p with r = Pick.make (Hashtbl.hash (seed, "tests")) } in
  Pick.times (Pick.between p.r 1 3) (fun () -> test_decl p)

(* The items of a program made from [seed]: its types, then its functions,
   then [main], which uses the seed's arrays when [arrays], reflects when
   [reflect], uses the macros of the module [macros], handles its effects when
   [effects], makes its calls of [std.par] when [par] and links handles into
   cycles when [cycles], views fields when [views], uses text beyond ASCII
   when [unicode], recurses deeply when [deep] and declares a trait and generic
   functions when [generics], then the items its arrays,
   its reflection, its uses of macros, its effects, its cycles, its views, its
   text and its recursions need. *)
(* Whether the program made from [seed] panics where its arithmetic overflows
   or divides by zero, one program in ten, so that the implementations are
   compared on panics too: their kinds and places (numbers.integer-panics). *)
let panicking seed = Pick.chance (Pick.make (Hashtbl.hash (seed, "panics"))) 0.1

let program_items ?pub ?(arrays = false) ?(reflect = false) ?macros
    ?(par = false) ?(cycles = false) ?(effects = false) ?(views = false)
    ?(unicode = false) ?(deep = false) ?(generics = false) ?(capped = false)
    seed =
  let p =
    {
      r = Pick.make seed;
      decls = [];
      fns = [];
      count = 0;
      fault;
      fault_variants;
      panics = panicking seed;
      capped;
    }
  in
  let types =
    Pick.times (Pick.between p.r 0 4) (fun () -> type_decl p ~pub:false)
  in
  let functions =
    Pick.times (Pick.between p.r 1 6) (fun () ->
        snd (function_ p ~budget:2_000 ~pub:false))
  in
  let seed_if wanted = if wanted then Some seed else None in
  let extra, main =
    main_with ?pub ?arrays:(seed_if arrays) ?reflect:(seed_if reflect)
      ?macros:(Option.map (fun m -> (m, seed)) macros)
      ?par:(seed_if par) ?cycles:(seed_if cycles) ?effects:(seed_if effects)
      ?views:(seed_if views) ?unicode:(seed_if unicode) ?deep:(seed_if deep)
      ?generics:(seed_if generics) p
  in
  (p, ((line fault_decl :: types) @ functions) @ (main :: extra))

(* The module of macros of the program made from [seed], if it uses
   macros. *)
let make_macros seed =
  if Csmith_macros.wanted seed then Some (Macro_module.make seed) else None

let meta_use (m : Macro_kinds.t) = line ("meta use " ^ m.module_name)
let items ?macros seed = snd (program_items ?macros seed)

(* The program made from [seed], and its module of macros if it has one and
   [macros]. *)
let text ?pub ?(macros = true) seed =
  let arrays = Csmith_arrays.wanted seed and par = Csmith_par.wanted seed in
  let reflect = Csmith_reflect.wanted seed in
  let cycles = Csmith_cycles.wanted seed in
  let effects = Csmith_effects.wanted seed in
  let views = Csmith_views.wanted seed and unicode = Csmith_text.wanted seed in
  let deep = Csmith_deep.wanted seed in
  let generics = Csmith_generics.wanted seed in
  let macros = if macros then make_macros seed else None in
  let p, items =
    program_items ?pub ~arrays ~reflect ?macros ~par ~cycles ~effects ~views
      ~unicode ~deep ~generics ~capped:true seed
  in
  let uses =
    (if arrays then [ line "use std.array" ] else [])
    @ (if reflect then [ line "use std.meta" ] else [])
    @ (if par then [ line "use std.par" ] else [])
    @ (if cycles || Csmith_effects.shares seed then [ line "use std.sync" ]
       else [])
    @ (if views then [ line "use std.view" ] else [])
    @ (if unicode then [ line "use std.text" ] else [])
    @ Option.fold ~none:[] ~some:(fun m -> [ meta_use m ]) macros
  in
  let items = items @ tests p seed in
  (String.concat "\n" (List.map render (uses @ caps items @ items)), macros)

let program ?macros seed = fst (text ?macros seed)

let module_file (m : Macro_kinds.t) =
  (m.module_name ^ ".lt", Macro_module.text m)

let files seed =
  let name = Printf.sprintf "seed_%d" seed in
  match text seed with
  | program, None -> [ (name ^ ".lt", program) ]
  | program, Some m ->
      [
        (Filename.concat name "main.lt", program);
        (let file, text = module_file m in
         (Filename.concat name file, text));
      ]

let module_files seed =
  let program, macros = text ~pub:true seed in
  (Printf.sprintf "seed_%d.lt" seed, program)
  :: Option.fold ~none:[] ~some:(fun m -> [ module_file m ]) macros

let bundle seeds =
  let name = Printf.sprintf "seed_%d" in
  let uses = List.map (fun s -> "use " ^ name s) seeds in
  let calls =
    List.concat_map
      (fun s ->
        [
          Printf.sprintf "  print(\"== %s\")" (name s);
          Printf.sprintf "  %s.main()" (name s);
        ])
      seeds
  in
  String.concat "\n" (uses @ [ ""; "fn main() / io {" ] @ calls @ [ "}"; "" ])
