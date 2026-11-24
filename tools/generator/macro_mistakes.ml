(* Mistakes in the procedural macros (macros.failed-uses and macros.errors-in-expansions) of a csmith program, each
   annotated with the one diagnostic the Reference requires for it, on the line
   where it starts, as Mutants plants its own: in a use, planted at the top of
   a function of the program, or in the module of macros, which then expands
   no use and reports nothing where its macros are used (macros.expansion-order). *)

open Code
open Macro_kinds

type place =
  | Use of string list
      (** Lines at the top of a function of the program, which name nothing but
          what they declare and the module's macros. *)
  | Module of (decl -> line list option)
      (** The lines of each declaration of the module that changes. *)

let first m wanted = List.find (fun d -> wanted d.kind) m.decls
let mix m = first m (function Mix _ -> true | _ -> false)
let zeros n = List.init n (fun _ -> "0")

let use m d parts =
  Printf.sprintf "%s.%s!(%s)" m.module_name d.called (String.concat ", " parts)

let annotate code lines =
  List.mapi
    (fun i text ->
      if i = List.length lines - 1 then text ^ " //~ ERROR " ^ code else text)
    lines

(* [lines], annotated, at the top of the body of the [i]th macro of [m]. *)
let in_macro m i code lines =
  let target = List.nth m.decls (i mod List.length m.decls) in
  Module
    (fun d ->
      if d == target then
        Some
          (Macro_module.render
             ~planted:(List.map (fun t -> (0, t)) (annotate code lines))
             d)
      else None)

(* Each mistake: the code of the diagnostic, and where it goes in [m], which
   [i] varies. *)
let mistakes =
  [
    (* macros.parts: a part too many, at it. *)
    ( "E0227",
      fun m _ ->
        let d = mix m in
        Use [ "let planted = " ^ use m d (zeros (List.length d.params + 1)) ] );
    (* macros.parts: a part too few, at the group's closing bracket. *)
    ("E0227", fun m _ -> Use [ "let planted = " ^ use m (mix m) [] ]);
    (* macros.procedural-uses: an expression macro where a pattern stands. *)
    ( "E0223",
      fun m _ ->
        let d = mix m in
        Use
          [
            Printf.sprintf "let planted = match 0 { %s => 1, _ => 2 }"
              (use m d (zeros (List.length d.params)));
          ] );
    (* macros.procedural-uses: a type macro where an expression stands. *)
    ( "E0223",
      fun m _ ->
        let d = first m (function Shape _ -> true | _ -> false) in
        Use [ "let planted = " ^ use m d (List.map (fun _ -> "i64") d.params) ]
    );
    (* macros.cursor and macros.raised-errors: the cursor raises at a token that ends no
       expression. *)
    ( "E0225",
      fun m _ ->
        Use
          [ "let planted = " ^ use m (first m (fun k -> k = Listed)) [ "1 2" ] ]
    );
    (* macros.procedural-declarations: a parameter whose type isn't an input type. The quote splices
       it as a literal, which an expression may be (macros.literal-splices). *)
    ( "E0228",
      fun m i ->
        let d = mix m in
        let t = List.nth [ "i64"; "str"; "bool" ] (i mod 3) in
        Module
          (fun d' ->
            if d' == d then
              match Macro_module.render ~retyped:(0, t) d with
              | doc :: (depth, signature) :: rest ->
                  Some (doc :: (depth, signature ^ " //~ ERROR E0228") :: rest)
              | lines -> Some lines
            else None) );
    (* macros.quote-hygiene: a quote naming a local of the macro's code without [$]. *)
    ( "E0211",
      fun m i ->
        in_macro m i "E0211"
          [ "let planted = 1"; "let quoted = quote { planted + 1 }" ] );
    (* macros.meta-use: a macro used in its own module. *)
    ( "E0212",
      fun m i ->
        let d = mix m in
        in_macro m i "E0212"
          [
            Printf.sprintf "let planted = %s!(%s)" d.called
              (String.concat ", " (zeros (List.length d.params)));
          ] );
  ]

let plant m kind =
  let code, place = List.nth mistakes (kind mod List.length mistakes) in
  match place m (kind / List.length mistakes) with
  | Use lines -> Use (annotate code lines)
  | Module _ as edit -> edit
