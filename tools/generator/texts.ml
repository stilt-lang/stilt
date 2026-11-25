(* The forms that make a [str]: interpolations, with their format specs, and
   the methods of strings. *)

open Code
open Context
open Ty

(* A format spec for a value of type [ty] that std.invalid-specs allows, or none. *)
let spec r ty =
  let padding () =
    if Pick.chance r 0.5 then
      Pick.one r [ ""; "<"; ">"; "^"; "*<"; "*>"; "-^"; "0>"; ".<"; "_>" ]
      ^ string_of_int (Pick.between r 0 12)
    else ""
  in
  Pick.run r
    [
      (3, fun () -> "");
      (2, padding);
      ( (match ty with Int _ -> 2 | _ -> 0),
        fun () -> padding () ^ Pick.one r [ "x"; "X"; "o"; "b" ] );
      ( (match ty with Float _ -> 3 | _ -> 0),
        fun () ->
          let precision =
            if Pick.chance r 0.7 then "." ^ string_of_int (Pick.below r 7)
            else ""
          in
          padding () ^ precision ^ if Pick.chance r 0.3 then "e" else "" );
    ]

(* An interpolated string, whose splices have types fixed in their body
   (std.invalid-specs). *)
let interpolation expr b sc ~depth =
  let r = b.p.r in
  let splice () =
    let t =
      match List.filter (fun v -> not (has_map b.p.decls v.ty)) sc.vars with
      | vars when vars <> [] && Pick.chance r 0.5 -> (Pick.one r vars).ty
      | _ -> random_ty b.p ~maps:false 2
    in
    let e = expr b sc ~depth ~known:true t in
    let spec = spec r t in
    "{" ^ operand e ^ (if spec = "" then "" else ":" ^ spec) ^ "}"
  in
  let parts =
    Pick.times (Pick.between r 1 3) (fun () -> Lit.string_body r ^ splice ())
  in
  atom ("\"" ^ String.concat "" parts ^ Lit.string_body r ^ "\"")

let str_ops expr b sc ~depth =
  let r = b.p.r in
  let d = depth - 1 in
  let me ?(known = false) () = expr b sc ~depth:d ~known Str in
  let strs = typed sc.vars Str in
  [
    (4, fun () -> cap_str b.p (interpolation expr b sc ~depth:d));
    ( 2,
      fun () ->
        method_on (me ~known:true ())
          (Pick.one r
             [
               "trim";
               "ascii_upper";
               "ascii_lower";
               "trim_start";
               "trim_end";
               "reversed";
             ])
          [] );
    ( 1,
      fun () ->
        (* The replacement is a literal, so that a string can't grow faster
           than linearly in a loop or a fold. *)
        let from = if Pick.chance r 0.1 then "\"\"" else Lit.string r in
        cap_str b.p
        @@ method_on (me ~known:true ())
             (Pick.one r [ "replace"; "replace_first" ])
             [ from; Lit.string r ] );
    ( 1,
      fun () ->
        cap_str b.p
        @@ method_on (me ~known:true ()) "join"
             [ (expr b sc ~depth:d ~known:false (List Str)).text ] );
    ( (if strs = [] then 0 else 1),
      fun () ->
        (* Every string is ASCII, so every offset is on a UTF-8 boundary. *)
        let v = (Pick.one r strs).name in
        atom
          (Printf.sprintf "%s.slice(0, %s.len().min(%d))" v v
             (Pick.between r 0 4)) );
  ]
