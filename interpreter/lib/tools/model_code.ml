(* The code that the export writes of its own, for the structural impls and for maps whose
   keys have impls that the program writes: what each computes, and the expressions it is
   built of. *)

open Model_json
open Model_types
open Model_ops
open Model_forms

(* What a structural impl computes: [Eq.eq], [Ord.compare], [Hash.hash], or [Show.show],
   nested in another value or not (traits.show). *)
type kind = Eq | Compare | Hash | Show of bool

let bool_ty = prelude_ty "bool"
let i64 = prelude_ty "i64"
let str_ty = prelude_ty "str"
let ordering_ty = Types.Con (ordering_item, [])
let u64 = prelude_ty "u64"
let hash_trait = { Hir.home = "std.prelude"; name = "Hash" }

let result_of = function
  | Eq -> bool_ty
  | Compare -> ordering_ty
  | Hash -> u64
  | Show _ -> str_ty

let name_of = function
  | Eq -> "Eq.eq"
  | Compare -> "Ord.compare"
  | Hash -> "Hash.hash"
  | Show false -> "Show.show"
  | Show true -> "Show.show_nested"

let int n = int_lit i64 (string_of_int n) ~negated:false
let false_e = tag "bool" [ Bool false ]
let true_e = tag "bool" [ Bool true ]
let field_e v f = tag "field" [ v; Str f ]
let let_e cx n t init body = tag "letIn" [ Str n; ty cx t; init; body ]
let var_in cx n t init body = tag "varIn" [ Str n; ty cx t; init; body ]
let assign n v = tag "assign" [ Arr [ Str n; Arr [] ]; v ]
let when_e c x = tag "if" [ c; Str "unit"; x; unit_e ]
let not_e x = op (Str "not") [ x ]
let and_e x y = binary And bool_ty bool_ty x y
let list_len x = op (tag "list" [ Str "len" ]) [ x ]
let incr n = assign n (binary Add i64 i64 (var_e n) (int 1))
let concat parts = op (Str "concat") parts

let ordering cx c =
  tag "variant" [ Str (declared cx ordering_item []); Str c; Arr [] ]

let same_ordering cx o c =
  op (tag "structural" [ Str "eq"; Arr [] ]) [ o; ordering cx c ]

(* A call of a function the export declares, by its key. *)
let helper_call cx key args result =
  call_e cx
    (tag "fnRef" [ Str key; Arr []; Arr [] ])
    (List.map (fun x -> tag "value" [ x ]) args)
    result

(* Declares the function [key] of the export's own, once: [params] with their types, its
   result's type, and its body, written after the key is among the helpers, so that the
   body may call it. *)
let declare cx key params result body =
  if not (List.mem_assoc key cx.helpers) then begin
    cx.helpers <- (key, Null) :: cx.helpers;
    let param (n, t) = Arr [ Str "let"; Str n; ty cx t; Null ] in
    let decl =
      Arr
        [
          Str key;
          Arr [];
          Arr [];
          Arr (List.map param params);
          ty cx result;
          row cx Types.empty_row;
          body ();
        ]
    in
    cx.helpers <-
      List.map (fun (n, d) -> if n = key then (n, decl) else (n, d)) cx.helpers
  end

(* The texts that [show_part] gives each element of [iterable], of type [elem], joined by
   [, ] between [opening] and [closing]. *)
let joined cx elem iterable show_part (opening, closing) =
  let strs = Types.Con (list_item, [ str_ty ]) in
  let push =
    assign "parts"
      (op
         (tag "list" [ Str "push" ])
         [ var_e "parts"; show_part (var_e "element") ])
  in
  var_in cx "parts" strs
    (tag "list" [ Str "str"; Arr [] ])
    (tag "seq"
       [
         tag "for" [ Str "element"; ty cx elem; iterable; push ];
         concat
           [
             str_lit opening;
             op (tag "list" [ Str "join" ]) [ str_lit ", "; var_e "parts" ];
             str_lit closing;
           ];
       ])

(* Texts with [, ] between them. *)
let rec separated = function
  | [] -> []
  | [ x ] -> [ x ]
  | x :: rest -> x :: str_lit ", " :: separated rest

(* A hash [h] with another mixed in, [h * 31 + x], wrapping. *)
let mix h x =
  let wrap name = tag "wrapping" [ Str name; Str "u64" ] in
  op (wrap "add") [ op (wrap "mul") [ h; int_lit u64 "31" ~negated:false ]; x ]

(* [Less], [Greater] or [otherwise], as the integer [x] is below, above or equal to [y]. *)
let native_ordering cx x y otherwise =
  let o = ty cx ordering_ty in
  tag "if"
    [
      binary Lt i64 i64 x y;
      o;
      ordering cx "Less";
      tag "if" [ binary Gt i64 i64 x y; o; ordering cx "Greater"; otherwise ];
    ]

(* A variant's arm, [C(base/0, …) => body], its payload bound to fresh names. *)
let ctor_arm name (c, ts) base body =
  let names = List.mapi (fun i _ -> Printf.sprintf "%s/%d" base i) ts in
  let pattern =
    tag "variant"
      [ Str name; Str c; Arr (List.map (fun n -> tag "bind" [ Str n ]) names) ]
  in
  Arr
    [
      pattern;
      Arr (List.map (fun n -> Str n) names);
      body (List.map var_e names);
    ]

(* How the export writes a prelude trait's function at a type, on its operands. *)
type at = kind -> Types.ty -> Model_json.t list -> Model_json.t
