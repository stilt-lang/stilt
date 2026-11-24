(* The exported functions of c.exported-signatures and c.exported-names: what C can take of a signature (c.exported-signatures),
   the names C can already mean (c.exported-names), and one name per package (c.exported-names). *)

open Ast

(* The names of reference/c-names.txt, which the compiler reads too. *)
let reserved =
  lazy
    (let table = Hashtbl.create 2048 in
     String.split_on_char '\n' C_names.text
     |> List.iter (fun line ->
         let line = String.trim line in
         if line <> "" && line.[0] <> '#' then Hashtbl.replace table line ());
     table)

let prefixes = [ "_"; "stilt_"; "lt_"; "f_"; "m_" ]

let starts_with name prefix =
  String.length name >= String.length prefix
  && String.sub name 0 (String.length prefix) = prefix

(* Whether C or C++ code can already mean [name]. *)
let taken name =
  Hashtbl.mem (Lazy.force reserved) name
  || List.exists (starts_with name) prefixes

let simple = [ "i8"; "i16"; "i32"; "i64"; "u8"; "u16"; "u32"; "u64" ]
let simple = simple @ [ "f32"; "f64"; "bool" ]

(* Whether C takes a value of type [t] (c.exported-signatures), [()] only as a result. *)
let c_type ~result (t : ty) =
  match t.desc with
  | Ty_named ([ name ], []) -> List.mem name.desc simple
  | Ty_tuple [] -> result
  | _ -> false

let error ~file loc message = Diagnostic.at ~file Code.e0352 loc message
let generic_loc = function Type_param p -> p.name.loc | Row_param n -> n.loc

let row_loc = function
  | Row_io _ -> None
  | Row_raise (loc, _) | Row_async loc -> Some loc
  | Row_var n -> Some n.loc
  | Row_effect (path, _) ->
      Option.map (fun (n : name) -> n.loc) (List.nth_opt path 0)

let param_errors ~file = function
  | Self_param (_, loc, _) ->
      [ error ~file loc "an exported function takes no receiver" ]
  | Param (Inout, name, _, _) ->
      [ error ~file name.loc "C can't pass an `inout` parameter" ]
  | Param (_, name, _, true) ->
      [ error ~file name.loc "C can't pass an `escaping` parameter" ]
  | Param (Let, _, ty, false) ->
      if c_type ~result:false ty then []
      else
        [
          error ~file ty.loc
            "C can't pass this type; use an integer, a float or `bool`";
        ]

(* c.exported-signatures's errors of [f]'s signature, then c.exported-names's of its name, in order. *)
let signature ~file (f : fn_decl) =
  let named =
    if taken f.name.desc then
      [
        error ~file f.name.loc
          (Printf.sprintf "`%s` is a name C or C++ code can already mean"
             f.name.desc);
      ]
    else []
  in
  let generics =
    List.map
      (fun g ->
        error ~file (generic_loc g)
          "an exported function takes no type, value or row parameter")
      f.generics
  in
  let result =
    match f.ret with
    | Some t when f.projection || not (c_type ~result:true t) ->
        [
          error ~file t.loc
            "C can't take this result; use an integer, a float, `bool` or `()`";
        ]
    | _ -> []
  in
  let row =
    List.filter_map
      (fun e ->
        Option.map
          (fun l -> error ~file l "C can't take this effect")
          (row_loc e))
      f.row
  in
  named @ generics
  @ List.concat_map (param_errors ~file) f.params
  @ result @ row

let exported (tree : module_) =
  List.filter_map
    (fun (item : item) ->
      match item.desc with
      | Decl { exported = true; kind = Fn f; _ } -> Some f
      | _ -> None)
    tree.items

(* c.exported-names: each exported function after the first of its name in its package,
   but where its own module declares the name again, which E0208 reports. *)
let twice packages reads =
  let keyed =
    List.map
      (fun ((src : Program.source), tree) ->
        let path = String.concat "." (Program.local_path packages src) in
        ((src.package, path), src, exported tree))
      reads
    |> List.sort (fun (a, _, _) (b, _, _) -> compare a b)
  in
  let seen = Hashtbl.create 16 in
  List.concat_map
    (fun ((package, path), (src : Program.source), fns) ->
      List.filter_map
        (fun (f : fn_decl) ->
          let key = (package, f.name.desc) in
          let paths = Option.value (Hashtbl.find_opt seen key) ~default:[] in
          Hashtbl.replace seen key (path :: paths);
          if paths = [] || List.mem path paths then None
          else
            Some
              (Diagnostic.at ~file:src.file Code.e0219 f.name.loc
                 (Printf.sprintf
                    "another exported function of this package is named `%s`"
                    f.name.desc)))
        fns)
    keyed

let check packages reads =
  List.concat_map
    (fun ((src : Program.source), tree) ->
      List.concat_map (signature ~file:src.file) (exported tree))
    reads
  @ twice packages reads
