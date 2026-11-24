(* Value parameters and value arguments (generics.value-parameters, generics.value-arguments and generics.constant-arguments), and the
   constants that value arguments name, computed while the program is
   checked. *)

open Hir
open Resolve_context
open Resolve_paths

(* generics.value-parameters: the types whose values compare exactly. *)
let value_type_names =
  List.filter
    (fun n -> n = "bool" || n.[0] = 'i' || n.[0] = 'u')
    primitive_types

let value_type (t : ty) =
  match t.desc with
  | Ty_con ({ home; name }, [])
    when home = prelude && List.mem name value_type_names ->
      Some name
  | _ -> None

let array_item = { home = "std.array"; name = "Array" }

(* Declaring *)

(* generics.value-parameters: a value parameter [n: T], whose type [t] is an integer type
   or [bool] (E0345), and whose name no other generic of its list, nor of its
   impl, has (E0208). The module is in the meta tier (generics.meta-tier). *)
let declare ctx (n : name) (t : ty) =
  meta ctx;
  if t.desc <> Ty_error && Option.is_none (value_type t) then
    errorf ctx Code.e0345 t.loc
      "a value parameter's type is an integer type or `bool`, whose values \
       compare exactly, so that two types with equal arguments are one type";
  if is_primitive n.desc then
    errorf ctx Code.e0210 n.loc "`%s` is a primitive type name" n.desc;
  let v = fresh ctx n in
  if
    List.mem_assoc n.desc ctx.value_params || List.mem_assoc n.desc ctx.row_vars
  then (
    errorf ctx Code.e0208 n.loc "`%s` is already a generic here" n.desc;
    (ctx, v))
  else ({ ctx with value_params = (n.desc, (v, t)) :: ctx.value_params }, v)

(* Literals *)

(* numbers.negative-literals: the value of the integer literal [text], which may start
   with [-], as a value of the integer type [name], in decimal, if it is one. *)
let int_value name text =
  let negative = String.length text > 0 && text.[0] = '-' in
  let digits =
    if negative then String.sub text 1 (String.length text - 1) else text
  in
  match Ints.of_name name with
  | Some k when Literal.int_fits digits ~negative name ->
      let v = Ints.of_literal digits in
      Some (Ints.to_string k (if negative then Int64.neg v else v))
  | Some _ | None -> None

(* Computing constants (generics.constant-arguments; declarations.constant-expressions) *)

let rec path_of (e : Ast.expr) =
  match e.desc with
  | Name n -> Some [ { desc = n; loc = e.loc } ]
  | Field (base, member) -> Option.map (fun p -> p @ [ member ]) (path_of base)
  | _ -> None

(* The constant that a walked path names: one of a module, or of an inherent
   impl, as [Type.NAME]. *)
let named_constant ctx = function
  | Item_ref (item, { kind = Const_item; _ }), _, [] -> Some item
  | ( ( Item_ref (owner, { kind = Type_item; _ })
      | Self_ref { desc = Ty_con (owner, _); _ } ),
      _,
      [ (n : name) ] ) ->
      let item = { owner with name = owner.name ^ "." ^ n.desc } in
      if Hashtbl.mem ctx.env.st.constants item then Some item else None
  | _ -> None

(* The constant that [path] names where [ctx] is, found quietly. *)
let constant_of ctx path =
  fst
    (quietly ctx.env.st (fun () ->
         named_constant ctx
           (walk ctx ~want:Values ~noun:"a constant" ~locals:false path)))

type outcome = Known of string | Panic | No_value

(* The value of a constant expression of the type [name], read in [ctx]. A
   unary [-] that overflows panics, and an expression with an error of its
   own, which its constant reports, has no value. *)
let rec value_of ctx name (e : Ast.expr) =
  let literal text =
    match int_value name text with Some v -> Known v | None -> No_value
  in
  match e.desc with
  | Int text -> literal text
  | Bool b when name = "bool" -> Known (string_of_bool b)
  (* numbers.negative-literals: a [-] directly before a literal is part of it. *)
  | Unary (Neg, { desc = Int text; loc })
    when loc.line = e.loc.line && loc.col = e.loc.col + 1 ->
      literal ("-" ^ text)
  | Unary (Neg, operand) -> (
      match (value_of ctx name operand, Ints.of_name name) with
      | Known v, Some k when k.signed -> (
          match Ints.neg k (Int64.of_string v) with
          | n -> Known (Ints.to_string k n)
          | exception Fault.Panic _ -> Panic)
      | (Panic as o), _ -> o
      | _ -> No_value)
  | Name _ | Field _ -> (
      match
        Option.map (compute ctx.env) (Option.bind (path_of e) (constant_of ctx))
      with
      | Some (Value (t, v)) when t = name -> Known v
      | Some (Panics t) when t = name -> Panic
      | Some _ | None -> No_value)
  | _ -> No_value

(* generics.constant-arguments: a constant, computed once. One that a cycle reaches
   computes nothing: the cycle is its declaration's error (declarations.constant-cycles). *)
and compute env item =
  match Hashtbl.find_opt env.st.computed item with
  | Some c -> c
  | None ->
      Hashtbl.replace env.st.computed item (Unknown None);
      let c =
        match Hashtbl.find_opt env.st.constants item with
        | None -> Unknown None
        | Some (c, home) -> (
            match Smap.find_opt home env.scopes with
            | None -> Unknown None
            | Some scope -> compute_decl (module_ctx env scope) c)
      in
      Hashtbl.replace env.st.computed item c;
      c

(* A constant of an integer type or [bool] has a value of it, and one of
   another type has none, which a value argument can't take (E0311), unless
   its type has an error of its own. One whose part breaks after its [=] has
   no value, and a value argument that names it has the error type, whatever
   its type (errors.broken-parts). *)
and compute_decl ctx (c : Ast.const_decl) =
  match c.ty.desc with
  | _ when c.value = None -> Unknown None
  | Ty_named ([ n ], []) when List.mem n.desc value_type_names -> (
      match Option.map (value_of ctx n.desc) c.value with
      | Some (Known v) -> Value (n.desc, v)
      | Some Panic -> Panics n.desc
      | Some No_value | None -> Unknown (Some n.desc))
  | Ty_named ([ n ], []) when is_primitive n.desc -> Unknown (Some n.desc)
  | Ty_named (path, _) -> (
      match
        quietly ctx.env.st (fun () ->
            walk ctx ~want:Types ~noun:"a type" ~locals:false path)
      with
      | (Broken_ref, _, _), _ | _, true -> Unknown None
      | _ -> Unknown (Some (dotted_path path)))
  | Ty_int _ | Ty_bool _ | Ty_macro _ | Ty_splice _ -> Unknown None
  | Ty_tuple _ | Ty_record _ | Ty_spread _ | Ty_fn _ | Ty_handler _ ->
      Unknown (Some "a compound type")

(* Arguments *)

(* E0347: [what] is given for a value parameter. *)
let misplaced ctx (arg : Ast.ty) what =
  errorf ctx Code.e0347 arg.loc
    "%s, which can't be given for a value parameter: give a literal, a \
     constant or a value parameter"
    what;
  Ty_error

let wrong_type ctx (arg : Ast.ty) what found expected =
  errorf ctx Code.e0311 arg.loc
    "expected a value of `%s` for this value parameter, found %s of `%s`"
    expected what found;
  Ty_error

(* generics.array-sizes: an array's size is never negative. *)
let sized ctx ~size (arg : Ast.ty) v =
  if size && String.length v > 0 && v.[0] = '-' then (
    errorf ctx Code.e0347 arg.loc
      "an array's size is never negative, and this one is %s" v;
    Ty_error)
  else Ty_value v

let literal_arg ctx ~size expected (arg : Ast.ty) =
  match (arg.desc, expected) with
  | _, None -> Ty_error
  | Ty_bool b, Some "bool" -> Ty_value (string_of_bool b)
  | Ty_bool _, Some e -> wrong_type ctx arg "a literal" "bool" e
  | Ty_int _, Some "bool" -> wrong_type ctx arg "a literal" "{integer}" "bool"
  | Ty_int text, Some e -> (
      match int_value e text with
      | Some v -> sized ctx ~size arg v
      | None ->
          errorf ctx Code.e0320 arg.loc "the literal %s doesn't fit in `%s`"
            text e;
          Ty_error)
  | _ -> Ty_error

(* A [lower] name given for a value parameter: a value parameter in scope,
   whose type is the parameter's (E0311), and anything else that the name
   means there is E0347 (generics.value-arguments). *)
let lower_arg ctx expected (n : name) (arg : Ast.ty) =
  if is_primitive n.desc then misplaced ctx arg ("`" ^ n.desc ^ "` is a type")
  else
    match List.assoc_opt n.desc ctx.value_params with
    | Some (v, t) -> (
        match (value_type t, expected) with
        | Some found, Some e when found <> e ->
            wrong_type ctx arg ("the value parameter `" ^ n.desc ^ "`") found e
        | Some _, Some _ -> Ty_param v
        | _ -> Ty_error)
    | None -> (
        match lookup ctx Values ~locals:true n.desc with
        | Some Broken_ref -> Ty_error
        | Some m ->
            misplaced ctx arg
              (Printf.sprintf "`%s` is %s" n.desc (describe_meaning m))
        | None when List.mem_assoc n.desc ctx.row_vars ->
            misplaced ctx arg (Printf.sprintf "`%s` is a row variable" n.desc)
        | None ->
            unknown_name ctx ~name:n.desc n.loc "unknown name `%s`" n.desc;
            Ty_error)

(* A path given for a value parameter: a constant of its type (E0311),
   computed, whose computation doesn't panic (E0347). *)
let constant_arg ctx ~size expected path (arg : Ast.ty) =
  let report (n : name) what =
    ignore (misplaced ctx arg (Printf.sprintf "`%s` is %s" n.desc what))
  in
  match
    walk ctx ~want:Values ~noun:"a constant" ~misplaced:report ~locals:false
      path
  with
  | Broken_ref, _, _ -> Ty_error
  | walked -> (
      match (named_constant ctx walked, expected, walked) with
      | _, None, _ -> Ty_error
      | None, _, (m, last, []) ->
          misplaced ctx arg
            (Printf.sprintf "`%s` is %s" last.desc (describe_meaning m))
      | None, _, _ ->
          misplaced ctx arg
            (Printf.sprintf "`%s` is no constant" (dotted_path path))
      | Some item, Some e, _ -> (
          let shown = Printf.sprintf "the constant `%s`" item.name in
          match compute ctx.env item with
          | Value (t, v) when t = e -> sized ctx ~size arg v
          | Panics t when t = e ->
              errorf ctx Code.e0347 arg.loc
                "computing `%s` panics, so it gives this argument no value"
                item.name;
              Ty_error
          | (Value (t, _) | Panics t | Unknown (Some t)) when t <> e ->
              wrong_type ctx arg shown t e
          | Unknown _ | Value _ | Panics _ -> Ty_error))

(* Whether a name is a [lower] identifier's, whose first letter after its
   underscores is lowercase (lexical.case). *)
let is_lower name =
  match Seq.find (fun c -> c <> '_') (String.to_seq name) with
  | Some 'a' .. 'z' -> true
  | _ -> false

(* generics.value-arguments: the argument [arg] given for a value parameter whose type
   is named [expected], [None] when that type has an error. [size] tells
   whether it is an array's size (generics.array-sizes). *)
let value_arg ctx ~size expected (arg : Ast.ty) =
  match arg.desc with
  | Ty_int _ | Ty_bool _ -> literal_arg ctx ~size expected arg
  | Ty_named ([ n ], []) when is_lower n.desc -> lower_arg ctx expected n arg
  | Ty_named (path, []) -> constant_arg ctx ~size expected path arg
  | Ty_named (_, _ :: _)
  | Ty_tuple _ | Ty_record _ | Ty_spread _ | Ty_fn _ | Ty_handler _ | Ty_macro _
  | Ty_splice _ ->
      misplaced ctx arg "a type is given"

(* generics.value-arguments: a type parameter takes a type, so a value given for one,
   a literal, a constant or a value parameter, is E0347, and so is any other
   name that means no type there. *)
let not_a_type ctx (arg : Ast.ty) what =
  errorf ctx Code.e0347 arg.loc "%s, but a type parameter takes a type" what

let type_arg_misplaced ctx (arg : Ast.ty) =
  match arg.desc with
  | Ty_int text -> Some (Printf.sprintf "%s is a value" text)
  | Ty_bool b -> Some (Printf.sprintf "%b is a value" b)
  | Ty_named ([ n ], []) when List.mem_assoc n.desc ctx.value_params ->
      Some (Printf.sprintf "`%s` is a value parameter" n.desc)
  | _ -> None
