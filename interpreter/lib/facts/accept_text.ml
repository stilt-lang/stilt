(* The text of what E0204 says a rule of acceptance needs (facts.closest-rule):
   each expression written back from the typed program, as the compiler
   writes it, a block and any other form that holds one as [{ … }]. *)

open Tast

let level : Ast.binary -> int = function
  | Or -> 1
  | And -> 2
  | Eq | Ne | Lt | Le | Gt | Ge -> 3
  | Bit_or -> 4
  | Bit_xor -> 5
  | Bit_and -> 6
  | Shl | Shr -> 7
  | Add | Sub | Add_wrap | Sub_wrap -> 8
  | Mul | Div | Rem | Mul_wrap -> 9

let quoted s =
  let b = Buffer.create (String.length s + 2) in
  Buffer.add_char b '"';
  String.iter
    (function
      | '"' -> Buffer.add_string b "\\\""
      | '\\' -> Buffer.add_string b "\\\\"
      | '\n' -> Buffer.add_string b "\\n"
      | c -> Buffer.add_char b c)
    s;
  Buffer.add_char b '"';
  Buffer.contents b

let is_method env (owner : Hir.item) name =
  List.exists
    (fun (m : Env.member) ->
      m.name = name && match m.kind with Method _ -> true | _ -> false)
    (Env.inherent_members env owner)

(* An expression's text, and the level of its outermost operator: 10 for a
   unary one, 11 for a postfix one or an atom. *)
let rec text env (e : expr) =
  match e.desc with
  | Int s | Float s -> (s, 11)
  | Str s -> (quoted s, 11)
  | Bool b -> (string_of_bool b, 11)
  | Local v | Value_param v -> (v.name, 11)
  | Constant i -> (i.name, 11)
  | Member_constant (i, name, _) -> (i.name ^ "." ^ name, 11)
  | Field (x, f) -> (at env 11 x ^ "." ^ f, 11)
  | Tuple_field (x, i) -> (at env 11 x ^ "." ^ string_of_int i, 11)
  | Index (x, k) -> (at env 11 x ^ "[" ^ fst (text env k) ^ "]", 11)
  | Unary (Neg, x) -> ("-" ^ at env 10 x, 10)
  | Unary (Not, x) -> ("!" ^ at env 10 x, 10)
  | Binary (op, a, b) ->
      let l = level op in
      (at env l a ^ " " ^ Sexp_atoms.binary op ^ " " ^ at env (l + 1) b, l)
  | Call (Member (owner, name), _, recv :: args, _)
    when is_method env owner name ->
      (at env 11 recv.value ^ "." ^ name ^ arguments env args, 11)
  | Call (Trait_method (_, name, _), _, recv :: args, _) ->
      (at env 11 recv.value ^ "." ^ name ^ arguments env args, 11)
  | Call (Member (owner, name), _, args, _) ->
      (owner.name ^ "." ^ name ^ arguments env args, 11)
  | Call (Function i, _, args, _) -> (i.name ^ arguments env args, 11)
  | Call (Operation (eff, name), _, args, _) ->
      (eff.name ^ "." ^ name ^ arguments env args, 11)
  | Call_value (f, args) -> (at env 11 f ^ arguments env args, 11)
  | Comptime x | Generalize (_, x) | Instantiate (x, _) -> text env x
  | Tuple es ->
      ( "(" ^ String.concat ", " (List.map (fun e -> fst (text env e)) es) ^ ")",
        11 )
  | List es ->
      ( "[" ^ String.concat ", " (List.map (fun e -> fst (text env e)) es) ^ "]",
        11 )
  | _ -> ("{ … }", 11)

and at env needed e =
  let s, l = text env e in
  if l < needed then "(" ^ s ^ ")" else s

and arguments env args =
  "("
  ^ String.concat ", "
      (List.map
         (fun (a : arg) ->
           (if a.mode = Inout then "inout " else "") ^ fst (text env a.value))
         args)
  ^ ")"

let expr env e = fst (text env e)
let len env list = at env 11 list ^ ".len()"
let range_closures = "a range loop needs the index outside closures"

let range_form (i : Hir.var) =
  Printf.sprintf "a range loop needs the index to be `%s`, `%s + k` or `%s - k`"
    i.name i.name i.name

let range_start = "a range loop needs it to start at a value known non-negative"

let range_start_at env k =
  Printf.sprintf "a range loop needs it to start at `%s` or above" (expr env k)

let range_end env list k e ~inclusive =
  let wanted =
    match k with
    | Some k -> len env list ^ " - " ^ expr env k
    | None -> len env list
  in
  Printf.sprintf "a range loop needs it to end at `%s`, not at `%s%s`" wanted
    (if inclusive then "..=" else "")
    (expr env e)

let range_length env list line =
  Printf.sprintf
    "a range loop needs a body that keeps the length of `%s`, which line %d \
     changes"
    (expr env list) line

let guard_form = "a guard needs the index to be a name or a literal"

let guard_lower env i =
  Printf.sprintf "a guard needs a test that gives `%s >= 0`" (expr env i)

let guard_upper env i list =
  Printf.sprintf "a guard needs a test that gives `%s < %s`" (expr env i)
    (len env list)

let between = "nothing between the test and the"

let guard_writes env i line =
  Printf.sprintf "a guard needs %s index to write `%s`, which line %d does"
    between (expr env i) line

let guard_length env list line =
  Printf.sprintf
    "a guard needs %s index to change the length of `%s`, which line %d does"
    between (expr env list) line

let divisor_form = "a divisor needs to be a name or a literal other than 0"

let divisor_test env d =
  Printf.sprintf "a divisor needs a test that gives `%s != 0`" (expr env d)

let divisor_writes env d line =
  Printf.sprintf "a divisor needs %s division to write `%s`, which line %d does"
    between (expr env d) line

let key_form = "a key needs to be a name or a literal that doesn't interpolate"
let key_type = "a key needs a type whose `Eq` and `Hash` are structural"

let key_test env m k =
  let k = expr env k in
  Printf.sprintf
    "a key needs a test that gives `%s.contains(%s)`, or a store of `%s` \
     before it"
    (at env 11 m) k k

let key_writes env k line =
  Printf.sprintf "a key needs nothing between to write `%s`, which line %d does"
    (expr env k) line

let key_changes env m line =
  Printf.sprintf
    "a key needs nothing between to change `%s` but by storing into it, which \
     line %d does"
    (expr env m) line

let loop_comparison =
  "a counting loop needs a comparison by `<`, `<=`, `>` or `>=`"

let loop_var = "a counting loop needs a `var` on one side"

let loop_bound = function
  | None -> "a counting loop needs a bound that the loop doesn't change"
  | Some line ->
      Printf.sprintf
        "a counting loop needs a bound that the loop doesn't change, which \
         line %d does"
        line

let op grows = if grows then "+=" else "-="

let loop_step (v : Hir.var) grows =
  Printf.sprintf
    "a counting loop needs a statement `%s %s s` of the loop's own block, with \
     `s` known positive"
    v.name (op grows)

let loop_continue env (v : Hir.var) grows s line =
  Printf.sprintf
    "a counting loop needs no `continue` before `%s %s %s`, which line %d is"
    v.name (op grows) (expr env s) line

let loop_writes (v : Hir.var) line =
  Printf.sprintf
    "a counting loop needs `%s` written nowhere else, which line %d does" v.name
    line

let shrink_form =
  "shrinking recursion needs every self-call to pass `p - s` or `p + s` at one \
   parameter"

let shrink_test (p : Hir.var) falls line =
  Printf.sprintf
    "shrinking recursion needs a test that gives `%s %s b` at the self-call on \
     line %d"
    p.name
    (if falls then ">" else "<")
    line
