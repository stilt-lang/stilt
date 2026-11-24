open Model_json
open Model_types

let op o operands = tag "op" [ o; Arr operands ]
let str_lit s = op (tag "str" [ Str s ]) []

let literal_value kind text =
  let digits = String.concat "" (String.split_on_char '_' text) in
  if String.starts_with ~prefix:"-" digits then
    (* A negative literal pattern (numbers.negative-literals), of a signed type: the
       negation of its digits, which wraps to [i64]'s least value as its digits do. *)
    let v = Ints.of_literal (String.sub digits 1 (String.length digits - 1)) in
    Int64.to_string (Int64.neg v)
  else
    let v = Ints.of_literal digits in
    if kind.[0] = 'u' then Printf.sprintf "%Lu" v else Int64.to_string v

let int_lit t text ~negated =
  match int_kind t with
  | None -> outside "a literal of a type the model lacks"
  | Some kind ->
      let v = literal_value kind text in
      let v =
        if not negated then v
        else if String.starts_with ~prefix:"-" v then v
        else "-" ^ v
      in
      tag "int" [ Str v ]

let unary (u : Ast.unary) t x =
  match (u, int_kind t, float_kind t, norm t) with
  | Neg, Some k, _, _ -> op (tag "neg" [ Str k ]) [ x ]
  | Not, Some k, _, _ -> op (tag "complement" [ Str k ]) [ x ]
  | Neg, None, Some f, _ -> op (tag "fneg" [ Str f ]) [ x ]
  | Not, None, None, Con ({ home = "std.prelude"; name = "bool" }, []) ->
      op (Str "not") [ x ]
  | _ -> outside "a unary operator on a type the model lacks"

let cmp : Ast.binary -> string option = function
  | Eq -> Some "eq"
  | Ne -> Some "ne"
  | Lt -> Some "lt"
  | Le -> Some "le"
  | Gt -> Some "gt"
  | Ge -> Some "ge"
  | _ -> None

let int_op (b : Ast.binary) k amount =
  let arith name = tag "arith" [ Str name; Str k ] in
  let wrap name = tag "wrapping" [ Str name; Str k ] in
  let bit name = tag "bitwise" [ Str name; Str k ] in
  let shift name =
    match amount with
    | Some a -> tag "shift" [ Str name; Str k; Str a ]
    | None -> outside "a shift by an amount the model lacks"
  in
  match b with
  | Add -> arith "add"
  | Sub -> arith "sub"
  | Mul -> arith "mul"
  | Div -> arith "div"
  | Rem -> arith "rem"
  | Add_wrap -> wrap "add"
  | Sub_wrap -> wrap "sub"
  | Mul_wrap -> wrap "mul"
  | Bit_and -> bit "and"
  | Bit_or -> bit "or"
  | Bit_xor -> bit "xor"
  | Shl -> shift "left"
  | Shr -> shift "right"
  | b -> (
      match cmp b with
      | Some c -> tag "compare" [ Str c; Str k ]
      | None -> outside "an operator the model lacks")

(* numbers.ieee-754: [+], [-], [*] and [/], and the comparisons. [%] on floats
   is [fmod], which the calculus lacks. *)
let float_op (b : Ast.binary) f =
  let arith name = tag "farith" [ Str name; Str f ] in
  match b with
  | Add -> arith "add"
  | Sub -> arith "sub"
  | Mul -> arith "mul"
  | Div -> arith "div"
  | b -> (
      match cmp b with
      | Some c -> tag "fcompare" [ Str c; Str f ]
      | None -> outside "the operator on floats")

let binary (b : Ast.binary) ta tb x y =
  match b with
  | And -> tag "if" [ x; Str "bool"; y; tag "bool" [ Bool false ] ]
  | Or -> tag "if" [ x; Str "bool"; tag "bool" [ Bool true ]; y ]
  | _ -> (
      match (int_kind ta, norm ta, cmp b) with
      | Some k, _, _ -> op (int_op b k (int_kind tb)) [ x; y ]
      | None, Con ({ home = "std.prelude"; name = ("f32" | "f64") as f }, []), _
        ->
          op (float_op b f) [ x; y ]
      | None, Con ({ home = "std.prelude"; name = "bool" }, []), Some c ->
          op (tag "bcompare" [ Str c ]) [ x; y ]
      | None, Con ({ home = "std.prelude"; name = "str" }, []), Some c ->
          op (tag "scompare" [ Str c ]) [ x; y ]
      | ( None,
          Con ({ home = "std.prelude"; name = "Set" }, [ _ ]),
          Some ("eq" | "ne") ) ->
          (* traits.structural-impls: a set is equal to another when its map of
             elements is, which holds the same keys in any order (std.sets). *)
          let equal =
            op (tag "set" [ tag "relate" [ Str "equal" ] ]) [ x; y ]
          in
          if b = Eq then equal else op (Str "not") [ equal ]
      | _ -> outside "an operator on a type the model lacks")

(* [binary], and [==] and [!=] on maps, which hold when the maps hold the same entries in
   any order, their keys and values compared part by part (traits.structural-impls). *)
let binary_at cx (b : Ast.binary) tx ty x y =
  match (b, norm tx) with
  | (Eq | Ne), Con ({ home = "std.prelude"; name = "Map" }, [ k; v ])
    when key cx k && key cx v ->
      let equal = op (tag "map" [ Str "equal" ]) [ x; y ] in
      if b = Eq then equal else op (Str "not") [ equal ]
  | _ -> binary b tx ty x y

let str_native name args =
  match name with
  | "len" -> op (Str "len") args
  | "is_empty" -> op (Str "isEmpty") args
  | "slice" -> op (Str "slice") args
  | "contains" -> op (tag "search" [ Str "contains" ]) args
  | "starts_with" -> op (tag "search" [ Str "startsWith" ]) args
  | "ends_with" -> op (tag "search" [ Str "endsWith" ]) args
  | "join" -> op (tag "list" [ Str "join" ]) args
  | "chars" | "split" | "lines" -> op (tag "list" [ Str name ]) args
  | "split_whitespace" -> op (tag "list" [ Str "splitWhitespace" ]) args
  | "bytes" -> op (tag "list" [ Str "bytes" ]) args
  | "from_utf8_lossy" -> op (tag "list" [ Str "fromUtf8Lossy" ]) args
  | "is_ascii" | "is_ascii_digit" | "is_ascii_alpha" | "is_ascii_alphanumeric"
  | "is_ascii_whitespace" | "is_ascii_upper" | "is_ascii_lower" ->
      op (tag "strClass" [ Str name ]) args
  | "pad_start" -> op (tag "padStr" [ Bool true ]) args
  | "pad_end" -> op (tag "padStr" [ Bool false ]) args
  | "code_points" -> op (tag "list" [ Str "codePoints" ]) args
  | "trim" | "trim_start" | "trim_end" | "ascii_upper" | "ascii_lower"
  | "reversed" ->
      op (tag "strMap" [ Str name ]) args
  | "replace" -> op (tag "replace" [ Bool false ]) args
  | "replace_first" -> op (tag "replace" [ Bool true ]) args
  | "char_count" -> op (Str "charCount") args
  | "count" -> op (Str "count") args
  | _ -> outside "the function str.%s" name

let int_native source name result args =
  let to_int prefix =
    match int_kind result with
    | Some target when name = prefix ^ target -> Some target
    | _ -> None
  in
  let methods =
    [
      "abs";
      "min";
      "max";
      "saturating_add";
      "saturating_sub";
      "pow";
      "div_euclid";
      "rem_euclid";
      "gcd";
      "lcm";
      "count_ones";
      "leading_zeros";
      "trailing_zeros";
    ]
  in
  if List.mem name methods then
    op (tag "intMethod" [ Str name; Str source ]) args
  else
    match (to_int "to_", to_int "wrap_to_", float_kind result) with
    | Some target, _, _ -> op (tag "convert" [ Str source; Str target ]) args
    | _, Some target, _ -> op (tag "wrapTo" [ Str source; Str target ]) args
    | None, None, Some f when name = "to_" ^ f ->
        op (tag "toFloat" [ Str source; Str f ]) args
    | _ -> outside "the function %s.%s" source name

(* The native methods of the float types, which IEEE 754 defines exactly (std.floats). *)
let float_methods =
  [ "sqrt"; "floor"; "ceil"; "trunc"; "abs"; "round"; "min"; "max"; "is_nan" ]

let native (owner : Hir.item) name result args =
  match owner with
  | { home = "std.prelude"; name = "str" } -> str_native name args
  | { home = "std.prelude"; name = k } when List.mem k Types.integer_types ->
      int_native k name result args
  | { home = "std.prelude"; name = ("f32" | "f64") as k } -> (
      match float_kind result with
      | Some f when name = "to_" ^ f -> op (tag "floatTo" [ Str k; Str f ]) args
      | _ when List.mem name float_methods ->
          op (tag "fmethod" [ Str name; Str k ]) args
      | _ -> outside "the function %s.%s" k name)
  | _ -> outside "the function %s.%s" (item_name owner) name

(* Whether an integer literal written in decimal stands at a float type, which it takes
   as a float literal of its digits does (numbers.integer-literals): [let x: f64 = 1]. *)
let decimal_at_float t text =
  float_kind t <> None
  && String.for_all (function '0' .. '9' | '_' -> true | _ -> false) text

(* A float literal, [m × 10^e] with its digits and exponent written in
   decimal, of the float type its context expects (numbers.float-literals). *)
let float_lit t text =
  let text = String.concat "" (String.split_on_char '_' text) in
  let digits, exponent =
    match String.index_from_opt (String.lowercase_ascii text) 0 'e' with
    | Some i ->
        ( String.sub text 0 i,
          int_of_string (String.sub text (i + 1) (String.length text - i - 1))
        )
    | None -> (text, 0)
  in
  let whole, fraction =
    match String.index_opt digits '.' with
    | Some i ->
        ( String.sub digits 0 i,
          String.sub digits (i + 1) (String.length digits - i - 1) )
    | None -> (digits, "")
  in
  let kind =
    match norm t with
    | Con ({ home = "std.prelude"; name = ("f32" | "f64") as k }, []) -> k
    | _ -> outside "a float literal of a type the model lacks"
  in
  op
    (tag "float"
       [
         Str kind;
         Str (whole ^ fraction);
         Str (string_of_int (exponent - String.length fraction));
       ])
    []

(* A splice with a format spec: its value's text by the spec's precision or kind,
   or as [Show] shows it, padded by its fill, alignment and width, which align a
   number right by default (std.width-fill-and-alignment, std.precision,
   std.integer-kinds and std.scientific-notation). *)
let formatted ~shown t spec x =
  let module S = Format_spec in
  let spec =
    match S.parse spec with
    | Some s -> s
    | None -> outside "a malformed format spec"
  in
  let number = int_kind t <> None || float_kind t <> None in
  let body =
    match (int_kind t, float_kind t, spec.kind, spec.precision) with
    | Some k, _, Some (('x' | 'X' | 'o' | 'b') as c), _ ->
        let base = match c with 'o' -> 8 | 'b' -> 2 | _ -> 16 in
        op
          (tag "inBase" [ Str k; Str (string_of_int base); Bool (c = 'X') ])
          [ x ]
    | _, Some f, Some 'e', p ->
        let p = Option.value p ~default:(-1) in
        op (tag "scientific" [ Str f; Str (string_of_int p) ]) [ x ]
    | _, Some f, None, Some p ->
        op (tag "fixed" [ Str f; Str (string_of_int p) ]) [ x ]
    | _ -> shown ()
  in
  if spec.width = 0 then body
  else
    let align =
      match spec.align with
      | Some a -> String.make 1 a
      | None -> if number then ">" else "<"
    in
    op
      (tag "pad" [ Str spec.fill; Str align; Str (string_of_int spec.width) ])
      [ body ]

let show ~structural t x =
  match (int_kind t, norm t) with
  | Some k, _ -> op (tag "showInt" [ Str k ]) [ x ]
  | None, Con ({ home = "std.prelude"; name = "bool" }, []) ->
      op (Str "showBool") [ x ]
  | None, Con ({ home = "std.prelude"; name = "str" }, []) -> x
  | _ when structural -> op (Str "showValue") [ x ]
  | _ -> outside "an interpolation of a type the model can't show"
