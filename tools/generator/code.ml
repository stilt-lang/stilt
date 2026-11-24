(* Source code: the text of expressions, and lines of code with their depth of
   nesting, as a program prints them. *)

(* An expression's text. [atom] tells whether it can be an operand or a
   receiver without parentheses. [known] tells whether its type is fixed
   without an expected type, as a receiver's must be (types.known-types). *)
type code = { text : string; atom : bool; known : bool }

let atom ?(known = true) text = { text; atom = true; known }
let compound ?(known = true) text = { text; atom = false; known }
let operand c = if c.atom then c.text else "(" ^ c.text ^ ")"

(* [text] as the head of an [if], [while] or [match], or the iterable of a
   [for], which end at their first [{] outside brackets (expressions.heads). *)
let head text = if String.contains text '{' then "(" ^ text ^ ")" else text
let call_text name args = name ^ "(" ^ String.concat ", " args ^ ")"
let method_on recv name args = atom (operand recv ^ "." ^ call_text name args)

(* A line of code, with its depth of nesting. *)
type line = int * string

let nest lines = List.map (fun (depth, text) -> (depth + 1, text)) lines
let line text = [ (0, text) ]

let block_lines opening lines closing =
  ((0, opening) :: nest lines) @ [ (0, closing) ]

let render lines =
  String.concat ""
    (List.map
       (fun (depth, text) -> String.make (2 * depth) ' ' ^ text ^ "\n")
       lines)
