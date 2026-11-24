(* vm: a stack machine interprets a loop that sums the squares of the integers below a bound,
   modulo a prime. *)

type op =
  | Push of int
  | Load of int
  | Store of int
  | Add
  | Mul
  | Rem
  | Lt
  | Jump_unless of int
  | Jump of int
  | Halt

let program bound =
  [|
    Push 0; Store 0; Push 0; Store 1;
    Load 0; Push bound; Lt; Jump_unless 22;
    Load 1; Load 0; Load 0; Mul; Add; Push 1000003; Rem; Store 1;
    Load 0; Push 1; Add; Store 0;
    Jump 4; Halt;
    Load 1; Halt;
  |]
[@@ocamlformat "disable"]

let run code =
  let stack = Stack.create () and locals = [| 0; 0 |] in
  let push n = Stack.push n stack in
  let pop () = Option.value (Stack.pop_opt stack) ~default:0 in
  let binary f =
    let b = pop () in
    let a = pop () in
    push (f a b)
  in
  let rec go pc =
    match code.(pc) with
    | Push n ->
        push n;
        go (pc + 1)
    | Load i ->
        push locals.(i);
        go (pc + 1)
    | Store i ->
        locals.(i) <- pop ();
        go (pc + 1)
    | Add ->
        binary ( + );
        go (pc + 1)
    | Mul ->
        binary ( * );
        go (pc + 1)
    | Rem ->
        binary ( mod );
        go (pc + 1)
    | Lt ->
        binary (fun a b -> if a < b then 1 else 0);
        go (pc + 1)
    | Jump_unless target -> if pop () = 0 then go target else go (pc + 1)
    | Jump target -> go target
    | Halt -> pop ()
  in
  go 0

let () = Printf.printf "%d\n" (run (program 1500000))
