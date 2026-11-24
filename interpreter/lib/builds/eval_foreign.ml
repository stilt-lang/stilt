(* The natives of [std.c], the prelude's lending methods, and the calls of
   foreign functions (c.module-std-c, c.lending-methods and c.calls). A [c.Ptr] and a [c.Str]
   are held as [Int] of their addresses. A lent list or string is copied into
   a C buffer that lives until the closure returns, and [with_mut_ptr] copies
   the buffer back into the list then. *)

open Value
open Eval_state

let address = function Int a -> a | _ -> invalid_arg "Eval_foreign.address"

(* Calls the closure [f] with the address of [buffer], runs [after] on the
   buffer when it returns, and frees the buffer when it returns, raises or
   panics. *)
let lending ?(after = ignore) t fr loc f buffer =
  match f with
  | Fn f ->
      Fun.protect
        ~finally:(fun () -> Foreign.free buffer)
        (fun () ->
          let target = Eval_targets.target_of_fn t f in
          let v = t.apply t fr loc target [| Int buffer |] in
          after buffer;
          v)
  | _ -> invalid_arg "Eval_foreign.lending"

(* macros.step-limits: a macro's run, which performs nothing, stops where it would reach C
   through [name] (macros.step-limits). *)
let compile_time name =
  if Option.is_some !Eval_state.running then
    raise (Eval_state.Stopped (Printf.sprintf "it reached C through `%s`" name))

(* c.lending-methods: [with_ptr] and [with_mut_ptr] on a list of [T], the first type
   argument, and [with_c_str] on a [str]. *)
let lend t fr loc name targs args =
  compile_time name;
  match (name, args) with
  | "with_ptr", [| List xs; f |] ->
      lending t fr loc f (Foreign.lend (List.hd targs) (Vec.to_list xs))
  | "with_mut_ptr", [| List xs; f |] ->
      let ty = List.hd targs in
      let after buffer =
        args.(0) <-
          List (Vec.of_list (Foreign.read_list ty buffer (Vec.length xs)))
      in
      lending ~after t fr loc f (Foreign.lend ty (Vec.to_list xs))
  | "with_c_str", [| Str s; f |] ->
      Option.iter
        (Fault.panic "nul-in-string" "the string holds a NUL at byte %d")
        (String.index_opt s '\000');
      lending t fr loc f (Foreign.c_string s)
  | _ -> invalid_arg ("Eval_foreign.lend: " ^ name)

let lends = [ "with_ptr"; "with_mut_ptr"; "with_c_str" ]

(* c.module-std-c: the operations on a [c.Ptr<T>], whose [T] is the first type
   argument, and on a [c.Str]. *)
let pointer name targs args =
  let ty () = List.hd targs in
  let at = address args.(0) in
  let int i = address args.(i) in
  match name with
  | "is_null" -> Bool (at = 0L)
  | "offset" ->
      Int
        (Int64.add at (Int64.mul (int 1) (Int64.of_int (Foreign.size (ty ())))))
  | "address" -> Int at
  | "read" -> Foreign.read (ty ()) at
  | "write" ->
      Foreign.write (ty ()) at args.(1);
      unit
  | "read_list" ->
      List (Vec.of_list (Foreign.read_list (ty ()) at (Int64.to_int (int 1))))
  | "to_str" -> Str (Foreign.to_str at)
  | _ -> invalid_arg ("Eval_foreign.pointer: " ^ name)

(* c.calls: a foreign function, called with its declared types. *)
let call t (item : Hir.item) args =
  let s = Option.get (Env.function_sig t.env item) in
  Foreign.call item.name (List.map snd s.params) s.ret (Array.to_list args)

let native t (callee : Tast.callee) targs args =
  (match callee with
  | Function { name; _ } | Member (_, name) -> compile_time name
  | Trait_method _ | Operation _ -> ());
  match callee with
  | Function { home = "std.c"; name = "null" } -> Int 0L
  | Member ({ home = "std.c"; _ }, name) -> pointer name targs args
  | Function item -> call t item args
  | Member _ | Trait_method _ | Operation _ -> invalid_arg "Eval_foreign.native"
