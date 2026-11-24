(* Unsafe code and what C holds, while a body is checked (c.unsafe-operations, c.element-types and c.lending-buffer). *)

open Check_state
module T = Types

let ptr = { Hir.home = "std.c"; name = "Ptr" }
let str = { Hir.home = "std.c"; name = "Str" }

let rec c_holds t =
  match T.resolve t with
  | T.Con (item, [ inner ]) when item = ptr -> pointee inner
  (* errors.error-type: no diagnostic arises from the error type, at any depth. *)
  | T.Error -> true
  | t -> Option.is_some (T.numeric_name t) || t = T.bool

(* What a [c.Ptr] may point at: what C holds, and [()] for [void]. *)
and pointee t = c_holds t || T.resolve t = T.unit

(* c.unsafe-operations: the operations that only an [unsafe] block may hold. *)
let is_unsafe st (callee : Tast.callee) =
  match callee with
  | Function item -> Env.is_foreign st.env item
  | Member (owner, ("read" | "write" | "read_list")) -> owner = ptr
  | Member (owner, "to_str") -> owner = str
  | _ -> false

(* c.module-std-c, c.element-types and c.lending-buffer: the calls whose [T], their first type argument, C must hold:
   reading, writing and moving through an address, and lending a list. *)
let reads_c_memory (callee : Tast.callee) =
  match callee with
  | Member (owner, ("read" | "write" | "read_list" | "offset")) -> owner = ptr
  | Member
      ({ home = "std.prelude"; name = "List" }, ("with_ptr" | "with_mut_ptr"))
    ->
      true
  | _ -> false

let used st loc callee targs =
  if is_unsafe st callee && st.unsafe_depth = 0 then
    error st Code.e0436 loc
      "this is an unsafe operation, which only an `unsafe because \"…\" { … }` \
       block may hold";
  match targs with
  | t :: _ when reads_c_memory callee ->
      st.c_elements <- (t, loc) :: st.c_elements
  | _ -> ()

let within st loc check =
  st.unsafe_blocks <- loc :: st.unsafe_blocks;
  st.unsafe_depth <- st.unsafe_depth + 1;
  Fun.protect ~finally:(fun () -> st.unsafe_depth <- st.unsafe_depth - 1) check

let fit st =
  List.iter
    (fun (t, loc) ->
      match T.resolve t with
      | T.Error | T.Var _ -> ()
      | resolved when not (c_holds resolved) ->
          error st Code.e0353 loc
            "C doesn't hold a `%s` as Stilt does: use an integer, a float, \
             `bool` or a `c.Ptr`"
            (show t)
      | _ -> ())
    (List.rev st.c_elements)
