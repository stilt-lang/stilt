(* The bytes read from stdin and not yet taken, from [start] to [stop] of
   [bytes], of which those before [scanned] hold no newline, and whether the
   input has ended. Input that can't be read ends as the end of the input
   does. *)
type input = {
  mutable bytes : Bytes.t;
  mutable start : int;
  mutable stop : int;
  mutable scanned : int;
  mutable ended : bool;
}

let input =
  {
    bytes = Bytes.create 65536;
    start = 0;
    stop = 0;
    scanned = 0;
    ended = false;
  }

(* Reads from stdin once, which waits unless something is waiting, into the
   room after [stop], moving what is left to the front first and growing the
   buffer when it is full. *)
let fill () =
  let b = input in
  let left = b.stop - b.start in
  if left = Bytes.length b.bytes then begin
    let grown = Bytes.create (2 * Bytes.length b.bytes) in
    Bytes.blit b.bytes b.start grown 0 left;
    b.bytes <- grown
  end
  else Bytes.blit b.bytes b.start b.bytes 0 left;
  b.scanned <- b.scanned - b.start;
  b.start <- 0;
  b.stop <- left;
  let rec go () =
    match
      Unix.read Unix.stdin b.bytes b.stop (Bytes.length b.bytes - b.stop)
    with
    | 0 -> b.ended <- true
    | n -> b.stop <- b.stop + n
    | exception Unix.Unix_error (Unix.EINTR, _, _) -> go ()
    | exception Unix.Unix_error _ -> b.ended <- true
  in
  go ()

(* The position of the first newline waiting, if one is. *)
let newline () =
  let b = input in
  let rec go i =
    if i >= b.stop then begin
      b.scanned <- b.stop;
      None
    end
    else if Bytes.get b.bytes i = '\n' then Some i
    else go (i + 1)
  in
  go (max b.start b.scanned)

(* Takes the bytes up to [stop] out of the buffer, and skips [skip] more. *)
let take stop skip =
  let b = input in
  let text = Bytes.sub_string b.bytes b.start (stop - b.start) in
  b.start <- stop + skip;
  b.scanned <- b.start;
  text

let line text =
  let text =
    if String.ends_with ~suffix:"\r" text then
      String.sub text 0 (String.length text - 1)
    else text
  in
  Strings.repair text

(* The line that is waiting, if a whole one is or the input has ended. *)
let waiting_line () =
  match newline () with
  | Some i -> Some (Some (line (take i 1)))
  | None when input.ended ->
      if input.start = input.stop then Some None
      else Some (Some (line (take input.stop 0)))
  | None -> None

let rec read_line () =
  match waiting_line () with
  | Some line -> line
  | None ->
      fill ();
      read_line ()

(* Whether a read from stdin would return at once. A descriptor that can't be
   polled fails the read, which ends the input. *)
let rec readable () =
  match Unix.select [ Unix.stdin ] [] [] 0.0 with
  | [], _, _ -> false
  | _ -> true
  | exception Unix.Unix_error (Unix.EINTR, _, _) -> readable ()
  | exception Unix.Unix_error _ -> true

let rec poll_line () =
  match waiting_line () with
  | Some line -> line
  | None when readable () ->
      fill ();
      poll_line ()
  | None -> None

let read_all () =
  while not input.ended do
    fill ()
  done;
  Strings.repair (take input.stop 0)
