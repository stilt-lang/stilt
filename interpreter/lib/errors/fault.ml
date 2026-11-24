exception Panic of string * string

let panic kind fmt =
  Printf.ksprintf (fun detail -> raise (Panic (kind, detail))) fmt
