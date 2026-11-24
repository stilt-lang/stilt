type t = {
  code : Code.t;
  file : string;
  line : int;
  col : int;
  message : string;
}

let at ~file code (loc : Ast.loc) message =
  { code; file; line = loc.line; col = loc.col; message }

let is_error diagnostic = (diagnostic.code :> string).[0] = 'E'

let to_json d =
  Printf.sprintf
    {|{"code": %s, "file": %s, "line": %d, "col": %d, "message": %s}|}
    (Json.string (d.code :> string))
    (Json.string d.file) d.line d.col (Json.string d.message)

let to_string d =
  Printf.sprintf "%s:%d:%d: %s: %s" d.file d.line d.col
    (d.code :> string)
    d.message
