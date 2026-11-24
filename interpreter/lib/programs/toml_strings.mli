(** The strings of TOML 1.0: basic and literal, on one line or on several
    (packages.manifest). *)

val string : Toml_scan.cursor -> string
(** A string of any kind, at its opening quote, as its value. *)
