(** A counterexample's values, written by their structure as std.show-output
    shows a value nested inside another, whatever [Show] impls the program
    writes (tests.property-verdict); and the identity of values, by their
    structure with floats by their bits, which comparing candidates uses
    (std.precision). *)

val show : Prop_types.graph -> int -> Value.value -> string
(** The value of a node's type, as it shows nested. *)

val identity : Value.value -> string
(** A text that two values of one type share exactly when they are identical:
    they have one structure, with floats compared by their bits. *)
