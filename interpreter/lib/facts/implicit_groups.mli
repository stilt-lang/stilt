(** Recursive groups of functions (facts.div). *)

val groups : ('k * 'k list) list -> 'k -> 'k list
(** [groups graph] maps each node of [graph], given with the nodes it names, to
    its recursive group: the strongly connected component that holds it, when
    that component has more than one node or its one node names itself, and
    nothing otherwise. Nodes are compared structurally. *)
