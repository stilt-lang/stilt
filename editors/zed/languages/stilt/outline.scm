; The outline of a file in Zed: its declarations, with an impl's, a trait's and an effect's
; members inside them, each named after its keywords, and its doc comments as their annotations.
; `just grammar` runs this over the suite's programs.

((comment) @annotation
  (#match? @annotation "^///"))

(item
  "pub"? @context
  "extern"? @context
  (fn
    (fn_head
      "fn" @context
      (lower) @name))) @item

(item
  "pub"? @context
  "extern" @context
  (fn_head
    "fn" @context
    (lower) @name)) @item

(item
  "pub"? @context
  (type_decl
    "type" @context
    (upper) @name)) @item

(item
  "pub"? @context
  (trait
    "trait" @context
    (upper) @name)) @item

(item
  "pub"? @context
  (const
    "const" @context
    (upper) @name)) @item

(item
  "pub"? @context
  (effect
    "effect" @context
    (upper) @name)) @item

(item
  "pub"? @context
  (macro
    "macro" @context
    (lower) @name)) @item

(item
  "pub"? @context
  (syntax
    "syntax" @context
    (lower) @name)) @item

(item
  (test
    "test" @context
    (string) @name)) @item

(item
  "impl" @context
  (bound)? @name
  "for"? @context
  (type) @name) @item

(inherent_member
  "pub"? @context
  (fn
    (fn_head
      "fn" @context
      (lower) @name))) @item

(inherent_member
  "pub"? @context
  (const
    "const" @context
    (upper) @name)) @item

(trait_impl_member
  (fn
    (fn_head
      "fn" @context
      (lower) @name))) @item

(trait_impl_member
  (const
    "const" @context
    (upper) @name)) @item

(trait_member
  (fn_head
    "fn" @context
    (lower) @name)) @item

(trait_member
  "const" @context
  (upper) @name) @item

(operation
  "fn" @context
  (lower) @name) @item
