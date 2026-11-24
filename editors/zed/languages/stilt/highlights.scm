; The highlighting of Stilt for Zed, with the capture names of Zed's themes. Generated
; from the grammar, itself generated from the Reference, by `just grammar-generate`; `just
; grammar` checks it is current and runs it over the suite's programs.

(comment) @comment
[(string) (string_head) (string_mid) (string_tail)] @string
(format) @string.special
[(int) (float)] @number
(limit) @attribute
["alloc" "assert" "async" "await" "because" "break" "catch" "clock" "comptime" "console" "const" "continue" "copy" "div" "effect" "else" "env" "escaping" "exec" "extern" "field" "fn" "for" "fs" "handler" "if" "impl" "in" "inout" "io" "let" "locks" "loop" "macro" "match" "meta" "module" "net" "overflow" "panic" "pattern" "pub" "quote" "raise" "rand" "resume" "return" "spawn" "syntax" "test" "trait" "try" "type" "unsafe" "use" "var" "when" "where" "while" "with" "without" "yield"] @keyword
["true" "false"] @boolean
["self" "Self"] @variable.special
["!" "!=" "%" "%=" "&" "&&" "&=" "*" "*%" "*%=" "*=" "+" "+%" "+%=" "+=" "-" "-%" "-%=" "-=" "->" ".." "..=" "/" "/=" "<" "<<" "<<=" "<=" "=" "==" "=>" ">" ">=" ">>" ">>=" "?" "^" "^=" "|" "|=" "||"] @operator
["(" ")" "[" "]" "{" "}"] @punctuation.bracket
["," ";" "." ":"] @punctuation.delimiter
(fn_head (lower) @function)
(field (lower) @property)
(param (lower) @variable.parameter)
(upper) @type
((comment) @comment.doc (#match? @comment.doc "^///"))
