; What Zed indents: the lines inside a pair of brackets, up to the closing one. `just grammar`
; runs this over the suite's programs.

(_ "{" "}" @end) @indent
(_ "[" "]" @end) @indent
(_ "(" ")" @end) @indent
