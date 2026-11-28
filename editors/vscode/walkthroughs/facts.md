# Read what the compiler infers

Stilt infers each function's types and facts, such as whether it can panic, overflow or allocate, and the editor writes them before its body. For this function:

```stilt
fn average(xs: List<i64>) -> i64 {
  var total = 0
  for x in xs { total += x }
  total / xs.len()
}
```

the editor shows `[panic, overflow]` after `-> i64`, and the type of `total`. Hover over a fact for what it means and every line that causes it. The line that holds the cursor says what it does at its end, as `// a division can panic; a / can overflow`.

**Stilt: Show Function with Its Facts** opens the function beside the editor with all of it written in, as `stilt show main.average` prints it.
