# Stilt, in *one* page

Stilt checks every **effect** a function performs, and the
compiler infers the rest.  
A line that ends with two spaces breaks.

## What it gives

- Values that are copied, never shared
- Errors in types: `raise<E>` and `try`
  - every raising call is marked
  - a catch-all needs a reason
- Fast builds, with [Cranelift](https://cranelift.dev "the code generator")

1. Write the code.
2. Run `stilt check`.

3. Read the diagnostics.

> Each name has one home.
> A reader finds it by its qualifier,
and so does a tool.

---

```stilt
fn main() / io { print("1 < 2 && 3 > 2") }
```

Escapes: \*not emphasis\*, `` a ` tick ``, snake_case_name, 2 * 3 * 4, and <https://stilt.dev>.

![The logo, *small*](logo.png)

### Closing #
