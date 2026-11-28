kind: fix

A closure given to `std.par` that captures a record or a variant type with a `Shared<T>` in a field or a payload is now E0431, as one that captures the handle itself is, and the message names the field. A generic type at an argument that its declaration places in no field, such as `Tag<Shared<i64>>` for `type Tag<T> = { n: i64 }`, holds no `Shared<T>` and is accepted. `stilt show` also marks a `spawn` whose closure captures a record with a task's handle in a field.
