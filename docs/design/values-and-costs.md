# Values with inferred costs

*Part of the [design sketch](design-sketch.md). It covers memory safety, concurrency and performance: where values live, where they are updated in place, what may run in parallel, and which run-time checks can go. [What you write, what is inferred](inferred-facts.md) gives the rules for the facts this page mentions.*

Every value behaves as an independent copy. That one meaning leaves the compiler free to choose where a value lives and how it is passed, and the choice is a fact the tools show, never something the programmer writes. Stilt's core already has no identity, no null and no shared mutable field, so the compiler can store values inline and update them in place without asking anyone to prove it safe.

## Memory safety (Rust)

Stilt is memory-safe and data-race-free without a tracing garbage collector, and no tier writes a lifetime. Safety comes in layers; you only climb when you need to.

1. **Values by default.** Every type has value semantics: assigning or passing a value gives an independent copy, and only `var` bindings and `inout` parameters can change. Copies are cheap.
   - Fixed-size records and variants are stored inline; heap data (strings, lists, maps, closures and recursive edges) is reference-counted with Koka's Perceus scheme, which removes most increments and decrements.
   - Heap data is copied only when a shared value is written.
   - Mutable data can't be aliased at this layer: this is the "mutable value semantics" of Hylo and Swift.
2. **`inout`, the one written mode.** An `inout` parameter has exclusive access to the caller's place, marked at the call site. It can't be stored or returned, so it never needs a lifetime. Every other parameter reads its argument, and whether the callee consumes it, reusing its memory in place, is inferred and shown.
3. **Inferred modes** ([modes.bindings-and-axes](../../reference/13-modes.md#modes.bindings-and-axes)). Every local, closure and parameter has a point on each axis of a lattice, which the compiler infers and shows where it isn't the default, and which no program writes:
   - **locality:** a value or closure that doesn't escape its scope lives on the stack, so the closures passed to `map` or `fold` never touch the heap;
   - **uniqueness:** a value with one owner is updated in place with no check, and Perceus stays the dynamic fallback;
   - **once:** a closure runs at most once, so it may hand its captures over at its call;
   - **portability and contention:** whether a value may cross to another thread, and whether several threads may reach it.

   The law of exclusivity becomes one rule: a unique access excludes every overlapping access ([modes.law](../../reference/13-modes.md#modes.law)). Types with no mutable heap state cross the thread axes automatically, so most code never meets them. OxCaml infers the same lattice, and mode crossing kept Jane Street's 80M lines to about 6,000 annotations ([Peters, Jacobs et al., ICFP 2026](https://dl.acm.org/doi/10.1145/3828681)).
4. **Views and projections** (`advanced` tier). Code that needs to look into a value without copying it uses a view that can't escape: a slice of a string or a list, or an iterator ([views.what-view-is](../../reference/13-modes.md#views.what-view-is) and [views.view-types](../../reference/13-modes.md#views.view-types)). A view's dependence on a parameter is inferred from the signature: a result views every argument it could view. A projection is a function whose result is written `inout T` and whose body `yield`s a place, as Hylo's subscripts do: its call is a place, the caller reads or changes it, and the projection resumes once the caller is done with it; a view made through `inout` writes its source, and a result writes every argument passed `inout` ([projections.declaring-projection](../../reference/13-modes.md#projections.declaring-projection) and [projections.results-that-write](../../reference/13-modes.md#projections.results-that-write)).
5. **Shared mutable identity** (`advanced` tier). `Shared<T>` covers graphs and caches, where a change must be visible through every handle. A `Shared<T>` is a Verona-style cown: its contents are reachable only inside `when (a, b) { … }`, which runs once it holds every cown it names, so it never deadlocks. Handles may hold one another in cycles, which the runtime frees by trial deletion of the shared objects alone once nothing else reaches them, so a graph needs no weak references ([cycles.freeing](../../reference/14-tasks.md#cycles.freeing)).
6. **`unsafe` blocks** (`systems` tier) for C's pointers and calls into C ([c.unsafe-and-foreign](../../reference/20-builds.md#c.unsafe-and-foreign)), and later inline assembly. Each needs a written justification, and `stilt show` lists them all. `unsafe` blocks and the foreign functions they call are inferred facts, shown next to each signature, which no caller inherits, so a safe wrapper of C is called as any function is: `without unsafe` keeps the blocks out of a module's or a function's own code, and a package's manifest keeps them out of its dependencies unless it grants `unsafe`. No tier needs a limit for that, since these facts are what a limit on the `systems` tier would have kept out.

First-class references with lifetimes, checked flow-sensitively as Rust's Polonius does, were weighed and rejected: non-escaping views cover iterators and slices without annotations, and lifetimes are exactly the proof by annotation that Stilt infers away. Inferring lifetimes or regions to stand in for a borrow checker was rejected too: Ante advertised it, then moved to Rust-style borrowing ([Ante](https://antelang.org/blog/safe_shared_mutability/)). Run-time borrow counts and generational references were rejected because they fail at run time, where Stilt's failures are typed.

```stilt
// `inout`: exclusive access, no lifetime anywhere
fn normalize(inout v: Vec3) {
  let len = v.length()
  v.x /= len
  v.y /= len
  v.z /= len
}

// A view (advanced tier). It can't outlive `line`, the one parameter
// it could view, and nothing in the signature has to say so.
fn first_word(line: str) -> View<str> {
  line.view(0, line.find(" ") else line.len())
}

// Functional style, imperative speed: `insert` consumes `tree`, so when
// a caller passes its last use, the nodes are reused in place
fn insert(tree: Tree<i32>, x: i32) -> Tree<i32> {
  match tree {
    Leaf => Node(Leaf, x, Leaf)
    Node(l, v, r) =>
      if x < v { Node(insert(l, x), v, r) }
      else { Node(l, v, insert(r, x)) }
  }
}
```

## Concurrency

Every 2022–2026 answer to data races proves that no two threads can reach the same mutable memory. Stilt's core guarantees it by construction: closures capture copies, and `inout` can't be stored. So concurrency is where Stilt can be simpler than Rust and still promise more.

- **Deterministic parallelism in `core`.** The standard library's `par`, `par_each` and `par_map` accept only closures whose row is empty. Their meaning is the sequential result, and the reference interpreter runs them sequentially, so the rule an agent learns is one sentence: a pure closure may run in parallel, and the result is the same. Splitting a list into `inout` parts gives race-free parallel writes in place. Release builds schedule by heartbeats, which need no grain size ([Westrick et al., POPL 2024](https://cs.nyu.edu/~shw8119/24/popl24-par-manage.pdf)), and floating-point reductions use a fixed tree, so they stay deterministic.
- **Counts that are atomic only when shared.** A reference count is updated non-atomically until its value reaches another thread, which a bit in the object header records. Forcing every count atomic slowed Koka by 5–59% ([Perceus TR](https://www.microsoft.com/en-us/research/uploads/prod/2020/11/perceus-tr-v4.pdf)).
- **Structured tasks** (`advanced` tier). A `scope` runs tasks that can't outlive it, so they can read the spawning scope's values safely, and when one task raises, the scope cancels its siblings.
- **`async` as an effect** (`advanced` tier). Starting and waiting for tasks performs `async`, whose handler `main` chooses: threads, or one-shot fibers on an event loop. No function is coloured and no executor locks anyone in.
- **Thread safety from modes** (`advanced` tier). Portability and contention say what may cross threads, so there is no `Send` and no `Sync`. Marker traits were weighed and rejected: they restate what a type's contents already imply, and every generic signature would carry them.
- **Deadlock-free shared state** (`advanced` tier). A `when` block on several `Shared<T>` values runs once it holds all of them, and behaviour-oriented concurrency of this kind can't deadlock; its banking benchmark needed 35% of Pony's code ([BoC](https://marioskogias.github.io/docs/boc.pdf)). Locks were rejected because they can.

```stilt
// core: the same result as `map`, on every core
let scores = players.par_map(|p| simulate(p, SEED))

// advanced: runs once it holds both accounts, and can't deadlock
fn transfer(from: Shared<Account>, to: Shared<Account>, n: i64) {
  when (from, to) {
    from.balance -= n
    to.balance += n
  }
}
```

Rust can't retrofit determinism or deadlock freedom. The risks are that copy-on-write copies a shared list before parallel writes into it, which `show` must report, and that Cranelift's support for switching stacks, which fibers need, is unverified.

## Performance (C++)

Stilt targets C++ and Rust speed with no tracing garbage collector, no mandatory runtime and no hidden costs.

- **No GC.** Memory is managed by reference counting with in-place reuse (see Memory safety). Async executors are handlers of the `async` effect, so there's no runtime you can't remove.
- **Values stored inline.** Records, tuples and variants whose types aren't recursive live inline, a word per field, in locals and in each other's fields, and pass and return in registers, so making, matching and updating one allocates nothing. Reference counting stays for buffers, closures and recursive edges, one node per value of a recursive type rather than one box per field: a header of two words, whose second tells which of the node's fields are heap words, then a word per field. A node that a `match` takes apart and that its arm builds again in place, the last reference to it, costs a test of its count and the writes of the fields that change. Lists hold their elements inline too, each at its own size, and a narrow scalar in its own width, so a `List<bool>` takes a byte per element. A string of at most seven bytes is held in its word, so slicing, splitting or interpolating short text allocates nothing, and a list of short strings holds their bytes in its elements; a longer string is an object of its bytes after a header and a length, 24 bytes more, and one that a loop appends to keeps as much room again after them. A slice copies its bytes rather than share its parent's: a string is one word, so a view of the parent would take an object of its own, whose allocation costs what copying a few hundred bytes does, and it would keep a large parent alive for as long as a small slice of it lived, the trap that made Java stop sharing substrings. Since a slice can still allocate, `slice` keeps the `alloc` fact ([facts.native-allocation](../../reference/15-facts.md#facts.native-allocation)), and `std.view` is the way to look into a string without a copy. Generic code is compiled once per layout of its type arguments, not per type, so a value of several words stays inline where a type parameter stands too: in a generic function's parameters and results, in a map's entries, in a field typed by a parameter, such as `Option<Particle>`'s, and as generic code reads a list's element. Each type parameter's witness gives its argument's shape, the size and the counted words of its values, so a list that generic code makes holds its elements as the code that names their type reads them. Dictionaries stay, one per bound; a trait's method with type parameters of its own is called directly where the bound's argument is known, since a dictionary's entry is compiled once for all their layouts. No value of a fixed size is boxed, whatever its size, and an error of several words that comes through a closure or a row variable comes back in memory its caller provides. Only polymorphic recursion, past the caps that keep its instances finite, and a debug build's reflection, whose functions are compiled once for every type they reflect on and read each part through its descriptor, hold a value in a box. An `inout` access to an inline value writes it in place and checks nothing; one through a list's element makes the list unique once and writes the element in place. Swiftlet ran nbody four times slower than Swift mostly through needless uniqueness checks ([Racordon et al., JOT 2022](https://www.jot.fm/issues/issue_2022_02/article2.pdf)), and boxed elements cost Lean 4 its quicksort ([Ullrich & de Moura](https://arxiv.org/pdf/1908.05647)).
- **A cheap optimizer before Cranelift.** Debug builds run scalar replacement of aggregates on each function's MIR, inline the standard library into user functions, and compile each generic function once per layout shape, with a table for trait methods only. The standard library is compiled once, at Cranelift's highest level. In a running program none of it crosses a user function's boundary, so each function can still be patched alone; a build, which has no edit to patch, also inlines small user functions, and built and running code differ in speed alone, and `just bench` gates every rewrite rule, since one Wasmtime benchmark ran 2.55x faster with optimizations off ([wasmtime #12106](https://github.com/bytecodealliance/wasmtime/issues/12106)).
- **Release builds through C.** The release backend emits freestanding C11, one file per module, and lets a pinned clang, which `stilt` fetches the first time a release build needs it, optimize the program, guided by its profile ([builds.release-builds](../../reference/20-builds.md#builds.release-builds)). The runtime's hot paths are a header the C compiler inlines, a list's length and elements stay in C locals across the stores to its elements, and WebAssembly comes through the same clang. The emitted C never reaches C's undefined behaviour: overflow goes through the compiler's checked builtins, wrapping arithmetic through unsigned types, a shift checks its amount and a division its divisor, including `MIN / -1`, and the code compiles with `-fwrapv -fno-strict-aliasing -ffp-contract=off -fno-math-errno`, so no multiply and add fuse, with a probe of each page of a large frame, so a stack overflow still ends with status 134, and with `#line` directives. On the benchmark suite, release builds run at 1.07 times their Rust baselines' cycles, as a geometric mean.
- **Specialization.** A release build specializes every instantiation a program reaches, of its type parameters, its value parameters and its reflection, and folds those whose code is the same, so only polymorphic recursion and polymorphic arguments keep dictionaries, and its performance report lists them. Cheap counters in debug runs make a profile, committed as text beside the manifest so builds stay reproducible, which tells the C compiler which branches are likely and which functions are hot.
- **Layout control** (`systems` tier). C-compatible, packed and aligned layouts; a `soa` attribute stores a `List<Particle>` as one array per field. SIMD vector types are in the standard library; inline assembly is available in `unsafe`.
- **Allocation is an implicit effect.** The compiler infers which functions allocate and shows it next to their signatures. `without alloc` forbids allocation in hot code in any tier, and on a function that consumes its arguments it promises updates in place. The `systems` tier chooses the allocator by handling the effect:

```stilt
fn render_frame(scene: Scene) -> Frame { … }   // inferred: [alloc]

with arena(4 * mem.MIB) {
  let frame = render_frame(scene)  // every allocation lands in the arena
  gpu.submit(frame)
}                                    // freed in one step; `frame` can't escape the block
```

- **Checks that cost little.** Bounds checks are on by default. Verification runs inside `check`: an abstract interpretation of each body over intervals and differences finds range and length facts, and each proof discharges a `bounds`, `missing-key` or `divide-by-zero` panic, or an overflow, so `without panic` accepts the index and release builds drop the check, while debug builds keep it. Integer overflow traps in every build, as in Swift; wrapping arithmetic uses explicit operators like `+%`, as in Zig.

LLVM IR was weighed as the release backend and kept as the fallback. It gives precise integer semantics and guaranteed tail calls directly, but the runtime would have to ship as bitcode to inline, and Lean's LLVM backend lost to its own C backend on exactly that point ([lean4 #3192](https://github.com/leanprover/lean4/issues/3192)). C gives every target a C compiler reaches, and no record guarantees a tail call, so C's lack of one costs nothing. An LLVM backend is built only if C output misses the release gate (goal `release-speed`).

Refinement predicates written on type declarations were weighed and rejected: they would be type invariants, which the design rejects permanently, so the facts stay attached to the checks they discharge, and they are inferred. An SMT solver was rejected too: its verdicts depend on its version and its limits, so two implementations couldn't reach the same ones. Verification stays in a domain that a record fixes, with a decision procedure of its own in each implementation.

Stilt still pays a small tax against hand-tuned C++:

- reference counting on heap buffers, mostly elided by Perceus and inferred uniqueness;
- the bounds and overflow checks that verification can't remove;
- runtime method tables for polymorphic recursion and polymorphic arguments, the only generic code a release build can't specialize, which its performance report lists.
