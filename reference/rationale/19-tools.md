# Rationale: Properties, edits, the REPL and engines

The tools of this chapter serve one aim. A person or an agent that changes a program learns at once whether the change is right, and learns it the same way every time. A property checks what holds for every value, including the cases its author didn't think of. Its verdict is the same on every run and in every implementation. An edit names the code it replaces by a path and a hash. So it can't land on the wrong declaration, or overwrite a change made after its author read the code. The REPL runs what the program runs, so its answers can be trusted as the program's.

## Properties

An example, `/// ex:`, checks one case. A property states what holds for every value of its parameters, and the test runner looks for a value that breaks it, as QuickCheck and Hypothesis do. Feedback from properties raises how often agents solve a task on the first attempt by 23 to 37% relative to tests alone. A counterexample that is shrunk and seeded tells an agent exactly what to fix.

A property is a doc line beside the examples ([tests.prop-lines](../19-tools.md#tests.prop-lines)), so it documents the declaration it tests and runs with it. It is a closure whose parameters' written types are the generators' only input ([tests.property-form](../19-tools.md#tests.property-form)). These alternatives are rejected:

- **Generators derived from the documented function's signature.** A property may relate several functions, or values that no single signature names. The closure's parameters are a signature of the property's own.
- **Generators that the user writes,** through a trait such as QuickCheck's `Arbitrary`. A precondition in the body covers most cases. A trait for generators would add a second way to describe a type's values, against the rule that nothing restates a type.
- **An implication operator,** such as QuickCheck's `==>`. `||` already says it, as in `|n: i64| n < 0 || isqrt(n) * isqrt(n) <= n`, and a case whose values fail the precondition counts as passing. A property whose precondition rarely holds runs few useful cases, so the better property generates the values that meet it.
- **A closure with no parameter, as a property of one case.** That is an example, which `/// ex:` already writes, and Stilt has one way to write each thing.

A parameter marked `inout` takes no generated value, since a generated value has no place for the closure to write to. So it is rejected with the other malformed parameters. A malformed property reports only E0332: the body's other errors would follow from the missing type, and the fix is to write it.

A property is checked as an example is ([tests.property-checking](../19-tools.md#tests.property-checking)). It may raise, as a test body may, since a raise is how a body reports a failed step with `try`. Discarding a case that raises, as Hypothesis's `assume` does, is rejected: an example that raises fails, and a property behaves as an example does.

A property performs no `io` ([tests.property-io](../19-tools.md#tests.property-io)). A property that reads a file or the clock could pass on one run and fail on the next, and its verdict couldn't be cached.

## Types that can be generated

Types carry no invariants, so a value is generated from its fields alone. A type is generable when its values can be built from scalars, collections, records and variants ([tests.generable-types](../19-tools.md#tests.generable-types)). The alternative is to skip the variants whose payloads can't be generated, or that hold a type with no values. A variant would then go untested without the author knowing. So a type that holds a function type, a type with no values, or a map whose key type lacks `Eq` or `Hash` is rejected wherever it appears.

A type that holds infinitely many types has no finite description to generate from. `Grow<i64>` holds `Grow<List<i64>>`, `Grow<List<List<i64>>>` and every deeper nesting. The test of [tests.growth-test](../19-tools.md#tests.growth-test) finds such a type without expanding any type, and it is exact:

- Every declaration that a type holds is given some argument, by the type or by a declaration that holds it. So each of its parameters takes some type, and a type's size is finite.
- Going once around a cycle takes the type that `D.p` stands for to the one that `E.j` stands for. Along an edge that doesn't grow, that is the same type. Along an edge that grows, it is a type that contains it, so a larger one.
- A cycle with a growing edge therefore gives, by going around it again and again, types of ever greater size, all of them held. So the type holds infinitely many types.
- Without such a cycle, going around a cycle never enlarges a type, and along a path without cycles a type grows by a bounded amount. So every parameter takes finitely many types, and every declaration is held with finitely many arguments.

## Cases

A property's verdict must be the same on every run. It can then be cached as a test's is, and an agent never chases a failure that has gone. It must be the same in every implementation, since conformance compares whether each property passed. So generation is fixed exactly ([tests.property-cases](../19-tools.md#tests.property-cases), [tests.seeds](../19-tools.md#tests.seeds), [tests.draws](../19-tools.md#tests.draws), [tests.generated-scalars](../19-tools.md#tests.generated-scalars), [tests.composite-values](../19-tools.md#tests.composite-values)). Each implementation runs the same FNV-1a, SplitMix64, generators and shrinker. Each choice keeps that cheap to specify and to implement twice. These alternatives are rejected:

- **Generation left to each implementation,** deterministic within one. A property that failed on a rare value in one implementation and not in the other would split them, and differential testing couldn't compare counterexamples.
- **A random seed, reported for replay,** as Hypothesis does by default. The verdict would change between runs.
- **A seed from the declaration's address or position.** Moving a function or formatting its file would change its cases. The seed comes from the property's text, so its cases change exactly when the property does.
- **BLAKE3 for the seed,** as edits hash parts. A seed needs mixing, and no resistance to forgery, and FNV-1a takes a few lines in each implementation.
- **A configurable number of cases.** A setting would give each project its own verdicts, against one way to do each thing. With 100 cases and 1,000 shrinking runs, `stilt test` stays fast, and a property runs its closure at most 1,100 times.

Case 0 is the minimal value ([tests.minimal-values](../19-tools.md#tests.minimal-values)), since an empty list or a zero is where many properties break. Later cases grow with the case number. A third of the scalar draws are boundary values ([tests.boundary-values](../19-tools.md#tests.boundary-values)). So `|x: i64| x + 1 > x` fails at `MAX` within a few cases, where draws from a range alone might never reach it. A composite value divides its budget among its components, so a recursive type's values stay small. A variant type at budget 0 takes only its nearest variants, so generation always ends.

## Running and shrinking

A case fails when the closure returns `false`, raises or panics ([tests.running-cases](../19-tools.md#tests.running-cases)). Shrinking keeps a candidate only when the run fails the same way ([tests.shrinking](../19-tools.md#tests.shrinking)). The alternative is shrinking to any failure, whatever its kind, as QuickCheck does. The counterexample could then show a failure met on the way, such as a panic reached while shrinking a `false`, instead of the one the case found.

Candidates come in a fixed order ([tests.shrink-candidates](../19-tools.md#tests.shrink-candidates)), compared by structure. So comparing them calls no code of the program, and two implementations shrink alike. The alternative is integrated shrinking, which shrinks the draws that made a value, as Hypothesis does. It needs every generator to be specified over a stream of bytes, while a fixed order of candidates is shorter to specify identically in two implementations.

## Results

A property is a doc example for every rule that names one ([tests.property-results](../19-tools.md#tests.property-results)). So it is checked, reported, ordered and expected by conformance tests as examples are, and needs no rule of its own in any of those places. Its verdict ([tests.property-verdict](../19-tools.md#tests.property-verdict)) gives the seed, the case and a counterexample. The counterexample is written by its structure, even for a type whose `Show` impl is the user's, since that impl could panic or hide the value that failed.

## Parts and addresses

Edits by line ranges silently corrupt 99.1% of files after a one-line shift upstream. Edits addressed by a function's name alone hit the wrong function 12.7% of the time, where names repeat. A search-and-replace edit avoids both, at the cost of quoting the code it replaces.

Stilt gives every name one home. Names are unique in each namespace of a module, across a type's inherent blocks and among a module's tests, and a trait has one impl per type constructor. So a short path names one declaration ([edits.paths](../19-tools.md#edits.paths), [edits.one-part-per-path](../19-tools.md#edits.one-part-per-path)), and a short hash tells which version of it the agent read.

A part is a declaration or its body ([edits.parts](../19-tools.md#edits.parts), [edits.bodies](../19-tools.md#edits.bodies)). These alternatives are rejected:

- **Line ranges.** One inserted line upstream makes every later range land on the wrong code, silently.
- **A name without a hash.** Unique names fix the edits that hit the wrong function. They don't fix those written against code that has changed since its author read it.
- **Search and replace as the main form.** Quoting the old code costs as many tokens as the code. A quote that matches twice, or matches after a change elsewhere, lands wrong.
- **`M.T.m` for a trait impl's method.** A type may implement two traits that each have a method `m`, and their methods would share an address. `M.T.Tr.m` is unique by coherence.
- **A declaration's part without its doc comments,** with the docs as a part of their own. Docs and their examples are edited with the declaration they describe, as `show` prints them together ([edits.extents](../19-tools.md#edits.extents)). The cost is that an edit of a declaration that leaves its docs out deletes them.
- **Deeper paths,** such as a path to one `if` inside a body, or an ordinal path like `/let#2`. A body is small enough to send again whole, and ordinal paths are fragile.
- **Addresses for `use` declarations, module headers and new declarations,** such as an edit that inserts after a part. An agent adds a declaration, or changes imports, by writing the file, and a fix that adds an import carries no edits.

A path's module is never in doubt ([edits.reading-paths](../19-tools.md#edits.reading-paths)), since case already tells modules from types and traits. So an address is read without resolving names. A body is addressed apart from its declaration ([edits.body-addresses](../19-tools.md#edits.body-addresses)). An edit that changes only code inside a function sends the body alone, and leaves untouched the signature and the docs that callers rely on.

## Hashes

Formatting must never invalidate an address. The hash covers the part's canonical text ([edits.canonical-text](../19-tools.md#edits.canonical-text)), which the canonical format makes a function of the syntax tree and the comments. So reindenting a file, moving a method between blocks or changing a signature leaves a body's hash as it is. Two alternatives are rejected:

- **Hashing the source bytes.** `stilt fmt`, or an editor that reindents, would invalidate every address in a file without changing any code.
- **Hashing the tree without comments,** as `parse --sexp` prints it. An edit would then silently delete a comment that someone added after the agent read the code.

The hash has four hexadecimal digits ([edits.hash](../19-tools.md#edits.hash)). The path already names one part. So the hash only has to tell the version an agent read from the one there at the moment of the edit, and never one part from all others. With 16 bits, a part that changed keeps its hash once in 65,536 changes, and only an edit written against an older version can meet that case. On `o200k_base`, a hash costs 3.5 tokens on average with four digits, 4.7 with six and 5.8 with eight. Six or eight digits would cost one or two more tokens in every address, every `at` and every fix. They would make rarer an event that needs a stale edit to begin with.

A declaration with a syntax error has no canonical text, so it is hashed as written ([edits.files-with-syntax-errors](../19-tools.md#edits.files-with-syntax-errors)), and an agent can still replace it whole.

## Showing parts

An agent edits in two steps. `stilt show ADDRESS --json` gives a part's text and its `at` ([edits.showing-parts](../19-tools.md#edits.showing-parts)), and an edit sends it back changed. A diagnostic carries the `at` of the smallest part that holds it ([edits.diagnostic-addresses](../19-tools.md#edits.diagnostic-addresses)), so a verdict says what to read and what to replace. A refusal costs one more `show`.

## Edits

The verdict must follow the edit in the same answer, so `check` and `test` take edits ([edits.command-line](../19-tools.md#edits.command-line)). The alternative is a separate `stilt edit` command. It would split one request into two answers, and Stilt keeps a small, fixed set of commands. A JSON list of edits on standard input is rejected as a second form of the same request: `--edit` repeats, and `-` passes one long text without quoting.

The new text must parse as the part it replaces ([edits.new-text](../19-tools.md#edits.new-text)), and an edit whose code has changed since its author read it is refused ([edits.refusals](../19-tools.md#edits.refusals)). Every edit is checked against the files as they are before any applies, and all apply or none does ([edits.all-or-nothing](../19-tools.md#edits.all-or-nothing)). The alternative is applying edits one after another, each against what the one before left. An agent writes every edit of a change against what it read, and a change applied in part leaves a program that no one wrote.

A refused edit ends with status 2. Status 1 is that of a program with errors, while a refused edit gives no verdict, and 2 is the status that `show` gives a request it refuses. Two commands that edit one part from one hash can't both apply ([edits.concurrent-edits](../19-tools.md#edits.concurrent-edits)), so two agents never overwrite each other unseen.

An edit writes only its part ([edits.writing](../19-tools.md#edits.writing)), so the rest of a file that isn't canonical keeps its bytes. A refusal reports no diagnostic of the program ([edits.edit-results](../19-tools.md#edits.edit-results)), so no reader takes it for a verdict.

## Edits in verdicts

A diagnostic's fixes are edits in the form `--edit` takes ([edits.json-form](../19-tools.md#edits.json-form), [edits.fixes-as-edits](../19-tools.md#edits.fixes-as-edits)). So an agent applies a fix by passing its fields back, and its result is checked in the same answer. A fix carries the whole text of the body or declaration it changes, so a verdict grows with the size of the bodies it fixes. Deeper paths would shrink it, at the cost of the fragility that [Parts and addresses](#parts-and-addresses) describes.

## The REPL

Lisp's live image and its REPL are the interactivity that compiled languages lose. Stilt keeps no image: `stilt run` patches each edit of a program's files into the running program, every function being called through a slot that holds its latest code. The REPL gives the rest ([repl.sessions](../19-tools.md#repl.sessions), [repl.scope](../19-tools.md#repl.scope)). An input is evaluated in a module's scope and answered in well under the tenth of a second that feels instant. Its state survives edits of the module's files.

An input is code of the language, checked as a test's body is and compiled into the image that holds the program's code ([repl.input-checking](../19-tools.md#repl.input-checking), [repl.running-inputs](../19-tools.md#repl.running-inputs)). So it runs what the program runs. The alternative is a second evaluator, such as the reference interpreter answering inputs. Its answers could differ from what the compiled program does, and an input couldn't call the program's code as it runs.

A session compiles only what its inputs reach, so it starts without compiling the program. It checks its inputs in the program's engine ([repl.prompt-and-end](../19-tools.md#repl.prompt-and-end)), which holds what the program's commands have already checked. So an answer needs no check of the program again.

An input is an expression or a `let` ([repl.inputs](../19-tools.md#repl.inputs)). Declarations at the prompt are rejected: a declaration typed into a session lives in no file, so neither the program nor the next session sees it. A `var` that inputs assign is rejected too: a `let` bound again serves, and an input stays the body of one test. An input spans one line, so an expression over several lines is written on one, or as a function of the program.

An answer shows the value as `show_nested` does ([repl.answers](../19-tools.md#repl.answers)). The alternative is `show`, which writes a string as it is. The value of `"7"` would then read as a number's, and a string that holds a newline would break its answer over two lines. A panic in the input itself is reported without its `at` line, since the input is the line just typed.

Bindings keep their values across edits ([repl.program-edits](../19-tools.md#repl.program-edits), [repl.bindings-across-edits](../19-tools.md#repl.bindings-across-edits)). Two alternatives are rejected:

- **Running the session's inputs again after each edit,** so that bindings follow the program's new code. It repeats every input's `io`, and its time grows with the session.
- **Dropping every binding when any declaration changes,** as `run` starts a program again. A binding of `i64`, or of a type that the edit left alone, keeps its meaning. Only values whose layout the edit may change are dropped.

A one-shot `stilt repl --eval EXPR` is rejected ([repl.no-one-shot-evaluation](../19-tools.md#repl.no-one-shot-evaluation)). Tests, doc examples and properties already evaluate code once, and keep it where it is checked again. The REPL's refusals are messages, without diagnostic codes, as `run`'s refusal of a program without `main` is. An input's diagnostics are the language's own.

## Engines

An engine decides what each command it answers reports. For `run`, `test` and the REPL, it also decides the code that the command compiles and runs. So only its user may reach it ([engines.private](../19-tools.md#engines.private)). A socket that another user could reach, or an engine of another user that a command could ask, would let one user run code as another.

The directory is the guard on every system. Where the system gives it, the check of the user at the other end is a second guard. A directory that another user could open once may still hold that user's socket after it is closed. A command that can't trust the directory runs without an engine and still succeeds, since an engine only saves time: its report is the one the command gives alone. A directory of the user's that others may open is closed, and not refused, since the user's own tools may have made it so. Nothing else in it is trusted.

Each version of the toolchain has engines of its own ([engines.toolchains](../19-tools.md#engines.toolchains)). An editor and a terminal may use two versions on one program. One engine for both would stop at each command of the other and check the program again for the next. Two engines on one program cost the memory of two databases, which only a user of two versions pays.

Two builds of one version share an engine's place instead, and a command of the newer build stops the engine of the older one. A build of the compiler from changed sources is the newer one, and the engine of the build before it would answer from code that no longer exists.
