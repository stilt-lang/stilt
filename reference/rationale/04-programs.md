# Rationale: Programs, modules and packages

A Stilt program is read by people, by agents and by tools that address its declarations by path. Most rules of this chapter follow from one principle: every name has exactly one home. If you see a name, its qualifier tells you where it is defined, and a search for its definition finds one place. The same care covers what lies around the code. A manifest pins what a program may import and what its dependencies may do. Editions let the language fix its mistakes without breaking anyone, and pinned docs can't drift from the code they describe without a warning.

## Programs and modules

A module's name comes from its file's path ([program.module-names](../04-programs.md#program.module-names)), so a module has one name, and no header can contradict it ([program.module-header](../04-programs.md#program.module-header)). A single file is always module `main`, whatever it is called ([program.forms](../04-programs.md#program.forms)). So the functions of `orders.lt` are addressed as `main.parse_line` and `main.totals` wherever the file is copied, and an address stays the same when the file is renamed. Paths are reported relative to the root directory, with `/` ([program.report-paths](../04-programs.md#program.report-paths)), so two machines, and two implementations, report the same text.

A file with an invalid name is still checked. Its own mistakes are reported where they are, while the modules that name it get the error type and no second error.

Symbolic links are followed, and each module is named after the link's path. A folder shared between programs is then part of each program that links it, under the name that program gives it. A link that would make a cycle is skipped, because walking it would never end. Only regular files are read, because reading a named pipe or a device may block or never end.

Entries whose names start with `.` belong to other tools: `.git/`, an editor's lock file such as `.#main.lt`, or a cache. Leaving them out of the program means that another tool's files never become modules. It also means that `stilt fmt`, `meta.File` and both implementations agree on which files a program holds ([program.module-names](../04-programs.md#program.module-names)).

## Module headers and tiers

A header names its module and may limit facts ([program.module-header](../04-programs.md#program.module-header)). The alternative is a separate header option for each check, such as `total` and `noalloc`. That gives two spellings of one check, and no way to limit a single function, which a function's own `without` clause can do.

The language comes in four ordered tiers ([program.tiers](../04-programs.md#program.tiers)). A reader, a teacher or a reviewer can then say how much of the language a module needs. A core module stays readable to someone who knows only the core. Haskell instead gives each feature its own switch, as its language extensions are. Four ordered tiers give four dialects to learn and to report on, while independent switches give one dialect for every combination of them.

A module's tier is inferred, never declared ([program.module-tier](../04-programs.md#program.module-tier)). Declaring it in the header, to unlock a later tier, would put a line in every module that uses a later feature. That line would assert nothing that the compiler can't find out, because the features a module uses already decide its tier. A limit on a module's tier, through an option or a `without` entry, is left out for the same reason. The one use of such a limit is to keep unsafe code and foreign calls out of a module. `without unsafe` already does that, as a limit on an inferred fact. So reaching a later tier costs nothing to write, and you see a module's tier in the tools.

E0203 ([program.unsupported-tiers](../04-programs.md#program.unsupported-tiers)) is for an implementation that supports fewer tiers than the language defines. Such an implementation then rejects a feature with a known code, and every program gets the same diagnostic from it.

## Visibility

Items are private unless marked `pub` ([program.visibility](../04-programs.md#program.visibility)), a keyword familiar from Rust. Go marks visibility by capitalization instead. Stilt can't, because case already has a grammatical meaning: an uppercase name is a type, a variant, a trait or a constant. A signature that other modules see can't mention a private type ([program.private-in-signatures](../04-programs.md#program.private-in-signatures)), because those modules couldn't name the type it uses.

## Imports

`use` imports modules, never items ([program.what-use-binds](../04-programs.md#program.what-use-binds)). Rust's `use std::fs::read` imports one function. It breaks the rule that every name has one home: `read` is then written bare in one module and `fs.read` in another. A search for its definition must then follow the import. Aliases and re-exports are left out for the same reason. E0230 names the most common form of the mistake, a `use` of an item. Its fix writes the module, so that the code that names the item through it then checks. The name that the `use` binds has the error type, so one mistake gives one diagnostic.

Modules can't depend on one another in a cycle ([program.no-cycles](../04-programs.md#program.no-cycles)), because each module is compiled against the interfaces of the modules it depends on. Imported modules share the value namespace ([program.one-value-namespace](../04-programs.md#program.one-value-namespace)). A local named after an imported module would make `m.f` ambiguous, so it is an error, where shadowing it would change the meaning of `m.f` without a word.

## The prelude

The prelude is a fixed list ([program.contents](../04-programs.md#program.contents)). A prelude that libraries can extend is a re-export by another name, so no library extends it. Its names mean the same thing in every module ([program.prelude-names](../04-programs.md#program.prelude-names)).

A prelude item's name is reserved in its own namespace only ([program.prelude-namespaces](../04-programs.md#program.prelude-namespaces)). A name is read in one namespace at a time, so a variant `Eq` can't be taken for the trait `Eq`. Reserving the name in both namespaces would cost renames and protect nothing.

Every name outside the prelude is written qualified where it is used ([program.qualified-names](../04-programs.md#program.qualified-names)), which keeps path-and-hash addressing unambiguous. A pattern's variant needs no qualifier, because the type it matches gives the variant's one home. Without that exception, a walker over another module's syntax tree would repeat the module's name on every arm.

## The entry point

`main` takes no arguments ([program.main](../04-programs.md#program.main)). The arguments come from `std.cli`, so every program has one entry point of one shape. A raise that escapes `main` prints `error: …` and exits with status 1 ([program.exit-statuses](../04-programs.md#program.exit-statuses)), so most programs never need a `catch` at the top level. `exit` has type `Never` ([program.prelude-functions](../04-programs.md#program.prelude-functions)), so a `catch` arm or an `else` branch that calls it checks wherever a value is expected.

`check` and `test` need no `main` ([program.missing-main](../04-programs.md#program.missing-main)). A library, and a program checked by its tests alone, are complete without one.

## How a program ends

Each way a program ends has its own status ([program.exit-statuses](../04-programs.md#program.exit-statuses)), so a script can tell a raise from a panic, and a panic from a crash. The panic report is two fixed lines at the end of stderr ([program.panic-report](../04-programs.md#program.panic-report)), so a tool, a test or an agent finds it without parsing anything else. Its detail is fixed only where the program wrote it ([program.panic-detail](../04-programs.md#program.panic-detail)). Its location is the operation in the program's own files, and the call into the library when the panic is inside it ([program.panic-location](../04-programs.md#program.panic-location)), because that is where you can act.

Output isn't held until the program reads or exits ([program.output-flushing](../04-programs.md#program.output-flushing)). If it were, a program that reports progress, such as a search that prints each depth, would be read only at its end. A program that only prints would hold an unbounded buffer.

## Tests and doc examples

`check` runs no tests ([program.running-tests](../04-programs.md#program.running-tests)). It answers a static question fast, and `test` gives the full verdict. An `exit` in a test ends only that test ([program.test-results](../04-programs.md#program.test-results)). If it ended every test, it would hide the results of the tests after it, as a panic would. Tests run in a fixed order ([program.test-order](../04-programs.md#program.test-order)), so what they print comes out the same on every run, though it isn't part of their result.

A doc example ([program.doc-examples](../04-programs.md#program.doc-examples)) is a test that lives in the doc it illustrates. `test` runs it, so it can't drift from the code it documents, and an agent that reads a function's doc reads a checked fact about the function. It is checked as a test body of its module, so it reads as the module's own code.

## Programs with errors

`run` runs a program that has errors ([program.programs-with-errors](../04-programs.md#program.programs-with-errors)). If it refused, an agent or a person fixing one function couldn't see the rest run, and an option to run anyway would split the language into two behaviours. The run exits with status 2 however it ends, so that no script takes it for a success.

The unit that a `check-error` panic replaces is a body with its declaration ([program.bodies-with-errors](../04-programs.md#program.bodies-with-errors)). A panic at the expression that meets the error type would be finer. But which expressions a type checker gives the error type isn't part of the language, so two implementations would panic in different places. A body is the smallest unit whose errors every implementation agrees on. For the same reason, the ways a body gets an error are listed in full ([program.errors-in-bodies](../04-programs.md#program.errors-in-bodies), [program.meeting-the-error-type](../04-programs.md#program.meeting-the-error-type)). A body without an error checks as it would in a program without errors, so it runs. An error in a type's declaration stops only the code that touches the part with the error ([program.errors-outside-bodies](../04-programs.md#program.errors-outside-bodies)).

A `check-error` panic is located at its declaration, not at an error ([program.check-error-report](../04-programs.md#program.check-error-report)). A body can hold several errors, or meet the error type through an error elsewhere, while its declaration is one place, and the diagnostics already locate the errors. A file with a syntax error still runs ([program.syntax-errors-at-run](../04-programs.md#program.syntax-errors-at-run)). Otherwise a typo in one function would stop the whole program. Reading the file a part at a time, as `check` reads it, runs every declaration that the syntax error leaves whole.

## Packages

Models that write code invent package names, and attackers register the names they invent. In Stilt, nothing installs on import. A package imports only the dependencies that its manifest names, and the manifest pins each fetched one by its content hash ([packages.manifest](../04-programs.md#packages.manifest), [packages.dependencies](../04-programs.md#packages.dependencies)). An agent that wants a package writes its `from`, and the first `check` pins it, so an invented name fails at that check and installs nothing.

A dependency's entry is named as its package names itself ([packages.dependency-names](../04-programs.md#packages.dependency-names)). If an entry could name its dependency by its key alone, two packages could call one dependency by two names, which is an import alias. A name isn't required of every package ([packages.package-table](../04-programs.md#packages.package-table)): a program that nobody depends on has no use for one, so a package needs a name once another depends on it.

A path dependency is the directory as it is ([packages.path-dependencies](../04-programs.md#packages.path-dependencies)), for packages developed together. A fetched package is built from its own content alone, so only the root and its path dependencies may have path dependencies.

## Fetched dependencies

A dependency comes from a git repository, whose tags are its versions ([packages.versions](../04-programs.md#packages.versions)). Archives over HTTPS, which Cargo and npm fetch, need a URL scheme for each host, while every host serves git. The content hash ([packages.content-hash](../04-programs.md#packages.content-hash)) makes the transport irrelevant to what is built. The hash covers only what building reads, so any mirror serves a package, and a change to a README never changes the hash. `stilt` speaks git's protocol over HTTPS by itself ([packages.fetching](../04-programs.md#packages.fetching)), so a machine needs nothing but `stilt` to build a program.

You write the `from`, and every command fills in the rest ([packages.filling-in](../04-programs.md#packages.filling-in)) and reports what it fetched ([packages.fetch-report](../04-programs.md#packages.fetch-report)). A pinned entry never changes until its author changes it. Content is checked against its hash each time it is read ([packages.checked-content](../04-programs.md#packages.checked-content)), so no one can change a package unseen, in a cache or upstream.

## Dependencies in a program

A dependency's module `main` is named after the package, and its other modules after the package and their own names ([packages.modules-of-dependencies](../04-programs.md#packages.modules-of-dependencies)). A prefix of their own, such as `D.main` for the root module or `deps.D.a.b`, would add nothing a reader needs. The package's name is the one prefix that tells you where a module comes from. With this rule, `use json` reaches the root module, and nothing in a package changes when another package depends on it. The cost is that an item of a dependency's module `main` hides its module of the same name.

A module imports only from its own package, `std` and the packages its manifest names ([packages.imports](../04-programs.md#packages.imports)). So every import is pinned in the manifest of the package that makes it, and a dependency of a dependency is no import of its own.

A package's modules are named after the package. Two packages of one name in a program ([packages.one-name-one-package](../04-programs.md#packages.one-name-one-package)) would then give a type or a function of one the name of one of the other. A package that depends on itself ([packages.dependency-cycles](../04-programs.md#packages.dependency-cycles)) would give its modules two names: its own, and those that its dependents give them.

A fetched dependency's errors are its author's to fix ([packages.dependencies-with-errors](../04-programs.md#packages.dependencies-with-errors)). The program reports one E0607 for it instead of each of its diagnostics, and can't use the items they touch. A path dependency's errors are the program's own, reported in its files.

## Granted effects

A grant in the manifest is a limit on what a dependency's own code does to the world ([packages.grants](../04-programs.md#packages.grants)). It is written once, where the dependency is used, as a `without` is a limit written where code is. A raise needs no grant, because its error type is in the signature of each function that raises it, and the caller sees it there.

A package's own effects are counted at its calls to other packages' functions ([packages.own-effects](../04-programs.md#packages.own-effects)). Its functions' rows can't be used for this, because a row also holds the effects of the callbacks a function takes. A function such as `fn each(xs: List<str>, f: fn(str) / io) / io` would then need a grant for its user's effects. Counting the effects that pass through a dependency as its own fails the same way. Every dependency that takes a callback, as a list library does, would need `io` granted whenever its user prints, and the grant would stop saying anything. The rule has a cost. A package that calls another's function whose row names `io` needs the grant. That holds for a function that only takes a callback whose row names `io`, even when the callback that the package gives it is pure.

A grant for each function that the program calls wouldn't bound what runs, because a dependency can return a closure that performs the effect. A grant for each package is checked once, over the package's own code. `panic` and `alloc` can't be granted. Nearly every package can panic or allocate, so their grant would be noise, and `without` already limits both where the code that cares about them is written.

A dependency whose grant falls short is an error at its entry ([packages.ungranted-effects](../04-programs.md#packages.ungranted-effects)), and its offending functions don't run ([packages.running-with-ungranted-effect](../04-programs.md#packages.running-with-ungranted-effect)). So no command performs an effect that a manifest doesn't grant. A package has no build script, and `stilt test` never runs a dependency's tests ([packages.no-build-time-code](../04-programs.md#packages.no-build-time-code)). A dependency's tests may perform `io` that its grant doesn't cover, and its author's checks already ran them.

## Editions

A language that never breaks anything keeps every mistake it makes, and a language that breaks programs on upgrade can't be relied on. Editions, as Rust has them, resolve the two. A package names the edition it is written in ([editions.edition](../04-programs.md#editions.edition)), and every toolchain reads every edition with its own meaning. Packages of different editions make one program, and a tool rewrites a package from one edition to the next ([editions.migrate](../04-programs.md#editions.migrate)). The `go` line of Go's `go.mod` does the same for its language version.

Without editions, every release would keep everything forever, and a mistake in a name or a rule could never be fixed. Go names a language version for each release, as `go 1.22`. A toolchain released every two months would make as many languages, and you would need a table to know what each version means. An edition changes at most once a year ([editions.only-editions-break](../04-programs.md#editions.only-editions-break)).

A package without an `edition` is of the first edition. If it took the newest, it would change meaning when a new edition arrives, which is the break editions exist to prevent. Editions don't change what `std` does ([editions.what-an-edition-changes](../04-programs.md#editions.what-an-edition-changes)). Otherwise an item would mean one thing to one package and another to its dependency, while their values cross between them. So the promise holds by construction: a program keeps its edition until its author runs `migrate`, and every toolchain keeps each edition's renames ([editions.renames](../04-programs.md#editions.renames)).

## Pinned docs

Models treat comments as true even when they contradict the code. So a doc is pinned to its declaration's signature ([docs.pins](../04-programs.md#docs.pins)), and a doc left untouched after its signature changed is stale ([docs.stale](../04-programs.md#docs.stale)).

A pin covers the signature's text, which leaves bodies out ([docs.pinned-texts](../04-programs.md#docs.pinned-texts)). A pin on the declaration's whole text would make a doc stale at every edit of its body, while a doc describes what callers see. A pin holds the doc's own hash too. Without it, a doc rewritten after its signature changed couldn't be told from one left behind. A doc without a pin is never stale: it is new, and the next command that writes source pins it. If unpinned docs were flagged, a package checked for the first time would flag every doc, and so would one that gained docs in an editor. No edit made those docs wrong. A doc whose own hash changed is never stale either, because its author changed it.

`check` never writes `docs.lock` ([docs.writing-pins](../04-programs.md#docs.writing-pins)). A command that only reads source shouldn't rewrite a committed file, and a `check` in CI would change the files it checks. An edit that sends a declaration back with the same signature and doc pins that doc again, because sending it back says that the doc still holds. That is W0002's fix. A mark that silences a stale doc would be one more piece of syntax for what a tool can infer, while the fix pins it again in one step. So an agent sees a stale doc in the verdict of the edit that changed the signature, and either edits the doc or sends the declaration back as it is.

Pins could live in each file, as comments, or in one lock per module ([docs.lock-file](../04-programs.md#docs.lock-file)). A doc's history isn't code, and one file per package, beside its manifest, is reviewed as the manifest is. A fetched package's `docs.lock` is never read, because its diagnostics aren't reported. It isn't part of the content hash either, because building doesn't read it.

## Duplicate bodies

Agents often copy a body where they could call the function that holds it, and two copies drift apart when one is fixed and the other isn't. A copy is flagged at the later body, naming the first ([docs.duplicate-bodies](../04-programs.md#docs.duplicate-bodies)), with a fix that calls the first where the two signatures allow it ([docs.duplicate-body-fix](../04-programs.md#docs.duplicate-body-fix)).

Bodies are compared as typed bodies ([docs.same-body](../04-programs.md#docs.same-body)). If canonical texts were compared, renaming a local would hide a copy, and one text that calls different functions in two modules would count as one body. If bodies were compared without their types, `x * x + 1` over `i32` and over `i64` would be a copy that no call can replace. A warning without a way to remove it teaches agents to ignore it. Type parameters are compared by name, because copies keep their type parameters' names. Comparing them by position would need the order of an impl's and a function's own generics fixed in both implementations, for little gain. Near copies, as a clone detector finds them by a distance, are left out. Exact copies come from the typed bodies at no cost, while a distance needs a threshold that each project would tune.

Only bodies of 20 tokens or more count ([docs.body-size](../04-programs.md#docs.body-size)), so `{ x }` never warns. Tests, constants and doc examples aren't compared ([docs.bodies-compared](../04-programs.md#docs.bodies-compared)). No call can stand in for them, so their warning would have no fix, and a test that repeats another with other values isn't a copy. Bodies of the standard library aren't compared either. Its functions are short and generic, so most matches would be coincidences of 20 tokens.

The warning is at the later copy. An error of several places is reported at the later one too, and the first copy is the one the rest of the program keeps. The fix requires the same result type and row, not only the same parameter types. A call of a function that declares `io` or a `raise` that the later doesn't, or that returns another type, wouldn't check, and a fix must leave no diagnostic.

W0302 depends on the program alone, so it is part of conformance. W0002 depends on a file that records the history of the docs, which no conformance test holds ([docs.warnings-in-conformance](../04-programs.md#docs.warnings-in-conformance)).

## Rendered documentation

`stilt doc` writes a package's documentation as HTML ([docs.stilt-doc](../04-programs.md#docs.stilt-doc)). `stilt show` answers a question about one declaration, while a library's reader browses a package, in a browser, without a toolchain. A module's declarations share one page ([docs.module-pages](../04-programs.md#docs.module-pages)), because they are read together, as their file holds them, and an anchor names each one.

A page prints each function's limitable facts beside its signature, so you see what each call may do without opening its body. The toolchain infers the facts, so a doc that restated them in prose would go stale, which `docs.lock` exists to prevent. A page that prints them can't go stale. A module's description is the comment that its file starts with. Rust writes module docs with a comment form of their own, `//!`. In Stilt, the first comment of a file already describes it, and a new form would be syntax for what a tool can infer.

The standard library is documented by the same pages ([docs.std](../04-programs.md#docs.std)). You learn one form for the library and for every package, and the library's facts come from the same inference, natives included, with no table kept beside it. The built-in types have no pages written by hand. Their methods are declared in `std.prelude`, with their docs and examples, so the page of that module shows them as it shows a declared type's.
