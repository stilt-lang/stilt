# Rationale: Programs with errors

A program under work has mistakes most of the time, and its diagnostics are what a person or an agent reads to fix them. Two goals shape this chapter. One mistake gives one diagnostic, so the list of diagnostics is the list of things to fix. Every implementation gives the same list, so conformance tests can compare it exactly.

## Root causes

An implementation reports only the diagnostics that no other diagnostic caused ([errors.root-causes](../18-errors.md#errors.root-causes)). Most compilers, rustc, GCC and Clang among them, suppress cascades each in their own way. Leaving that to each implementation is rejected: exact matching is fair only if every implementation suppresses the same diagnostics. So the rules that decide which ones are reported are part of the language.

## Syntax errors

Which errors are syntax errors is fixed ([errors.syntax-errors](../18-errors.md#errors.syntax-errors)), because a syntax error hides everything else in its part. A primitive type name used as a name is left to name resolution, so the declaration around it still parses and is checked.

## Reading a file in parts

A compiler can stop at the first syntax error of a file and check nothing else, as Python does. That is rejected: one typo would hide every other mistake of the program, and a person or an agent fixing several mistakes would see them one at a time. So a file with a syntax error is read a part at a time, a part for each declaration ([errors.parts](../18-errors.md#errors.parts)). Each part reports its first syntax error ([errors.part-reports](../18-errors.md#errors.part-reports)), and the rest of the program is checked as usual.

Resuming only where the brackets balance is rejected: a `}` left out keeps every bracket after it open, so the rest of the file would be one part. People and `stilt fmt` begin declarations at a line that starts with a declaration's word in its first column, and inside a body nothing starts there. So reading resumes at such a line ([errors.resuming](../18-errors.md#errors.resuming)), even inside a bracket that the broken part leaves open, and a `}` left out costs one diagnostic. A doc example that doesn't parse is reported, but breaks nothing ([errors.breaks](../18-errors.md#errors.breaks)), because its function is still whole.

In a part with a syntax error, nothing else is reported ([errors.part-reports](../18-errors.md#errors.part-reports)). The type errors of a declaration that doesn't parse are mostly the syntax error seen again.

## What a part that breaks declares

A part that breaks still declares what it begins ([errors.broken-parts](../18-errors.md#errors.broken-parts)), so the rest of the program can use it without a diagnostic for each use. A function whose body breaks keeps the signature written before it, and its callers are checked against that signature. Only a whole signature counts, so a function never gets a type that its author didn't write. A trait or an impl that breaks inside its block keeps the members that parse ([errors.broken-blocks](../18-errors.md#errors.broken-blocks)), so one broken method doesn't make every call of the others an error.

A function written `extern` that breaks is declared as a function with an error, never as a foreign one. The part that declares it may well have had a body, and requiring `unsafe` at its calls would turn one mistake into many.

## The error type

A name or an expression with an error gets the error type ([errors.error-type](../18-errors.md#errors.error-type)), which fits everywhere and causes nothing. Compilers such as rustc use an error type internally to stop cascades. Stilt makes it part of the language, so every implementation stops the same cascades. A `try` around it, a `catch` of it and a match on it are all accepted ([errors.error-type-raises](../18-errors.md#errors.error-type-raises)). A binding that can't be named as written gets it too ([errors.primitive-type-bindings](../18-errors.md#errors.primitive-type-bindings)), so its declaration is the only diagnostic.

## Unknown names

A body reports each unknown name once ([errors.unknown-names](../18-errors.md#errors.unknown-names)). Reporting every place where it is used is rejected: a misspelled name used three times is one mistake, and three diagnostics for it hide which other mistakes there are. Outside bodies every place is reported. Each signature or declaration is read on its own, and a name in one is a mistake of that declaration.

## Bodies and phases

A body is checked in phases ([errors.phases](../18-errors.md#errors.phases)), and a phase runs only when the earlier ones found nothing in that body. Analyses such as exhaustiveness and exclusivity rely on types, so after a type error their results would mostly be consequences of it. Warnings about code that doesn't check yet are noise. The analyses of phase 2 don't depend on one another, so they all run and all their errors are reported.

The registry gives each code its phase ([errors.registry-phases](../18-errors.md#errors.registry-phases)). Placing codes by the prose of this chapter alone is rejected. The prose names areas, not codes, so a new code would have to be placed by reading it, while a phase in the registry is checked mechanically.

Errors that the form of the code decides are in phase 1 ([errors.phase-by-form](../18-errors.md#errors.phase-by-form)), because they are known before any type is. Assigning to what can't be modified belongs with modes and exclusivity. An undecided type is reported last ([errors.undecided-types-last](../18-errors.md#errors.undecided-types-last)), because another error in the body, such as a name that doesn't resolve, often leaves a type undecided.

A warning about a comment is about the comment alone, so it is reported whatever the code around it does ([errors.warnings-with-errors](../18-errors.md#errors.warnings-with-errors)).

## Where diagnostics are reported

An error that involves several places is reported at the last of them ([errors.several-places](../18-errors.md#errors.several-places)), in an order that depends on the paths and positions alone. So every implementation picks the same place. The last is chosen so that the earlier declaration is the one that the rest of the program sees, as a reader who meets the first declaration first expects.

## Running a program with errors

A program with errors still runs, and only the code with errors panics ([errors.running](../18-errors.md#errors.running)). So a person or an agent fixing one function sees the rest of the program run. The rationale of [Programs, modules and packages](04-programs.md#programs-with-errors) explains that choice.
