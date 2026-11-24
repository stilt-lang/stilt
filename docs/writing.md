# How Stilt's documentation is written

Every page of Stilt's documentation follows these rules: the tour, the guide, the Reference and its rationale, the error index, the standard library's doc comments, the README files and the website. They come from the Diátaxis framework, Google's developer documentation style guide, GOV.UK's writing guidelines, and the way the Rust book, the Elm guide, A Tour of Go and the Go specification are written.

## For every page

**Know what kind of page you are writing.** A page is one of four kinds, and doesn't drift into another:

| Kind | Pages | It |
| --- | --- | --- |
| Tutorial | The tour | Teaches by building one program, step by step |
| Guide | The guide's chapters, the cookbook, the pages for programmers of other languages | Shows how to use a part of the language |
| Reference | The Reference, the error index, the library's docs | States what is true, exactly and completely |
| Explanation | The rationale, [Why Stilt is this way](guide/10-design.md), the design documents | Says why, and what else was considered |

When a guide chapter starts listing every rule, link to the Reference instead. When the Reference starts giving reasons, move them to the rationale.

**Put the point first.** The first sentence of a page or section says what it gives the reader. Don't restate the heading, and don't announce what's coming ("This chapter covers…").

**Be specific.** If a sentence could appear in any language's documentation, it says nothing yet. Name the construct, the value, the error code or the output.

**Say what is true now.** No "currently", "new", "soon", "no longer" or "for now". [Known limitations](design/known-limitations.md) is the one page about what isn't done.

**Keep a calm tone.** No exclamation marks, no jokes, no cheering the reader on. Program output may say what it says.

## Words and sentences

- **Write to "you".** Never "the user", and never "we" or "let's": not even in the tour.
- **Present tense, active voice.** "The compiler rejects the program", not "The program will be rejected by the compiler". Passive is fine when nobody acts: "The file is read once".
- **One idea per sentence.** Split a sentence of more than 25 words. Keep paragraphs to five sentences or fewer.
- **Condition first:** "If the list may be empty, use `get`", not "Use `get` if the list may be empty".
- **Verbs, not nouns made from verbs:** "allocates a buffer", not "performs the allocation of a buffer".
- **Plain words:** use, not utilize or leverage; lets you, not enables you to; to, not in order to; can, not is able to; because, not since; for example, not e.g.; that is, not i.e.
- **No words that judge for the reader:** simply, just, easy, easily, obviously, of course, note that, please.
- **Must, can and can't** have fixed meanings: must is required, can is allowed, can't is refused. Avoid "should" and "may" in the guide; the Reference uses "may" for permission only.
- **One word for each idea.** Once a term is defined, use it every time. A synonym makes the reader look for a second thing.
- **Define a term where it first appears,** in bold, and tie it to the code on the page.
- **Code font for everything you type:** keywords, types, functions, files, commands and values. Never use code as a verb or a possessive: write "the payload of an `Option`", not "the `Option`'s payload".

## Terms

These are the words the documentation uses, and the ones it doesn't:

| Use | Not | Meaning |
| --- | --- | --- |
| fact | property, annotation | What the compiler infers about a function: `panic`, `overflow`, `alloc`, `div`, `copy` and the others |
| limit | constraint, restriction | A `without` clause, which the checker holds a body to |
| effect row, row | effect list, signature effects | The `/ io` or `/ {io, raise<E>}` after a signature |
| raise | throw | Report an error that the caller handles |
| panic | crash, abort | Stop the program, for a bug; nothing catches it |
| tier | level, edition | `core`, `advanced`, `meta` or `systems` |
| record, variant type | struct, enum | The two kinds of declared type |
| `inout` parameter | reference, mutable borrow | A parameter that changes the caller's place |
| place | lvalue | Something you can assign to or pass `inout` |
| property | property test, prop test | A `prop:` line, checked on generated values |
| example | doctest | An `ex:` line |
| the reference interpreter | the oracle | `stilt-ref` |

## Page structure

- **Headings in sentence case.** A heading for a task starts with a verb ("Read a file"). A heading for a concept is a noun phrase ("Effect rows"). No questions, no "Introduction" or "Overview", no links.
- **Text under every heading,** and no skipped levels.
- **Lists:** numbered for steps, bullets for unordered items, a table for pairs. Introduce each list with a full sentence. Never a list of one.
- **Link text names its target:** "see [Parameter modes]", never "see [here]".
- **No closing summaries.** End when the content ends.

## Code examples

- **Introduce each example with a sentence** that says what to look at, ending with a colon.
- **Every example is a whole program that the guide's tests run** (`just guide`), unless it is marked `fragment`. Its output is shown exactly, in an `output` block right after it, and comes from what the Reference says, never from running an implementation. The word after `stilt` in a block's info string says what the program must do, as the runner's [`examples` module](../tools/runner/src/examples.rs) documents:

  | Info string | The program |
  | --- | --- |
  | ` ```stilt ` | has no error or warning |
  | ` ```stilt E0404:5 ` | has exactly this diagnostic, on line 5 of the block |
  | ` ```stilt pass:3 fail:7 ` | has a test on line 3 that passes, and one on line 7 that fails |
  | ` ```stilt exit:1 ` | exits with status 1, printing what the `output` and `stderr` blocks after it hold |
  | ` ```stilt fragment ` | shows a form rather than a program, and isn't checked |

- **Explain after the code,** naming the lines or names that matter. Don't retell the whole example.
- **Keep it as small as the point allows,** with real names. The guide's examples come from the arena of [the tour](guide/01-tour.md): creatures, elements, moves, hits and battles. Use those names, so every chapter reads as part of one story.
- **The arena's names are fixed.** Reuse these before inventing new ones, and keep any new one in the same world:

  ```stilt fragment
  type Element = | Fire | Water | Plant
  type Creature = { name: str, element: Element, hp: i64, attack: i64 }
  type Move = { name: str, element: Element, power: i64 }
  ```

  The creatures are Embercat (`Fire`, 30 HP, attack 8), Mossling (`Plant`, 34 HP, attack 6) and Tidepup (`Water`, 32 HP, attack 7). The moves are Flame Pounce (`Fire`, 40), Root Snare (`Plant`, 30) and Bubble Jet (`Water`, 35). The tour's functions are `effectiveness`, `hit` and `remaining`. Not every example has to be about the arena: a rule about integers can use plain numbers.
- **Change one thing between two examples,** and say what changed.
- **Show the compiler's message exactly** when an example is wrong on purpose.

## For each kind of page

**The tour** names what you'll build in its first sentence, adds one thing per step, shows each step's output, and makes a mistake on purpose now and then to show what the compiler says. It gives a reason in a sentence and links to the guide for the rest.

**A guide chapter** opens with a small example, then names what it shows. It explains how to do things, with the rules a reader needs to write correct code, and links each rule to the Reference paragraph that states it in full. It doesn't restate edge cases, algorithms or exact limits: those are the Reference's.

**A Reference paragraph** describes and nothing else, with fixed patterns: "A **block** is…" for a definition; "… is E0402" for a rejected program; "may" for permission. Every paragraph keeps its ID and its `Tests:` line. Reasons go to the rationale.

**A rationale section** answers one "why": what was chosen, what else was considered, and what each costs, with a program that shows the difference.

**An error page** says what went wrong in the reader's terms, shows the smallest program that makes the mistake and the same program fixed, and links to the rule. The registry, [`errors.toml`](../reference/errors.toml), writes it.

**A doc comment in the library** is one sentence first. A function that gives a value says what it gives: "The contents of the file at `path`.", or "Whether a file exists at `path`." for a `bool`. A function that does something starts with a verb: "Appends `text` to the file at `path`." Its `ex:` lines check a result rather than print it.

**The front page** says what Stilt is in words anyone can read, shows one short program with what the compiler says about it, and links to the tour.

## Delete on sight

- Inflated words: delve, leverage, robust, seamless, powerful, crucial, key (as an adjective), enhance, empower, facilitate, showcase, landscape.
- "Serves as", "acts as", "boasts", "features" where "is" or "has" works.
- "Not X but Y", "not just X", "rather than X": say Y.
- Lists of three adjectives that show nothing.
- More than one dash in a paragraph. Use a full stop or a colon.
- Trailing "-ing" phrases: ", ensuring safety", ", making it easy to…".
- Throat-clearing: "It's worth noting that", "It's important to understand", "Here's the thing".
- A question answered by the next sentence.
- Fragments for effect: "Fast. Safe. Simple."
- A name for an idea that nobody else uses. Use the Reference's term.
- "Many developers find", "it is widely known".
- "Etc." and "and so on". Write "such as" before the list.
- A paragraph that names no construct, value or output.
