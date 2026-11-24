# Governance

This document says who decides what in Stilt, how, and how that changes.

## Roles

- **The benevolent dictator** decides what the language is. Today that is Eyusd ([@eyusd](https://github.com/eyusd)), who designed Stilt and decides every RFC. The dictator's decisions rest on the language's design philosophy, which the [guide](docs/guide/10-design.md) and the [design documents](docs/design/) state, and on plain examples: a feature is judged by the program a user would write, what it does, and what goes wrong without it.
- **Maintainers** review and merge changes in the areas they are responsible for. They decide everything that is not a change to the language.
- **Contributors** are everyone else who sends an issue, a pull request or a review. [CONTRIBUTING.md](CONTRIBUTING.md) says how.

## Areas

Each area has at least one maintainer, listed in [`.github/CODEOWNERS`](.github/CODEOWNERS):

| Area | Paths |
| --- | --- |
| The Reference | `reference/` |
| The conformance suite | `conformance/` |
| The reference interpreter | `interpreter/` |
| The compiler | `compiler/` |
| The standard library | `std/` |
| Tools and tests | `tools/`, `tests/`, `bench/` |
| The Lean model | `formal/` |
| Editors | `editors/` |
| Documentation and examples | `docs/`, `examples/` |
| Process | `.github/`, `justfile`, the files at the root |

## How decisions are made

- **Ordinary changes**, such as a fix, a refactoring, a test, a better message or a document, merge when one maintainer of the area approves and CI passes. A maintainer's own pull request is approved by another maintainer, or by the dictator while the project has only one.
- **Changes to the language** go through an [RFC](https://github.com/stilt-lang/stilt-rfcs). The RFC process, its states and its ten-day final comment period are written in that repository. The dictator decides: accepts, asks for changes, or declines, and gives the reasons in writing on the RFC. A change small enough to be a clarification of a paragraph of the Reference, with no change to what any program does, is an ordinary change.
- **Changes to the Reference** that an RFC accepted are made first in `reference/`, as [CONTRIBUTING.md](CONTRIBUTING.md) says, and implementations follow.
- **Releases** are cut by the dictator, following [RELEASING.md](RELEASING.md).
- **Security reports** are handled under [SECURITY.md](SECURITY.md).

All decisions and their reasons are written where anyone can read them: in the pull request, the RFC or the issue.

## Becoming a maintainer

A contributor who has, over several months, sent changes in an area that were merged with little rework, reviewed other people's changes well, and been kind in doing both, can be proposed by any maintainer or by themselves, by opening an issue in this repository. The dictator decides, after a week in which maintainers may object. A maintainer is added to the area's entry in `.github/CODEOWNERS`.

A maintainer who has done nothing in the project for twelve months is asked whether they want to continue; if not, or if there is no answer after a month, they become an emeritus maintainer, are removed from `.github/CODEOWNERS` and are thanked in the history. They can return by asking.

## Appeals

A decision of a maintainer can be appealed to the dictator by a comment on the pull request or issue that asks for it and gives the argument. A decision of the dictator on an RFC is reconsidered once, when someone brings an argument or an example that the discussion did not weigh; the dictator answers in writing. Decisions about conduct are appealed as the Code of Conduct says.

## If the dictator is unavailable

If the dictator is out of contact for ninety days without having named a replacement, the maintainers choose from among themselves a steward who decides until the dictator returns or the maintainers adopt another model under the next section.

## When this changes

This model is for a project that has one designer and a small number of maintainers. It will be revisited when the project has five regular maintainers, that is, five people who have each merged or reviewed changes in most months of the last six. The revisit is an RFC about the next model, for example a core team that decides by consensus with the dictator's role reduced to a casting vote, which the dictator decides like any other RFC.

Until then, this document changes by a pull request that the dictator approves after ten days open for comments.
