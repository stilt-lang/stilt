# Documentation

Where a document here describes the language, it describes it exactly as the [Reference](../reference/) states it.

| Folder | Contents |
| --- | --- |
| [`guide/`](guide/) | The guide, which teaches the language and explains its design |
| [`writing.md`](writing.md) | How every page of the documentation is written: the kinds of page, words and sentences, the terms, code examples, and what to delete on sight |
| [`commands.md`](commands.md) | The commands of `stilt` and their options, written from its help |
| [`errors/`](errors/) | The error index: a page for each diagnostic code, with what to do about it, a program that makes the mistake and the same program fixed, and what the compiler prints, generated from the [registry](../reference/errors.toml) and the [snapshots](../tests/diagnostics/) by `cargo run -p stilt-registry` |
| [`design/`](design/) | The design: the [sketch](design/design-sketch.md) of the long-term vision, with its parts on [values with inferred costs](design/values-and-costs.md), [compile-time code](design/compile-time-code.md) and [its sandbox](design/compile-time-sandbox.md); [what you write and what is inferred](design/inferred-facts.md); the [goals and measurements](design/goals.md), the [known limitations](design/known-limitations.md), the [agent syntax](design/agent-syntax.md) and the [compiler architecture](design/compiler-architecture.md), with the [compiler's internals](design/compiler-internals.md) |
