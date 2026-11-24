# Proof map

Reads the compiled Lean model of [`formal/`](../../formal/) and writes what the site's proof map, `/design/proof-map/`, shows of it, so that page is generated from the proofs and can't drift from them. `just proof-map` builds and runs it, and `just formal` runs it after the model's build.

It is a Lake package of its own that requires the model by path, so it reads the model's build without changing it. Its executable imports the module `Stilt` and writes `target/proof-map/map.json`:

| Part | What it holds |
| --- | --- |
| `decls` | Every declaration written in a file of the model, with its kind, module and line, the declarations its statement and its proof use (read through the ones the elaborator makes, a constructor standing for its type and a projection for its structure), the paragraphs of the [Reference](../../reference/) its doc cites, whether `soundness` reaches it, and for the theorems it reaches, the statement as Lean prints it |
| `accepted`, `promises` | The fields of `Program.Accepted` and `Program.Promises`, each with its statement, and for each promise the lemma that the proof of `soundness` gives it from |
| `chapters` | Each paragraph of the Reference, **in the theorem** when a declaration that `soundness` reaches cites it, **modeled apart** when only others do, **described** when only a module's doc does, and **not modeled** otherwise |
| `modules` | Each module with its doc and how many of its declarations `soundness` reaches |
| `problems` | A citation of no paragraph, or a declaration resting on `sorry` or on an axiom beyond `propext`, `Classical.choice` and `Quot.sound`; any of them fails the run |

| File | Holds |
| --- | --- |
| [`Main.lean`](Main.lean) | The executable: imports the model, gathers the map and writes it |
| [`ProofMap/Graph.lean`](ProofMap/Graph.lean), [`ProofMap/Collect.lean`](ProofMap/Collect.lean), [`ProofMap/Build.lean`](ProofMap/Build.lean) | The written declarations and what each uses, and the axioms each rests on |
| [`ProofMap/Theorem.lean`](ProofMap/Theorem.lean) | The fields of `Accepted` and `Promises`, and the lemma behind each promise |
| [`ProofMap/Reference.lean`](ProofMap/Reference.lean) | The paragraphs of the Reference and the citations of them in docs |
| [`ProofMap/Output.lean`](ProofMap/Output.lean), [`ProofMap/Map.lean`](ProofMap/Map.lean) | The JSON, the statuses and the problems |
| [`tables.py`](tables.py) | The Modules and Theorems tables of [`formal/README.md`](../../formal/README.md), written from `map.json` by `just proof-map`, and checked current by `just formal` |
