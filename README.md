# Monodromy

A computer built from successive path lifting.

Two persistent logarithmic branches drive a third through a fixed pair of
covering maps. Five fixed loops provide memory shifts and conditional winding.
An analytic observation of the returned roots selects the next finite path word.
The actual lifts produce the next state.

The Lean development proves simulation of arbitrary finite Post–Turing machines,
including complete configurations, exact first returns, halting, divergence,
and geometric realization of every finite execution.

## Read

- [Mathematical note](notes/monodromy-note.pdf) · [LaTeX source](notes/monodromy-note.tex)
- [Complete review bundle](notes/monodromy-review.zip), with the pinned Lean project and theorem index
- [Geometry and execution](docs/architecture.md)
- [Source map and theorem chain](docs/structure.md)
- [Current research position](docs/NOW.md)

The note derives the operations from the geometry before constructing the
machine. Its main theorem is native geometric Turing universality.

## Verify

The project uses Lean 4.35.0 and the Mathlib revision pinned in
[lakefile.lean](lakefile.lean). With Lean and Lake installed:

```sh
lake build
lake env lean -DautoImplicit=false -DwarningAsError=true src/Audit.lean
```

The audit checks the transitive axioms of every exported Monodromy declaration.
Only `propext`, `Classical.choice`, and `Quot.sound` are allowed.
It also checks that native execution and compilation definitions retain actual
lifts and avoid source-machine interpreters and proof-side integer successors.

The development specifies exact geometric execution and proves its properties.
The library defines the current execution semantics. The archived four-root
numerical command-line demonstration belongs to the earlier finite model.

The same five loops also compile locally reversible integer two-counter
tables into a globally reversible native return map. Eleven word returns
realize one source transition, preserving complete execution, halting, and
divergence under an explicit completeness condition. The remaining research
task is to construct the reversible universal source encoding.

A direct analytic comparator over three real coordinates preserves the same
programs' complete integer-lattice executions. Its scope and the reversible
construction are recorded in [the current research position](docs/NOW.md).

## Files

`src/Monodromy/` contains the current mathematics; `src/Monodromy.lean` is its
public entry point. `notes/` contains an independently versioned note, its complete
review snapshot, and numbered proof companions. `docs/` contains navigation and
research history. `paper/` preserves the frozen earlier manuscript.

[Monodromy.zip](Monodromy.zip) is a source distribution of the current development,
including its build configuration, documentation, and manuscript sources.
[docs/history.zip](docs/history.zip) preserves the retired implementations,
four-root executor, earlier manuscripts, proof drafts, and audit evidence.
Historical claims and directory names are recorded in [docs/history.md](docs/history.md).

Author: Xiaoyang Liu, University of Waterloo · x98liu@uwaterloo.ca

[AI contributions](AI_CONTRIBUTIONS_STATEMENTS.txt) · [License](LICENSE)
