# Monodromy

A computational model inspired by monodromy, based on covering spaces and analytic continuation, formally developed in Lean 4.

The model uses covering-space path lifting to realize state transitions, with persistent branch information providing memory.

## The Construction
- **Memory:** Three integer-valued branches of logarithmic coverings.
- **Observation:** A cubic covering provides finite branch information.
- **Operations:** Integer-affine updates, analytic branch selection, and covering-level descent.
- **Execution:** State-dependent paths are lifted through covering spaces, with discrete returns defining computational steps.

Finite programs determine globally real-analytic state-transition maps. On the exact integer lattice, their execution is realized through actual covering-space path lifting.

The descent operation allows finite observations to access successively deeper digits of unbounded memory.

A mathematical explanation is available in [The Computational Structure of Analytic Continuation](docs/structure.md).

## Formally Verified Results

Three main results have been established in Lean 4.

### 1. Turing Universality

Every finite-alphabet, finite-control Turing machine can be simulated from an arbitrary configuration, preserving complete configurations, termination, and divergence.

The simulation is connected to actual covering-space path lifting.

**Lean:** [`Universality.lean`](src/Monodromy/Universality.lean), [`Structure.lean`](src/Monodromy/Structure.lean)

### 2. Exact Computational Characterization

With fixed, effective input/output encodings, the realizable partial functions are exactly the partial recursive functions:

$$
\mathcal C_{\mathrm{Mono}}=\mathcal R_{\mathrm{partial}}.
$$

The equivalence concerns complete execution semantics, including definedness, numerical results, and divergence.

**Lean:** [`Structure.continuation_characterization`](src/Monodromy/Structure.lean)

### 3. Strict Computational Separation

Removing covering-level descent yields a restricted language whose halting problem is decidable, even though its integer-valued states can remain unbounded.

The full language is Turing complete, establishing a strict separation in computational expressivity.

**Lean:** [`ForwardBoundary.lean`](src/Monodromy/ForwardBoundary.lean), [`Structure.descent_strictly_extends`](src/Monodromy/Structure.lean)

## Verification

The project uses Lean 4 and Mathlib.

To build and check the formal development:

```bash
lake build
lake env lean -DautoImplicit=false -DwarningAsError=true src/Audit.lean
```

The audit checks the transitive axiom dependencies of Monodromy declarations against the standard Lean axioms.

## Scope and Related Work

The characterization concerns exact integer-lattice execution with discrete-return semantics and the specified finite program language.

Questions concerning minimal dimension, numerical stability, computational efficiency, and physical realization remain open.

Analytic simulation of Turing machines has established precedents, including work by Koiran and Moore. The present development investigates covering-space execution, a fixed computational interface, and the expressivity boundary induced by descent.

Further reading:

- [Mathematical characterization](docs/structure.md)
- [Current results and verification status](docs/NOW.md)
- [Formal development](src/Monodromy.lean)
- [Research history](docs/history.md)

## Author

**Xiaoyang Liu 刘潇阳**  
Applied Mathematics, University of Waterloo

Developed with AI assistance. See [AI contribution statements](AI_CONTRIBUTIONS_STATEMENTS.txt).

Feedback, mathematical criticism, and references to related work are welcome.
