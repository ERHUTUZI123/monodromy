# AGENTS.md — Monodromy Research Protocol

## 1. Mission and scope

Monodromy is an independent fundamental-research project exploring **Topology-Native Computational Learning**: a learning system that constructs, preserves, composes, and improves internal computations through the learned geometry and topology of its execution space.

The long-term ambition is a potentially paradigm-level learning architecture. Do not treat this ambition as an established result, a requirement for every experiment, or a reason to exaggerate findings.

Keep this project independent of **Prometheus** unless the researcher explicitly requests integration. Existing Monodromy experiments, including negative results, are part of the scientific record.

The first-priority question is:

> **Can topology-preserving geometric adaptation causally reduce the cost of acquiring genuinely new computational capabilities?**

Secondary questions are (B) learned topological/structural growth and (C) expressivity beyond finite reversible permutations. Prioritize A until evidence justifies shifting focus.

## 2. Conceptual architecture

The working hypothesis has five components:

1. **Geometric substrate:** a learnable relation, e.g. `F_theta(z, u) = 0`, defining a branched state space and its safe control domain.
2. **Path generator:** a controller producing candidate paths from inputs, goals, and execution state.
3. **Monodromy executor:** actual continuation/path lifting of a state along a path, with numerical work accounted for.
4. **Computational memory:** reusable, executable operations with conditions, bindings, and provenance.
5. **Structural growth:** task-driven proposals that may expand states, branching, loops, or operations, subject to explicit protection checks.

These are research hypotheses and design roles, not permission to invent unneeded modules before there is a testable mechanism.

## 3. Mathematical correctness contract

For a fixed parameter setting, state the assumptions under which a finite covering exists:

`p_theta: E_theta -> X_theta`, with `X_theta` excluding critical values.

For based loops `gamma` in `X_theta`, path lifting induces a monodromy representation:

`rho_theta: pi_1(X_theta, u_0) -> S_D`.

Before claiming topological invariance, explicitly specify:

- the allowed parameter deformation and the singularity-avoidance conditions;
- the basepoint and identification of fibers/sheets across parameter values;
- the path homotopy class, path orientation, and permutation-composition convention;
- what is held fixed (sheet count, covering type, operation interface) and what may change.

A change of sheet labels can conjugate a represented permutation. Do not claim literal equality when only equivalence under a valid identification is established.

Within a fixed covering topology, continuous safe deformation does not automatically enlarge the algebraic set of realizable monodromy operations. It may alter numerical conditioning, geometric accessibility, and the **cost of discovering or executing** operations. Test those claims separately.

Distinguish **operation semantics**, **task-level behavior**, **acquisition efficiency**, and **total resource cost**. Preserving one does not prove preservation or improvement of the others.

## 4. Execution and learning integrity

- A claimed monodromy computation must actually execute a continuous path and track the resulting state/sheet. A hard-coded permutation table can be a baseline or diagnostic, but cannot substitute for the claimed executor.
- An operation described as **learned** must be obtained through a specified learning or search process using permitted feedback. Do not feed the target permutation, correct path, future task labels, or oracle solutions into the learner unless explicitly identified as supervision.
- Record initial conditions, evolving state, candidate paths, path-lifting outcomes, task feedback, and how an operation entered memory.
- Clearly distinguish within-class geometric adaptation from discrete discovery of new loop classes and from structural changes to the covering itself.
- Do not imply a gradient can directly move between discrete homotopy or monodromy classes. State and measure the discrete proposal/search mechanism.
- When growing the substrate, test preservation of old executable operations and separately test preservation of old task behavior, including controller/readout/binding dependencies.

## 5. Primary scientific test: productive geometric plasticity

A positive result must show a **causal** improvement in future acquisition under fair resource accounting. Prefer controlled experiments that compare:

1. learned safe geometric adaptation;
2. frozen geometry with the same operation interface and learning/search budget;
3. non-topological or ordinary constraint-based adaptation with comparable capacity;
4. appropriate random, sham, or ablated geometric changes;
5. discrete path search / direct permutation / state-machine alternatives where applicable.

Use matched task information, compute budgets, candidate evaluations, and hyperparameter-search effort. If exact matching is impossible, report the differences rather than claiming strict parity.

Measure the outcome that the hypothesis actually predicts: task-feedback samples, valid candidates evaluated, discovery success, wall-clock time, numerical continuation work, parameter/storage use, and old-operation/task retention. Include unsuccessful runs and seeds. Separate *finding* an operation from *executing* it after discovery.

For any claimed advantage, ask whether it survives removal of the relevant topology-specific mechanism. A gain from generic search, ordinary weight sharing, additional capacity, or privileged information is not evidence for productive topological plasticity.

## 6. Historical evidence and non-negotiable baselines

In the earlier N8 six-stage comparison, Monodromy used **5,314 parameters** and an ordinary-constraint variant used **5,310**; both preserved the six tested capabilities. Under a fixed behavior-protection mechanism, removing the continuous monodromy component even produced byte-identical neural weights in a controlled comparison.

Interpret this as **no demonstrated parameter-efficiency advantage** for monodromy in that experiment. Positive historical results include executable path-lifted permutations, safe deformation checks, new operations from exploration, and some growth constructions; they do not yet prove productive adaptation.

Never conceal, overwrite, or silently reframe negative results. Strong non-topological baselines must remain competitive and must be allowed to succeed.

## 7. Experimental and engineering workflow

For each substantive change:

1. **Inspect** the existing code, experiments, tests, and recorded evidence before editing. Do not assume a directory layout, language, dependency, or framework not present in the repository.
2. **State the testable claim** and the strongest ordinary explanation that could produce the same observations.
3. **Specify the intervention**: manipulated variable, fixed conditions, controls, evaluation data, metrics, seeds, and total cost budget.
4. **Implement the smallest falsifiable experiment**. Prefer isolated, auditable changes over large architectural rewrites.
5. **Validate mathematics and execution** with analytic cases, invariant checks, orientation/composition tests, numerical convergence checks, and failure cases when relevant.
6. **Run controls and report all results**, including invalid paths, failures, timeout/compute limits, and unexpected outcomes.
7. **Record reproducibility**: exact command, code revision, configuration, seed, hardware if material, environment/dependencies, raw outputs, and a concise interpretation.
8. **Recommend the next discriminating experiment** based on evidence, without asserting that the long-term architecture has been established.

Use the repository's established conventions. Add new dependencies or major abstractions only when they have a demonstrated role. Avoid unrelated refactors. Keep experiments reproducible and make stochastic behavior seedable.

For nontrivial implementations, provide a short summary of changed files, tests actually executed, measured results, open uncertainties, and remaining failure modes. Never claim a test passed unless it was run.

## 8. Cost accounting and reporting

Count, where relevant:

- model parameters and trainable parameters;
- optimization steps and task-feedback queries;
- candidate paths proposed, rejected, and executed;
- path length/continuation steps, solver tolerances, retries, and failures;
- structural proposals and validation/protection work;
- runtime, peak memory, storage, and precomputation;
- evaluation and hyperparameter-selection overhead.

Do not present a precomputed operation or an external oracle as free computation. Where exact hardware-level comparison is unavailable, report both hardware-independent work measures and available measured runtime.

Label each scientific statement as appropriate: **proved**, **experimentally observed**, **hypothesized**, or **unknown**. Proofs require assumptions and checkable derivations; empirical claims require reproducible evidence. Explicitly disclose when a result is diagnostic, uses privileged information, or was obtained with post-hoc selection.

## 9. Scientific decision rule

Proceed toward a broader architecture only when a concrete mechanism earns that expansion. If safe geometry changes preserve old operations but do not improve acquisition, report the null result and reconsider the mechanism. If simpler non-topological methods achieve the same outcome at lower full cost, say so explicitly.

The research goal remains ambitious; the evidence standard remains adversarial. The agent's job is to **increase the density of rigorous tests**, actively seek counterexamples, and help distinguish a new computational learning principle from a more elaborate representation of an existing discrete algorithm.
