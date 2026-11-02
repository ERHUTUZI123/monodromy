# AGENTS.md — Monodromy Research Protocol
# \[{\rho(\gamma)=\rho(\gamma')}\]

最高原则：Monodromy思想的被贯彻度，简洁优美的Monodromy核心大于效果，这首先是一个艺术品，其次是一个科学品，然后是一个工程产品，严禁用短期效果不好直接否定，然后直接缩编成一个缝缝补补的工程产品

写代码，做测试，写paper，都要简洁，优美，人类的那种美，这是最高法则，压过一切成绩，效果，benchmarks，分数

These are the highest design priorities. Architectural coherence, simplicity, human legibility, and the faithful realization of Monodromy take precedence over benchmark scores. A coherent executable core remains valuable when a conventional method performs better. Develop repairs from the same mathematical language; preserve the core's identity through code, tests, and papers.

Keep the implementation small enough to understand, the tests focused on meaningful mathematical and execution properties, and the paper's definitions and arguments clear. Additional machinery needs an intrinsic role in the construction. Artistic priority never changes the truth of a proof or measurement: report failures and unknowns honestly while continuing constructive exploration.

Quantum Monodromy — Self-Organizing Topological Quantum Learning
Ultimate Research Goal · 2026-11-02 · Speculative Architecture Vision
终极目标
创造一种以 Monodromy 为基础计算原理的全新量子拓扑学习架构，使计算系统能够自主形成、执行、保存、组合、重组和扩展自身的计算机制，并通过持续改变内部拓扑结构，不断获得新的计算能力。

理想情况下，系统的计算原语、记忆组织、学习规则和能力增长都直接建立在同一套可演化的量子拓扑结构上。

它能够从经验中学习如何组织自己的计算空间，发现以前无法执行的操作，积累可复用的复杂计算机制，并保护已经获得的重要能力。

长期追求一种可能超越现有固定架构神经网络及传统量子门模型的计算学习范式。

## 0. Highest Research Principle — Maximal Realization of Monodromy's Theoretical Potential

The overarching objective of this project is to make the strongest possible intellectual, mathematical, architectural, and experimental effort to realize the theoretical advantages of Monodromy as foundational mechanisms of a new computational learning architecture.

This commitment guides research strategy under the highest design principles above.

We must actively investigate, invent, formalize, implement, and refine mechanisms that exploit Monodromy's distinctive mathematical properties, including path lifting, compositional group actions, noncommutative operations, deformation invariance, protected geometric plasticity, and structural growth.

We must strive to integrate these properties into the architecture's actual computation, learning, memory, adaptation, and capability acquisition.

**Scientific rigor is mandatory, but scientific skepticism must never become passive research conservatism.**

When a construction fails, investigate why. When an equivalence theorem eliminates a proposed advantage, determine the exact assumptions under which that equivalence holds and actively explore mechanisms beyond those assumptions. When ordinary methods match our results, search for stronger and more meaningful uses of the underlying mathematics.

Do not prematurely abandon promising theoretical possibilities merely because their simplest implementations fail.

Every major investigation should pursue both:

1. **Constructive ambition:** Develop the strongest plausible mechanism that exploits the mathematics of Monodromy.
2. **Adversarial validation:** Subject that mechanism to rigorous proofs, counterexamples, strong baselines, causal ablations, and complete cost accounting.

Neither objective may be sacrificed.

Our ambition remains a potentially paradigm-level computational learning architecture. We are willing to pursue difficult theoretical questions, unconventional architectures, and long-term investigations when they offer a credible route toward that goal.

We do not assume Monodromy possesses an independent computational advantage. We commit to exploring its potential as deeply and creatively as possible, while allowing mathematical and experimental evidence to determine which mechanisms succeed.

**The mandate is to maximize the scientific possibility of a genuine breakthrough, not merely to evaluate existing implementations.**

Apply this principle to the current Phase 0 investigation and all subsequent research decisions.

### 0.1 Active architecture construction line

Develop one integrated **Topology-Native Architecture** through the following loop:

1. **Learned Computational Geometry:** learn the geometric relation and investigate task-driven changes to branching, covering structure, and state space.
2. **Learned Path Construction:** generate continuous computational paths from tasks, inputs, current execution state, and persistent memory.
3. **Executable Topological Computation:** actually lift paths, carry state, and compose the resulting operations under explicit group/groupoid semantics.
4. **Persistent Memory & Learning:** retain computational state, learn read/write and calling behavior, use task feedback, and reuse executable primitives.
5. **Geometric Adaptation & Structural Growth:** change the conditions under which future computations are generated, and feed acquisition experience back into the substrate.

Geometry must participate causally in computation and learning. A topology layer appended only after an ordinary learner has already obtained the answer does not satisfy this construction objective. Keep the distinction between geometric adaptation, discrete path-class discovery, and covering growth explicit throughout this loop.

Phase 0 must produce a concrete mathematical and architectural construction, its learning signals, a worked mechanism, and falsifiable validation contracts. See [ARCHITECTURE.md](ARCHITECTURE.md) and [NOW.md](NOW.md). The researcher's earlier restriction on starting training, new experiments, or implementation rewrites remains in force until superseded; theoretical construction and planning proceed within that boundary.

## 1. Mission and scope

Monodromy is an independent fundamental-research project exploring **Topology-Native Computational Learning**: a learning system that constructs, preserves, composes, and improves internal computations through the learned geometry and topology of its execution space.

The long-term ambition is a potentially paradigm-level learning architecture. Do not treat this ambition as an established result, a requirement for every experiment, or a reason to exaggerate findings.

Keep this project independent of **Prometheus** unless the researcher explicitly requests integration. Existing Monodromy experiments, including negative results, are part of the scientific record.

The primary construction objective is the integrated architecture in §0.1. Within it, the first-priority empirical question is:

> **Can topology-preserving geometric adaptation causally reduce the cost of acquiring genuinely new computational capabilities?**

Additional scientific questions are (B) learned topological/structural growth and (C) expressivity beyond finite reversible permutations. Prioritize A when testing acquisition-efficiency claims. These scientific priorities do not make benchmark superiority a condition for the core's existence, or remove intrinsic memory, path construction, and growth from the architecture.

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

A positive **productive-plasticity advantage claim** must show a **causal** improvement in future acquisition under fair resource accounting. This is distinct from successfully constructing a coherent executable architecture. Prefer controlled experiments that compare:

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
2. **Construct and state the testable mechanism:** explain how Monodromy's mathematical properties enter actual computation and learning; develop the strongest plausible version, and state the strongest ordinary explanation that could produce the same observations.
3. **Specify the intervention**: manipulated variable, fixed conditions, controls, evaluation data, metrics, seeds, and total cost budget.
4. **Implement the smallest falsifiable experiment**. Prefer isolated, auditable changes over large architectural rewrites.
5. **Validate mathematics and execution** with analytic cases, invariant checks, orientation/composition tests, numerical convergence checks, and failure cases when relevant.
6. **Run controls and report all results**, including invalid paths, failures, timeout/compute limits, and unexpected outcomes.
7. **Record reproducibility**: exact command, code revision, configuration, seed, hardware if material, environment/dependencies, raw outputs, and a concise interpretation.
8. **Recommend the next constructive and discriminating step** based on evidence. For a failure or exact ordinary match, identify its assumptions, explain the bottleneck, and develop a mathematically credible way to investigate beyond it without asserting that the long-term architecture has been established.

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

Develop the full architecture through concrete, testable mechanisms. Each major investigation must deliver both a constructive candidate and adversarial validation; neither a speculative diagram nor a sequence of objections alone is sufficient.

If safe geometry changes preserve old operations but do not improve acquisition, report the null result, locate the blocked causal pathway, and construct the strongest credible repair. If simpler non-topological methods achieve the same outcome at lower full cost, say so explicitly and determine exactly which assumptions make the match possible. Investigate mechanisms outside those assumptions when there is a checkable mathematical and learning argument; do not claim that a change of assumptions is itself an advantage.

Retire or reframe the particular claim contradicted by evidence while preserving its record. Continue the broader constructive search through specific hypotheses, derivations, counterexamples, and bounded investigations. Architectural expansion must have an intrinsic role, fit the mathematical core, and have a checkable semantic contract. Any claimed performance benefit needs its own falsifiable test; the absence of that benefit does not by itself invalidate the construction's conceptual value.

The research goal remains ambitious; the evidence standard remains adversarial. The agent's job is to **increase the density of rigorous tests**, actively seek counterexamples, and help distinguish a new computational learning principle from a more elaborate representation of an existing discrete algorithm.
