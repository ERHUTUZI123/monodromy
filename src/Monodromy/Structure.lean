module

public import Monodromy.NativeIO
public import Monodromy.ForwardBoundary

/-!
# The computational class of native continuation

Finite words of the five geometric loops, with internal finite-root routing,
realize exactly the partial recursive functions under one fixed numeric
interface. Removing the two zero-conditional loops leaves a finite stopping
quotient and strictly reduces this class.
-/

@[expose] public section

namespace Monodromy.Structure

open CoupledContinuation NativeInterface

/-- The fixed numeric graph is read directly from actual native execution. -/
def Computes {degree : ℕ} [NeZero degree] (native : Program degree)
    (function : ℕ → Part ℕ) : Prop :=
  ∀ input value, value ∈ function input ↔ ∃ labels : Labels,
    Labels.prepare labels ∈ native.eval (Labels.prepare (inputLabels input)) ∧
      outputLabels labels = value

/-- Positive cover degrees are indexed by their predecessor. -/
def Realizable (function : ℕ → Part ℕ) : Prop :=
  ∃ degree : ℕ, ∃ native : Program (degree + 1), Computes native function

/-- The same interface defines the sublanguage with both conditional loops removed. -/
def ProbeFreeRealizable (function : ℕ → Part ℕ) : Prop :=
  ∃ degree : ℕ, ∃ native : Program (degree + 1), native.ProbeFree ∧ Computes native function

theorem computes_iff {degree : ℕ} [NeZero degree]
    (native : Program degree) (function : ℕ → Part ℕ) :
    Computes native function ↔
      ∀ input, outputLabels <$> native.evalInt (inputLabels input) = function input := by
  constructor
  · intro correct input
    apply Part.ext
    intro value
    rw [Part.map_eq_map, Part.mem_map_iff]
    have meaning := correct input value
    simp_rw [NativeInterface.prepared_result_iff] at meaning
    exact meaning.symm
  · intro correct input value
    rw [← correct input, Part.map_eq_map, Part.mem_map_iff]
    simp_rw [NativeInterface.prepared_result_iff]

theorem computes_dom {degree : ℕ} [NeZero degree] {native : Program degree}
    {function : ℕ → Part ℕ} (correct : Computes native function) (input : ℕ) :
    (native.eval (Labels.prepare (inputLabels input))).Dom ↔ (function input).Dom := by
  rw [Program.eval_prepareInt, ← (computes_iff native function).mp correct input]
  rfl

theorem computes_divergence {degree : ℕ} [NeZero degree] {native : Program degree}
    {function : ℕ → Part ℕ} (correct : Computes native function) (input : ℕ) :
    ¬ (native.eval (Labels.prepare (inputLabels input))).Dom ↔ ¬ (function input).Dom :=
  not_congr (computes_dom correct input)

theorem realizable_of_computes {degree : ℕ} [NeZero degree]
    {function : ℕ → Part ℕ} (native : Program degree) (correct : Computes native function) :
    Realizable function := by
  obtain ⟨predecessor, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne degree)
  exact ⟨predecessor, native, correct⟩

/-- The finite syntax and fixed effective I/O give the partial-recursive upper bound. -/
theorem partrec_of_realizable {function : ℕ → Part ℕ}
    (realized : Realizable function) : Partrec function := by
  obtain ⟨degree, native, correct⟩ := realized
  exact (NativeInterface.effective_execution native).of_eq
    ((computes_iff native function).mp correct)

/-- The actual Turing-to-counter-to-continuation compiler gives the matching lower bound. -/
theorem realizable_of_partrec {function : ℕ → Part ℕ}
    (effective : Partrec function) : Realizable function := by
  obtain ⟨source, correct⟩ := NativeInterface.every_partrec_graph effective
  exact realizable_of_computes (NativeInterface.program source) correct

/-- Exact characterization under fixed input/output maps and genuine native execution. -/
theorem continuation_characterization (function : ℕ → Part ℕ) :
    Realizable function ↔ Partrec function :=
  ⟨partrec_of_realizable, realizable_of_partrec⟩

theorem realizable_of_probeFree {function : ℕ → Part ℕ}
    (realized : ProbeFreeRealizable function) : Realizable function := by
  obtain ⟨degree, native, _, correct⟩ := realized
  exact ⟨degree, native, correct⟩

/-- Finite stopping observations remain decidable after the same fixed input preparation. -/
theorem no_probeFree_hardFunction {degree : ℕ} [NeZero degree]
    (native : Program degree) (free : native.ProbeFree) :
    ¬ Computes native ForwardBoundary.hardFunction := by
  intro correct
  have decision : ComputablePred (fun input : ℕ =>
      (native.eval (Labels.prepare (inputLabels input))).Dom) :=
    ForwardBoundary.computablePred_comp
      (initial := inputLabels)
      (predicate := fun labels : Labels => (native.eval (Labels.prepare labels)).Dom)
      (Program.probeFree_native_halting_primrec native free).computablePred
      NativeInterface.primrec_inputLabels.to_comp
  exact ForwardBoundary.hardFunction_undecidable
    (decision.of_eq (fun input => computes_dom correct input))

/-- The conditional monodromy loops strictly extend the realizable partial functions. -/
theorem conditional_gates_strictly_extend :
    ∃ function : ℕ → Part ℕ, Realizable function ∧ ¬ ProbeFreeRealizable function := by
  refine ⟨ForwardBoundary.hardFunction,
    realizable_of_partrec ForwardBoundary.hardFunction_partrec, ?_⟩
  rintro ⟨degree, native, free, correct⟩
  exact no_probeFree_hardFunction native free correct

end Monodromy.Structure

namespace Monodromy.Structure

open CoupledContinuation NativeInterface

/-- The direct analytic comparator has exactly the native program's fixed numeric graph. -/
theorem analytic_computes_iff {degree : ℕ} [NeZero degree]
    (program : Program degree) (function : ℕ → Part ℕ) :
    (∀ input value, value ∈ function input ↔ ∃ labels : Labels,
      AnalyticComparison.embed labels ∈ AnalyticComparison.eval program
        (AnalyticComparison.embed (inputLabels input)) ∧ outputLabels labels = value) ↔
      Computes program function := by
  simp_rw [AnalyticComparison.result_iff]
  rfl

/-- The same finite programs have globally real analytic successors in three real coordinates. -/
theorem analytic_realization {function : ℕ → Part ℕ} (effective : Partrec function) :
    ∃ degree : ℕ, ∃ program : Program (degree + 1),
      (∀ state, AnalyticAt ℝ (AnalyticComparison.next program) state) ∧
      (∀ state, AnalyticAt ℝ (AnalyticComparison.halt program) state) ∧
      ∀ input value, value ∈ function input ↔ ∃ labels : Labels,
        AnalyticComparison.embed labels ∈ AnalyticComparison.eval program
          (AnalyticComparison.embed (inputLabels input)) ∧ outputLabels labels = value := by
  obtain ⟨degree, program, correct⟩ := realizable_of_partrec effective
  exact ⟨degree, program, AnalyticComparison.analyticAt_next program,
    AnalyticComparison.analyticAt_halt program, (analytic_computes_iff program function).mpr correct⟩

end Monodromy.Structure
