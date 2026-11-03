module

public import Monodromy.Autonomy

@[expose] public section

namespace Monodromy.ProgramCounter

open scoped BigOperators

variable {m : ℕ}

/-- A translated observation of one finite program position. -/
noncomputable def pcWeight (i : Fin m) (p : ℝ) : ℝ :=
  Logarithm.zeroWeight (p - (i : ℕ) * (2 * Real.pi))

theorem pcWeight_at_j (i j : Fin m) :
    pcWeight i ((j : ℕ) * (2 * Real.pi)) = if i = j then 1 else 0 := by
  have displacement : (j : ℝ) * (2 * Real.pi) - (i : ℝ) * (2 * Real.pi) =
      (((j.val : ℤ) - (i.val : ℤ) : ℤ) : ℝ) * (2 * Real.pi) := by
    push_cast
    ring
  have same : ((j.val : ℤ) - (i.val : ℤ) = 0) ↔ i = j := by
    rw [sub_eq_zero]
    constructor
    · intro equal
      apply Fin.ext
      exact_mod_cast equal.symm
    · rintro rfl
      rfl
  unfold pcWeight
  rw [displacement, Logarithm.zeroWeight_sheet]
  simp only [same]

theorem analyticAt_pcWeight (i : Fin m) (p : ℝ) : AnalyticAt ℝ (pcWeight i) p :=
  (Logarithm.analyticAt_zeroWeight (p - (i : ℕ) * (2 * Real.pi))).comp
    (f := fun q : ℝ => q - (i : ℕ) * (2 * Real.pi))
    (analyticAt_id.sub analyticAt_const)

/-- The finite coefficient table is fixed data of the model. -/
noncomputable def choose (values : Fin m → ℝ) (p : ℝ) : ℝ :=
  ∑ i, pcWeight i p * values i

theorem choose_at_j (values : Fin m → ℝ) (j : Fin m) :
    choose values ((j : ℕ) * (2 * Real.pi)) = values j := by
  classical
  simp [choose, pcWeight_at_j]

theorem analyticAt_choose (values : Fin m → ℝ) (p : ℝ) :
    AnalyticAt ℝ (choose values) p := by
  unfold choose
  exact Finset.analyticAt_fun_sum Finset.univ
    (fun i _ => (analyticAt_pcWeight i p).mul analyticAt_const)

end Monodromy.ProgramCounter
