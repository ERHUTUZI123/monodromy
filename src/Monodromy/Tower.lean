module

public import Monodromy.Radix
public import Mathlib.Analysis.Complex.CoveringMap

/-!
# Continuation through the covering tower

The finite root observation is carried by the same path as logarithmic memory.
Thus it records a lower level of the covering tower throughout execution.
-/

@[expose] public section

namespace Monodromy.Radix.Tower

open unitInterval

abbrev Punctured := {z : ℂ // z ≠ 0}

noncomputable def project (x : ℝ) : Punctured :=
  ⟨(Circle.exp x : ℂ), (Circle.exp x).coe_ne_zero⟩

def power (B : ℕ) (z : Punctured) : Punctured :=
  ⟨z.val ^ B, pow_ne_zero B z.property⟩

theorem covering (B : ℕ) [NeZero B] : IsCoveringMap (power B) :=
  isCoveringMap_npow B (by exact_mod_cast NeZero.ne B)

noncomputable def observe (B : ℕ) (x : ℝ) : Punctured := project (x / B)

theorem square (B : ℕ) [NeZero B] (x : ℝ) : power B (observe B x) = project x := by
  apply Subtype.ext
  exact congrArg (fun z : Circle => (z : ℂ)) (readRoot_pow B x)

noncomputable def basePath (curve : C(I, ℝ)) : Path (project (curve 0)) (project (curve 1)) where
  toFun t := project (curve t)
  continuous_toFun := by unfold project; fun_prop
  source' := rfl
  target' := rfl

noncomputable def rootLift (B : ℕ) (curve : C(I, ℝ)) : C(I, Punctured) where
  toFun t := observe B (curve t)
  continuous_toFun := by unfold observe project; fun_prop

/-- Actual finite-cover transport carries the observation of the logarithmic branch. -/
theorem transport_observe (B : ℕ) [NeZero B] (curve : C(I, ℝ)) :
    Transport.transport (covering B) (basePath curve)
      ⟨observe B (curve 0), square B (curve 0)⟩ =
      ⟨observe B (curve 1), square B (curve 1)⟩ := by
  apply Subtype.ext
  exact Transport.transport_eq_actual_lift (covering B) (basePath curve)
    ⟨observe B (curve 0), square B (curve 0)⟩ (rootLift B curve)
    (funext fun t => square B (curve t)) rfl

end Monodromy.Radix.Tower
