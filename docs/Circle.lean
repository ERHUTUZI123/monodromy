module

public import Monodromy.Covering
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Memory carried by a continuous covering

The control returns to `1 : Circle`; its actual lift through `Circle.exp`
retains an integer winding in the real state. This is an exact, infinite-sheet
example. It asserts neither finite-precision storage nor a learning advantage.
-/

@[expose] public section

namespace Monodromy.CircleMemory

open unitInterval

/-- The proposed lifted computation, with its full continuous trajectory. -/
noncomputable def anglePath (n : ℤ) : C(I, ℝ) where
  toFun t := (t : ℝ) * ((n : ℝ) * (2 * Real.pi))
  continuous_toFun := continuous_subtype_val.mul continuous_const

/-- A closed control path, rather than a supplied endpoint permutation. -/
noncomputable def windingLoop (n : ℤ) : Path (1 : Circle) 1 where
  toFun t := Circle.exp (anglePath n t)
  continuous_toFun := Circle.exp.continuous.comp (anglePath n).continuous
  source' := by simp [anglePath]
  target' := by simp [anglePath]

/-- The actual initial state above the control basepoint. -/
def initial : Transport.Fiber Circle.exp (1 : Circle) :=
  ⟨0, Circle.exp_zero⟩

/-- Uniqueness of covering-space lifts identifies the retained real state. -/
theorem winding_transport (n : ℤ) :
    (Transport.transport Circle.isCoveringMap_exp (windingLoop n) initial : ℝ) =
      (n : ℝ) * (2 * Real.pi) := by
  have endpoint := Transport.transport_eq_actual_lift Circle.isCoveringMap_exp
    (windingLoop n) initial (anglePath n) rfl (by simp [anglePath, initial])
  simpa [anglePath] using endpoint

/-- Different windings leave different states while the control is unchanged. -/
theorem winding_states_injective : Function.Injective (fun n : ℤ =>
    Transport.transport Circle.isCoveringMap_exp (windingLoop n) initial) := by
  intro m n equal
  have endpoints := congrArg Subtype.val equal
  rw [winding_transport, winding_transport] at endpoints
  have period_ne_zero : (2 : ℝ) * Real.pi ≠ 0 :=
    mul_ne_zero two_ne_zero Real.pi_ne_zero
  exact Int.cast_injective (mul_right_cancel₀ period_ne_zero endpoints)

end Monodromy.CircleMemory
