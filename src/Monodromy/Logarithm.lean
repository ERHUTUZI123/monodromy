module

public import Monodromy.Covering
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The branches of the logarithm

Restricting the exponential to imaginary arguments gives the circle covering.
Its fiber over one retains an integer. A loop transports every initial
branch by addition, proved from its actual continuous lift.
-/

@[expose] public section

namespace Monodromy.Logarithm

open unitInterval

abbrev Memory := Transport.Fiber Circle.exp (1 : Circle)

noncomputable def sheet (k : ℤ) : Memory :=
  ⟨(k : ℝ) * (2 * Real.pi), Circle.exp_int_mul_two_pi k⟩

noncomputable def integers : ℤ ≃ Memory := Equiv.ofBijective sheet ⟨by
    intro k n same
    have values := congrArg Subtype.val same
    change (k : ℝ) * (2 * Real.pi) = (n : ℝ) * (2 * Real.pi) at values
    exact Int.cast_injective (mul_right_cancel₀
      (mul_ne_zero two_ne_zero Real.pi_ne_zero) values), by
    intro root
    obtain ⟨k, same⟩ := Circle.exp_eq_one.mp root.2
    exact ⟨k, Subtype.ext same.symm⟩⟩

noncomputable def turn (n : ℤ) : Path (1 : Circle) 1 where
  toFun t := Circle.exp (((n : ℝ) * (t : ℝ)) * (2 * Real.pi))
  continuous_toFun := Circle.exp.continuous.comp
    ((continuous_const.mul continuous_subtype_val).mul continuous_const)
  source' := by simp
  target' := by simp

noncomputable def lift (k n : ℤ) : C(I, ℝ) where
  toFun t := ((k : ℝ) + (n : ℝ) * (t : ℝ)) * (2 * Real.pi)
  continuous_toFun := (continuous_const.add
    (continuous_const.mul continuous_subtype_val)).mul continuous_const

theorem transport_turn (k n : ℤ) :
    Transport.transport Circle.isCoveringMap_exp (turn n) (sheet k) = sheet (k + n) := by
  have projects : Circle.exp ∘ lift k n = turn n := by
    funext t
    simp [lift, turn, add_mul, Circle.exp_add]
  have starts : lift k n 0 = (sheet k : ℝ) := by simp [lift, sheet]
  apply Subtype.ext
  calc
    (Transport.transport Circle.isCoveringMap_exp (turn n) (sheet k) : ℝ) =
        lift k n 1 := Transport.transport_eq_actual_lift
          Circle.isCoveringMap_exp (turn n) (sheet k) (lift k n) projects starts
    _ = (sheet (k + n) : ℝ) := by simp [lift, sheet]

/-- Every fixed loop translates all branches by the same integer. -/
theorem transport_translation (γ : Path (1 : Circle) 1) (k : ℤ) :
    Transport.transport Circle.isCoveringMap_exp γ (sheet k) =
      sheet (k + integers.symm
        (Transport.transport Circle.isCoveringMap_exp γ (sheet 0))) := by
  let deck : C(ℝ, ℝ) :=
    ⟨fun x => x + (k : ℝ) * (2 * Real.pi), continuous_id.add continuous_const⟩
  have square : Circle.exp ∘ deck = Circle.exp := by
    funext x
    simp [deck, Circle.exp_add]
  have mapped (j : ℤ) : Transport.mapFiber deck square (sheet j) = sheet (j + k) := by
    apply Subtype.ext
    simp [Transport.mapFiber, deck, sheet, add_mul]
  have natural := Transport.transport_naturality
    Circle.isCoveringMap_exp Circle.isCoveringMap_exp deck square γ (sheet 0)
  rw [mapped, zero_add] at natural
  have endpoint : sheet (integers.symm
      (Transport.transport Circle.isCoveringMap_exp γ (sheet 0))) =
      Transport.transport Circle.isCoveringMap_exp γ (sheet 0) :=
    integers.apply_symm_apply _
  rw [← endpoint, mapped] at natural
  simpa [add_comm] using natural

end Monodromy.Logarithm
