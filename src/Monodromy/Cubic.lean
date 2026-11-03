module

public import Monodromy.Choice
public import Mathlib.Analysis.Complex.CoveringMap
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-!
# One path, three roots

The cubic `z³ - 3z` covers the plane away from its two critical values.
One predetermined loop fixes one carried root and exchanges two others.
Its three explicit lifts identify this action with actual covering transport.
-/

@[expose] public section

namespace Monodromy.Cubic

open Polynomial unitInterval

noncomputable section

def polynomial : ℂ[X] := X ^ 3 - C 3 * X

@[simp] theorem eval_polynomial (z : ℂ) : polynomial.eval z = z ^ 3 - 3 * z := by
  simp [polynomial]

theorem critical_values :
    polynomial.eval '' {z | polynomial.derivative.eval z = 0} ⊆ ({2, -2} : Set ℂ) := by
  rintro _ ⟨z, hz, rfl⟩
  have derivative : polynomial.derivative.eval z = 3 * (z - 1) * (z + 1) := by
    simp [polynomial]
    ring
  change polynomial.derivative.eval z = 0 at hz
  rw [derivative] at hz
  have cases : z = 1 ∨ z = -1 := by
    rcases mul_eq_zero.mp hz with hz | hz
    · exact Or.inl (sub_eq_zero.mp
        ((mul_eq_zero.mp hz).resolve_left (by norm_num)))
    · exact Or.inr (eq_neg_of_add_eq_zero_left hz)
  rcases cases with rfl | rfl <;> norm_num

def regular : Set ℂ := ({2, -2} : Set ℂ)ᶜ

abbrev Space := polynomial.eval ⁻¹' regular
abbrev Base := regular

def projection : Space → Base := regular.restrictPreimage polynomial.eval

theorem covering : IsCoveringMap projection :=
  (polynomial.isCoveringMapOn_eval.mono
    (Set.compl_subset_compl.mpr critical_values)).isCoveringMap_restrictPreimage

/-- The three branches of the cubic along a common complex angle. -/
def root (θ : ℂ) (k : Fin 3) : ℂ :=
  2 * Complex.cos ((θ + (k : ℕ) * (2 * Real.pi)) / 3)

theorem root_equation (θ : ℂ) (k : Fin 3) :
    root θ k ^ 3 - 3 * root θ k = 2 * Complex.cos θ := by
  have h := Complex.cos_three_mul ((θ + (k : ℕ) * (2 * Real.pi)) / 3)
  rw [show 3 * ((θ + (k : ℕ) * (2 * Real.pi)) / 3) =
    θ + (k : ℕ) * (2 * Real.pi) by ring,
    Complex.cos_add_nat_mul_two_pi] at h
  dsimp [root]
  linear_combination -2 * h

theorem root_injective {θ : ℂ} (hθ : Complex.sin θ ≠ 0) :
    Function.Injective (root θ) := by
  intro i j hij
  have hc : Complex.cos ((θ + (i : ℕ) * (2 * Real.pi)) / 3) =
      Complex.cos ((θ + (j : ℕ) * (2 * Real.pi)) / 3) :=
    mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) hij
  obtain ⟨k, hk | hk⟩ := Complex.cos_eq_cos_iff.mp hc
  · have he : ((j.val : ℂ) - i.val - 3 * (k : ℂ)) * Real.pi = 0 := by
      linear_combination (3 / 2 : ℂ) * hk
    have hz : (j.val : ℂ) - i.val - 3 * (k : ℂ) = 0 :=
      (mul_eq_zero.mp he).resolve_right (by exact_mod_cast Real.pi_ne_zero)
    have hint : (j.val : ℤ) - i.val - 3 * k = 0 := by exact_mod_cast hz
    apply Fin.ext
    have hi := i.isLt
    have hj := j.isLt
    omega
  · exfalso
    apply hθ
    apply Complex.sin_eq_zero_iff.mpr
    refine ⟨3 * k - j.val - i.val, ?_⟩
    push_cast
    linear_combination (3 / 2 : ℂ) * hk

theorem root_neg_zero (θ : ℂ) : root (-θ) 0 = root θ 0 := by
  simp [root, neg_div, Complex.cos_neg]

theorem root_neg_one (θ : ℂ) : root (-θ) 1 = root θ 2 := by
  norm_num only [root, Fin.coe_ofNat_eq_mod, Nat.cast_one, Nat.cast_ofNat]
  change 2 * Complex.cos ((-θ + 1 * (2 * Real.pi)) / 3) =
    2 * Complex.cos ((θ + 2 * (2 * Real.pi)) / 3)
  rw [show (θ + 2 * (2 * Real.pi)) / 3 =
    (1 : ℤ) * (2 * (Real.pi : ℂ)) - ((-θ + 1 * (2 * Real.pi)) / 3) by ring]
  rw [Complex.cos_int_mul_two_pi_sub]

theorem root_neg_two (θ : ℂ) : root (-θ) 2 = root θ 1 := by
  have h := root_neg_one (-θ)
  simpa only [neg_neg] using h.symm

/-- Half a turn of the angle induces a closed loop in the cubic's base. -/
def angle (t : ℝ) : ℂ :=
  (Real.pi / 2 : ℝ) * (Circle.exp (Real.pi * t) : ℂ)

theorem norm_angle (t : ℝ) : ‖angle t‖ = Real.pi / 2 := by
  simp only [angle, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < Real.pi / 2), Circle.norm_coe, mul_one]

theorem angle_zero : angle 0 = (Real.pi / 2 : ℝ) := by simp [angle]

theorem angle_one : angle 1 = -(Real.pi / 2 : ℝ) := by
  simp [angle, Circle.coe_exp, Complex.exp_pi_mul_I]

theorem sin_angle_ne_zero (t : ℝ) : Complex.sin (angle t) ≠ 0 := by
  intro h
  obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp h
  have hn := norm_angle t
  rw [hk, norm_mul] at hn
  have hkn : ‖(k : ℂ)‖ = |(k : ℝ)| := by simp
  rw [hkn, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos] at hn
  have hsmall : |(k : ℝ)| < 1 := by nlinarith [Real.pi_pos]
  have hk0 : k = 0 := Int.abs_lt_one_iff.mp (by exact_mod_cast hsmall)
  subst k
  norm_num at hn
  linarith [Real.pi_pos]

theorem continuous_angle : Continuous angle := by
  unfold angle
  fun_prop

theorem continuous_root (i : Fin 3) : Continuous (fun t : ℝ => root (angle t) i) :=
  (Complex.continuous_cos.comp
    ((continuous_angle.add continuous_const).div_const _)).const_mul _

def base (t : ℝ) : ℂ := 2 * Complex.cos (angle t)

theorem base_zero : base 0 = 0 := by
  simp [base, angle_zero, Complex.ofReal_div, Complex.cos_pi_div_two]

theorem base_one : base 1 = 0 := by
  simp [base, angle_one, Complex.ofReal_div, Complex.cos_pi_div_two]

theorem continuous_base : Continuous base :=
  (Complex.continuous_cos.comp continuous_angle).const_mul _

theorem base_regular (t : ℝ) : base t ∈ regular := by
  have exclude (square : Complex.cos (angle t) ^ 2 = 1) : False := by
    have sine : Complex.sin (angle t) ^ 2 = 0 := by
      linear_combination Complex.sin_sq_add_cos_sq (angle t) - square
    exact sin_angle_ne_zero t (eq_zero_of_pow_eq_zero sine)
  simp only [regular, Set.mem_compl_iff, Set.mem_insert_iff,
    Set.mem_singleton_iff, not_or]
  constructor <;> intro h <;> apply exclude
  · have hc : Complex.cos (angle t) = 1 := by
      dsimp [base] at h
      linear_combination (1 / 2 : ℂ) * h
    simp [hc]
  · have hc : Complex.cos (angle t) = -1 := by
      dsimp [base] at h
      linear_combination (1 / 2 : ℂ) * h
    simp [hc]

def basePoint : Base := ⟨0, by norm_num [regular]⟩

/-- This same base path is used for every initial root. -/
def loop : Path basePoint basePoint where
  toFun t := ⟨base (t : ℝ), base_regular (t : ℝ)⟩
  continuous_toFun := (continuous_base.comp continuous_subtype_val).subtype_mk _
  source' := Subtype.ext base_zero
  target' := Subtype.ext base_one

def lift (i : Fin 3) : C(I, Space) where
  toFun t := ⟨root (angle (t : ℝ)) i, by
    change polynomial.eval (root (angle (t : ℝ)) i) ∈ regular
    rw [eval_polynomial, root_equation]
    exact base_regular (t : ℝ)⟩
  continuous_toFun := ((continuous_root i).comp continuous_subtype_val).subtype_mk _

theorem lift_projects (i : Fin 3) : projection ∘ lift i = loop := by
  funext t
  apply Subtype.ext
  change polynomial.eval (root (angle (t : ℝ)) i) = base (t : ℝ)
  simpa only [eval_polynomial, base] using root_equation (angle (t : ℝ)) i

abbrev Memory := Transport.Fiber projection basePoint

def state (i : Fin 3) : Memory :=
  ⟨lift i 0, (congrFun (lift_projects i) 0).trans loop.source⟩

theorem state_injective : Function.Injective state := by
  intro i j h
  have roots := congrArg (fun e : Memory => (e : Space).val) h
  exact root_injective (sin_angle_ne_zero 0) roots

theorem lift_endpoint_zero : lift 0 1 = (state 0 : Space) := by
  apply Subtype.ext
  change root (angle 1) 0 = root (angle 0) 0
  simpa only [angle_one, angle_zero, Complex.ofReal_neg] using
    root_neg_zero ((Real.pi / 2 : ℝ) : ℂ)

theorem lift_endpoint_one : lift 1 1 = (state 2 : Space) := by
  apply Subtype.ext
  change root (angle 1) 1 = root (angle 0) 2
  simpa only [angle_one, angle_zero, Complex.ofReal_neg] using
    root_neg_one ((Real.pi / 2 : ℝ) : ℂ)

theorem lift_endpoint_two : lift 2 1 = (state 1 : Space) := by
  apply Subtype.ext
  change root (angle 1) 2 = root (angle 0) 1
  simpa only [angle_one, angle_zero, Complex.ofReal_neg] using
    root_neg_two ((Real.pi / 2 : ℝ) : ℂ)

def operation : Memory → Memory := Transport.transport covering loop

theorem operation_state_zero : operation (state 0) = state 0 := by
  apply Subtype.ext
  exact (Transport.transport_eq_actual_lift covering loop (state 0) (lift 0)
    (lift_projects 0) rfl).trans lift_endpoint_zero

theorem operation_state_one : operation (state 1) = state 2 := by
  apply Subtype.ext
  exact (Transport.transport_eq_actual_lift covering loop (state 1) (lift 1)
    (lift_projects 1) rfl).trans lift_endpoint_one

theorem operation_state_two : operation (state 2) = state 1 := by
  apply Subtype.ext
  exact (Transport.transport_eq_actual_lift covering loop (state 2) (lift 2)
    (lift_projects 2) rfl).trans lift_endpoint_two

/-- Actual continuation along one fixed loop retains one state and moves another. -/
theorem selective : Choice.Selective (Transport.transport covering loop) := by
  refine ⟨state 0, state 1, operation_state_zero, ?_⟩
  change operation (state 1) ≠ state 1
  rw [operation_state_one]
  exact fun h => (by decide : (2 : Fin 3) ≠ 1) (state_injective h)

end

end Monodromy.Cubic
