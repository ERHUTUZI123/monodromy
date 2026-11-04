module

public import Monodromy.Choice
public import Mathlib.Data.Fin.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Finite-root observations

The power covering reads a finite residue of the retained logarithmic branch.
Normalized kernels select its regular roots; integer residues occur only in proofs.
-/

@[expose] public section

namespace Monodromy.Radix

variable (B : ℕ) [NeZero B]

noncomputable def omega (digit : Fin B) : Circle :=
  Circle.exp (2 * Real.pi * (digit.val : ℝ) / (B : ℝ))

theorem primitive : IsPrimitiveRoot (Circle.exp (2 * Real.pi / (B : ℝ))) B := by
  have complex : IsPrimitiveRoot ((Circle.exp (2 * Real.pi / (B : ℝ)) : Circle) : ℂ) B := by
    convert Complex.isPrimitiveRoot_exp B (NeZero.ne B) using 1
    simp only [Circle.coe_exp]
    congr 1
    push_cast
    ring
  exact complex.of_map_of_injective (f := Circle.coeHom) Subtype.val_injective

omit [NeZero B] in
theorem omega_eq_pow (digit : Fin B) :
    omega B digit = Circle.exp (2 * Real.pi / (B : ℝ)) ^ digit.val := by
  rw [← Circle.exp_natCast_mul]
  unfold omega
  congr 1
  ring

theorem omega_injective : Function.Injective (omega B) := by
  intro first second same
  rw [omega_eq_pow, omega_eq_pow] at same
  exact Fin.ext ((primitive B).pow_inj first.isLt second.isLt same)

theorem omega_pow (digit : Fin B) : omega B digit ^ B = 1 := by
  rw [omega_eq_pow, ← pow_mul, Nat.mul_comm digit.val B, pow_mul,
    (primitive B).pow_eq_one, one_pow]

theorem omega_complex_pow (digit : Fin B) : (omega B digit : ℂ) ^ B = 1 := by
  simpa only [Circle.coe_pow, Circle.coe_one] using
    congrArg (fun point : Circle => (point : ℂ)) (omega_pow B digit)

/-- The logarithmic lift factors the exponential through the finite power cover. -/
noncomputable def readRoot (x : ℝ) : Circle := Circle.exp (x / (B : ℝ))

theorem readRoot_pow (x : ℝ) : readRoot B x ^ B = Circle.exp x := by
  unfold readRoot
  rw [← Circle.exp_natCast_mul]
  congr 1
  field_simp [show (B : ℝ) ≠ 0 by exact_mod_cast NeZero.ne B]

/-- The finite root reads the lowest radix digit, without a modulus in its definition. -/
theorem readRoot_digit (n : ℤ) (digit : Fin B) :
    readRoot B ((2 * Real.pi) * (((B : ℤ) * n + digit.val : ℤ) : ℝ)) = omega B digit := by
  have split :
      (2 * Real.pi) * (((B : ℤ) * n + digit.val : ℤ) : ℝ) / (B : ℝ) =
        (n : ℝ) * (2 * Real.pi) + 2 * Real.pi * (digit.val : ℝ) / (B : ℝ) := by
    push_cast
    field_simp [show (B : ℝ) ≠ 0 by exact_mod_cast NeZero.ne B]
  unfold readRoot
  rw [split, Circle.exp_add, Circle.exp_int_mul_two_pi, one_mul]
  rfl

theorem omega_regular (digit : Fin B) :
    deriv (fun z : ℂ => z ^ B) (omega B digit : ℂ) ≠ 0 := by
  rw [deriv_pow_field]
  exact mul_ne_zero (by exact_mod_cast NeZero.ne B)
    (pow_ne_zero _ (omega B digit).coe_ne_zero)

theorem kernel_root (marked digit : Fin B) :
    Choice.kernel (fun z : ℂ => z ^ B) (omega B marked : ℂ) (omega B digit : ℂ) =
      if marked = digit then 1 else 0 := by
  classical
  by_cases same : marked = digit
  · subst digit
    simpa using Choice.kernel_self (omega_regular B marked)
  · simp only [same, ↓reduceIte]
    apply Choice.kernel_other
    · intro equal
      exact same ((omega_injective B) (Subtype.ext equal)).symm
    · exact (omega_complex_pow B digit).trans (omega_complex_pow B marked).symm

end Monodromy.Radix

namespace Monodromy.Radix.Tower

abbrev Punctured := {z : ℂ // z ≠ 0}

def power (degree : ℕ) (point : Punctured) : Punctured :=
  ⟨point.val ^ degree, pow_ne_zero degree point.property⟩

theorem covering (degree : ℕ) [NeZero degree] : IsCoveringMap (power degree) :=
  isCoveringMap_npow degree (by exact_mod_cast NeZero.ne degree)

def one : Punctured := ⟨1, one_ne_zero⟩

abbrev Roots (degree : ℕ) := Transport.Fiber (power degree) one

theorem root_power {degree : ℕ} (root : Roots degree) : root.val.val ^ degree = 1 :=
  congrArg Subtype.val root.property

end Monodromy.Radix.Tower
