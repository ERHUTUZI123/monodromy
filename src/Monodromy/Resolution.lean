module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Linarith

/-!
# Resolution under integer computation

Affine operations preserve every residue observation. Division by a radix
needs one finer input observation, and in general cannot use the old one.
-/

@[expose] public section

namespace Monodromy.Resolution

/-- Integer affine computation descends through every residue quotient. -/
theorem affine_modEq (a b : ℤ) {m x y : ℤ} (same : x ≡ y [ZMOD m]) :
    a * x + b ≡ a * y + b [ZMOD m] :=
  (same.mul_left a).add_right b

/-- Removing one radix level lowers the available observation by that level. -/
theorem tail_modEq (B : ℤ) (nonzero : B ≠ 0) {m x y : ℤ}
    (same : x ≡ y [ZMOD B * m]) : x / B ≡ y / B [ZMOD m] := by
  obtain ⟨k, relation⟩ := Int.modEq_iff_add_fac.mp same
  apply Int.modEq_iff_add_fac.mpr
  refine ⟨k, ?_⟩
  rw [relation, mul_assoc, Int.add_mul_ediv_left x (m * k) nonzero]

/-- A nontrivial output residue has precisely the radix-multiplied input degree. -/
theorem tail_degree_iff (B m N : ℤ) (radix : 0 < B) (modulus : 2 ≤ m) :
    (∀ x y : ℤ, x ≡ y [ZMOD N] → x / B ≡ y / B [ZMOD m]) ↔ B * m ∣ N := by
  constructor
  · intro preserves
    have quotient_zero : N / B ≡ 0 [ZMOD m] := by
      have compared := preserves 0 N (by simp [Int.ModEq])
      simpa using compared.symm
    have remainder_nonnegative : 0 ≤ N % B := Int.emod_nonneg N radix.ne'
    have remainder_bounded : N % B < B := Int.emod_lt_of_pos N radix
    have remainder_zero : N % B = 0 := by
      by_contra nonzero
      have first_zero : (B - N % B) / B = 0 :=
        Int.ediv_eq_zero_of_lt (by omega) (by omega)
      have second_next : (B - N % B + N) / B = N / B + 1 := by
        have regroup : B - N % B + N = B * (N / B + 1) := by
          nlinarith [Int.emod_add_mul_ediv N B]
        rw [regroup, Int.mul_ediv_cancel_left _ radix.ne']
      have compared := preserves (B - N % B) (B - N % B + N)
        (Int.modEq_iff_add_fac.mpr ⟨1, by simp⟩)
      rw [first_zero, second_next] at compared
      have one_zero : (1 : ℤ) ≡ 0 [ZMOD m] := by
        simpa using compared.symm.sub quotient_zero
      change 1 % m = 0 % m at one_zero
      rw [Int.emod_eq_of_lt (by omega) (by omega), Int.zero_emod] at one_zero
      omega
    obtain ⟨k, quotient⟩ := Int.modEq_zero_iff_dvd.mp quotient_zero
    refine ⟨k, ?_⟩
    calc
      N = B * (N / B) := by simpa [remainder_zero] using (Int.emod_add_mul_ediv N B).symm
      _ = B * (m * k) := by rw [quotient]
      _ = (B * m) * k := (mul_assoc B m k).symm
  · intro refines x y same
    exact tail_modEq B radix.ne' (same.of_dvd refines)

/-- Even positive radix division generally fails to preserve the same resolution. -/
theorem tail_counterexample (B m : ℤ) (radix : 2 ≤ B) (modulus : 2 ≤ m) :
    (B - 1 ≡ B - 1 + m [ZMOD m]) ∧
      ¬ ((B - 1) / B ≡ (B - 1 + m) / B [ZMOD m]) := by
  have positive : 0 < B := by omega
  have small : (B - 1) / B = 0 := Int.ediv_eq_zero_of_lt (by omega) (by omega)
  have lower : 1 ≤ (B - 1 + m) / B := by
    apply (Int.le_ediv_iff_mul_le positive).mpr
    omega
  have upper : (B - 1 + m) / B < m := by
    apply (Int.ediv_lt_iff_lt_mul positive).mpr
    have product : 0 < (B - 1) * (m - 1) := mul_pos (by omega) (by omega)
    nlinarith
  constructor
  · apply Int.modEq_iff_add_fac.mpr
    exact ⟨1, by simp⟩
  · intro same
    change (B - 1) / B % m = (B - 1 + m) / B % m at same
    rw [small, Int.zero_emod, Int.emod_eq_of_lt (by omega) upper] at same
    omega

/-- For positive moduli, only identity division or the trivial quotient stays closed. -/
theorem tail_preserves_iff (B m : ℤ) (radix : 0 < B) (modulus : 0 < m) :
    (∀ x y : ℤ, x ≡ y [ZMOD m] → x / B ≡ y / B [ZMOD m]) ↔ B = 1 ∨ m = 1 := by
  constructor
  · intro preserves
    by_cases identity : B = 1
    · exact Or.inl identity
    by_cases trivial : m = 1
    · exact Or.inr trivial
    have failure := tail_counterexample B m (by omega) (by omega)
    exact (failure.2 (preserves _ _ failure.1)).elim
  · rintro (rfl | rfl)
    · intro x y same
      simpa using same
    · intro x y _
      simp [Int.ModEq]

/-- A fixed coefficient table is read only at the residue of the current state. -/
def caseAffine (B : ℤ) (table : ℤ → ℤ × ℤ) (x : ℤ) : ℤ :=
  (table (x % B)).1 * x + (table (x % B)).2

/-- A positive branch modulus queries only its finite interval of residue labels. -/
theorem case_labels_bounded (B x : ℤ) (positive : 0 < B) : 0 ≤ x % B ∧ x % B < B :=
  ⟨Int.emod_nonneg x positive.ne', Int.emod_lt_of_pos x positive⟩

/-- Branch selection stays closed at any resolution refining its residue modulus. -/
theorem caseAffine_modEq (B : ℤ) (table : ℤ → ℤ × ℤ) {M x y : ℤ}
    (refines : B ∣ M) (same : x ≡ y [ZMOD M]) :
    caseAffine B table x ≡ caseAffine B table y [ZMOD M] := by
  have branch : x % B = y % B := same.of_dvd refines
  unfold caseAffine
  rw [branch]
  exact affine_modEq _ _ same

end Monodromy.Resolution

namespace Monodromy.Resolution

/-- Repeated Euclidean descent removes precisely the requested number of digits. -/
theorem iterate_tail (B : ℤ) (radix : 0 < B) (rounds : ℕ) (x : ℤ) :
    ((fun value : ℤ => value / B)^[rounds]) x = x / B ^ rounds := by
  induction rounds with
  | zero => simp
  | succ rounds previous =>
      rw [Function.iterate_succ_apply', previous, Int.ediv_ediv_of_nonneg (le_of_lt (Int.pow_pos radix)),
        pow_succ]

/-- Every further descent requires one further radix factor in the observed input. -/
theorem iterate_tail_degree_iff (B m N : ℤ) (radix : 0 < B) (modulus : 2 ≤ m) (rounds : ℕ) :
    (∀ x y : ℤ, x ≡ y [ZMOD N] →
      ((fun value : ℤ => value / B)^[rounds]) x ≡
        ((fun value : ℤ => value / B)^[rounds]) y [ZMOD m]) ↔ B ^ rounds * m ∣ N := by
  simp_rw [iterate_tail B radix rounds]
  exact tail_degree_iff (B ^ rounds) m N (Int.pow_pos radix) modulus

/-- Preservation at every depth forces the input residue relation to be equality. -/
theorem all_depths_iff (B m N : ℤ) (radix : 2 ≤ B) (modulus : 2 ≤ m) :
    (∀ rounds : ℕ, ∀ x y : ℤ, x ≡ y [ZMOD N] →
      ((fun value : ℤ => value / B)^[rounds]) x ≡
        ((fun value : ℤ => value / B)^[rounds]) y [ZMOD m]) ↔ N = 0 := by
  constructor
  · intro preserves
    by_contra nonzero
    obtain ⟨rounds, bound⟩ := pow_unbounded_of_one_lt |N| (by omega : 1 < B)
    have divides := (iterate_tail_degree_iff B m N (by omega) modulus rounds).mp (preserves rounds)
    have power_divides : B ^ rounds ∣ N := (dvd_mul_right (B ^ rounds) m).trans divides
    have upper : B ^ rounds ≤ |N| :=
      Int.le_of_dvd (abs_pos.mpr nonzero) ((dvd_abs _ _).mpr power_divides)
    exact not_lt_of_ge upper bound
  · rintro rfl rounds x y same
    have equal : x = y := by simpa [Int.ModEq] using same
    subst y
    exact Int.ModEq.rfl

end Monodromy.Resolution
