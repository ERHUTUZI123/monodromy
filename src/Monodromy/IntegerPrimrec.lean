module

public import Mathlib.Computability.Primrec.Basic
public import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Ring

/-!
# Effective integer primitives

The canonical signed encoding reduces integer arithmetic and positive-base
Euclidean division to primitive recursive operations on natural numbers.
-/

@[expose] public section

namespace Monodromy.IntegerPrimrec

def split (value : ℤ) : ℕ ⊕ ℕ := Equiv.intEquivNatSumNat value

def join (value : ℕ ⊕ ℕ) : ℤ := Sum.elim Int.ofNat Int.negSucc value

theorem split_primrec : Primrec split :=
  Primrec.encode_iff.mp ((Primrec.encode : Primrec (Encodable.encode : ℤ → ℕ)).of_eq
    (fun value => by cases value <;> rfl))

theorem join_primrec : Primrec join :=
  Primrec.encode_iff.mp ((Primrec.encode : Primrec (Encodable.encode : ℕ ⊕ ℕ → ℕ)).of_eq
    (fun value => by cases value <;> rfl))

theorem ofNat : Primrec Int.ofNat := join_primrec.comp Primrec.sumInl

theorem negSucc : Primrec Int.negSucc := join_primrec.comp Primrec.sumInr

theorem cases {α β : Type*} [Primcodable α] [Primcodable β] {key : α → ℤ}
    {positive negative : α → ℕ → β} (key_primrec : Primrec key)
    (positive_primrec : Primrec₂ positive) (negative_primrec : Primrec₂ negative) :
    Primrec (fun input : α => Sum.elim (positive input) (negative input) (split (key input))) :=
  Primrec.sumCasesOn (split_primrec.comp key_primrec) positive_primrec negative_primrec

def difference (first second : ℕ) : ℤ :=
  if second ≤ first then Int.ofNat (first - second) else Int.negSucc (second - first - 1)

theorem difference_eq (first second : ℕ) : difference first second = (first : ℤ) - second := by
  unfold difference
  split_ifs <;> (try simp only [Int.ofNat_eq_natCast]) <;> omega

theorem difference_primrec : Primrec₂ difference :=
  Primrec.ite (Primrec.nat_le.comp Primrec.snd Primrec.fst)
    (ofNat.comp (Primrec.nat_sub.comp Primrec.fst Primrec.snd))
    (negSucc.comp (Primrec.nat_sub.comp (Primrec.nat_sub.comp Primrec.snd Primrec.fst)
      (Primrec.const 1)))

theorem add : Primrec₂ ((· + ·) : ℤ → ℤ → ℤ) := by
  have positive : Primrec₂ (fun point : ℤ × ℤ => fun first : ℕ => (first : ℤ) + point.2) := by
    have piecewise := cases (Primrec.snd.comp (Primrec.fst : Primrec (Prod.fst : (ℤ × ℤ) × ℕ → ℤ × ℤ)))
      (ofNat.comp (Primrec.nat_add.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)).to₂
      (difference_primrec.comp (Primrec.snd.comp Primrec.fst) (Primrec.succ.comp Primrec.snd)).to₂
    exact piecewise.of_eq (fun point => by
      rcases point with ⟨⟨x, y⟩, n⟩
      cases y with
      | ofNat m => rfl
      | negSucc m =>
          change difference n (m + 1) = (n : ℤ) + Int.negSucc m
          rw [difference_eq]
          omega)
  have negative : Primrec₂ (fun point : ℤ × ℤ => fun first : ℕ => Int.negSucc first + point.2) := by
    have piecewise := cases (Primrec.snd.comp (Primrec.fst : Primrec (Prod.fst : (ℤ × ℤ) × ℕ → ℤ × ℤ)))
      (difference_primrec.comp Primrec.snd (Primrec.succ.comp (Primrec.snd.comp Primrec.fst))).to₂
      (negSucc.comp (Primrec.succ.comp
        (Primrec.nat_add.comp (Primrec.snd.comp Primrec.fst) Primrec.snd))).to₂
    exact piecewise.of_eq (fun point => by
      rcases point with ⟨⟨x, y⟩, n⟩
      cases y with
      | ofNat m =>
          change difference m (n + 1) = Int.negSucc n + (m : ℤ)
          rw [difference_eq]
          omega
      | negSucc m =>
          change Int.negSucc (n + m + 1) = Int.negSucc n + Int.negSucc m
          omega)
  exact (cases Primrec.fst positive negative).of_eq (fun point => by cases point.1 <;> rfl)

theorem negate : Primrec (fun value : ℤ => -value) := by
  have positive : Primrec (fun value : ℕ => -(value : ℤ)) :=
    (Primrec.nat_casesOn₁ (0 : ℤ) negSucc).of_eq (by intro value; cases value <;> rfl)
  exact (cases Primrec.id (positive.comp Primrec.snd).to₂ (ofNat.comp (Primrec.succ.comp Primrec.snd)).to₂).of_eq
    (by intro value; cases value <;> rfl)

theorem scale_nat (coefficient : ℕ) : Primrec (fun value : ℤ => (coefficient : ℤ) * value) := by
  induction coefficient with
  | zero => simpa using (Primrec.const (0 : ℤ))
  | succ coefficient previous =>
      exact (add.comp previous Primrec.id).of_eq (by intro value; change (coefficient : ℤ) * value + value = _; push_cast; ring)

theorem scale (coefficient : ℤ) : Primrec (fun value : ℤ => coefficient * value) := by
  cases coefficient with
  | ofNat value => exact scale_nat value
  | negSucc value =>
      exact (negate.comp (scale_nat (value + 1))).of_eq (by intro input; simp [Int.negSucc_eq]; ring)

theorem quotient (B : ℕ) : Primrec (fun value : ℤ => value / ((B + 1 : ℕ) : ℤ)) := by
  exact (cases Primrec.id
    (ofNat.comp (Primrec.nat_div.comp Primrec.snd (Primrec.const (B + 1)))).to₂
    (negSucc.comp (Primrec.nat_div.comp Primrec.snd (Primrec.const (B + 1)))).to₂).of_eq
      (by intro value; cases value <;> rfl)

theorem remainder (B : ℕ) : Primrec (fun value : ℤ => (value % ((B + 1 : ℕ) : ℤ)).toNat) := by
  have piecewise := cases Primrec.id
    (Primrec.nat_mod.comp Primrec.snd (Primrec.const (B + 1))).to₂
    (Primrec.nat_sub.comp (Primrec.const B)
      (Primrec.nat_mod.comp Primrec.snd (Primrec.const (B + 1)))).to₂
  apply piecewise.of_eq
  intro value
  cases value with
  | ofNat value => rfl
  | negSucc value =>
      change B - value % (B + 1) = (Int.negSucc value % ((B + 1 : ℕ) : ℤ)).toNat
      rw [Int.negSucc_emod value (by omega : 0 < ((B + 1 : ℕ) : ℤ))]
      rw [← Int.natCast_emod]
      have bound : value % (B + 1) < B + 1 := Nat.mod_lt _ (by omega)
      omega

end Monodromy.IntegerPrimrec
