module

public import Monodromy.CoverExpressions

/-!
# Finite tables from one ternary observation

Successive ternary observations read a finite address from the least
significant end. Each query uses the same cubic cover and its descent.
-/

@[expose] public section

namespace Monodromy.CoverExpressions.Ternary

variable {n : ℕ}

/-- A finite address at depth `depth`, including negative integer inputs. -/
def residue (depth : ℕ) (value : ℤ) : Fin (3 ^ depth) :=
  ⟨(value % ((3 ^ depth : ℕ) : ℤ)).toNat, by
    have positive : 0 < ((3 ^ depth : ℕ) : ℤ) := by exact_mod_cast pow_pos (by omega : 0 < 3) depth
    have lower := Int.emod_nonneg value positive.ne'
    have upper := Int.emod_lt_of_pos value positive
    omega⟩

theorem residue_cast (depth : ℕ) (value : ℤ) :
    ((residue depth value).val : ℤ) = value % ((3 ^ depth : ℕ) : ℤ) :=
  Int.toNat_of_nonneg (Int.emod_nonneg value (by exact_mod_cast pow_ne_zero depth (by omega : (3 : ℕ) ≠ 0)))

/-- The current ternary digit precedes the remaining address. -/
def join (depth : ℕ) (low : Fin 3) (high : Fin (3 ^ depth)) : Fin (3 ^ (depth + 1)) :=
  ⟨low.val + 3 * high.val, by rw [pow_succ]; omega⟩

theorem residue_succ (depth : ℕ) (value : ℤ) :
    join depth (digit 2 value) (residue depth (value / 3)) = residue (depth + 1) value := by
  let address := join depth (digit 2 value) (residue depth (value / 3))
  have address_cast : (address.val : ℤ) =
      value % 3 + 3 * ((value / 3) % ((3 ^ depth : ℕ) : ℤ)) := by
    simp only [address, join, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, digit_cast, residue_cast]
    norm_num
  have power : ((3 ^ (depth + 1) : ℕ) : ℤ) = 3 * ((3 ^ depth : ℕ) : ℤ) := by
    rw [pow_succ, Nat.cast_mul, Nat.cast_ofNat, mul_comm]
  have same : (address.val : ℤ) ≡ value [ZMOD ((3 ^ (depth + 1) : ℕ) : ℤ)] := by
    apply Int.modEq_iff_add_fac.mpr
    refine ⟨(value / 3) / ((3 ^ depth : ℕ) : ℤ), ?_⟩
    rw [address_cast, power]
    nlinarith [Int.mul_ediv_add_emod value 3,
      Int.mul_ediv_add_emod (value / 3) ((3 ^ depth : ℕ) : ℤ)]
  apply Fin.ext
  have bounded : (address.val : ℤ) < ((3 ^ (depth + 1) : ℕ) : ℤ) := by exact_mod_cast address.isLt
  have lower : 0 ≤ (address.val : ℤ) := by omega
  have result : (address.val : ℤ) = value % ((3 ^ (depth + 1) : ℕ) : ℤ) := by
    simpa only [Int.emod_eq_of_lt lower bounded] using same.eq
  exact_mod_cast result.trans (residue_cast (depth + 1) value).symm

/-- Read any finite power-of-three table using only ternary queries and descent. -/
def selectPower : (depth : ℕ) → Term n → (Fin (3 ^ depth) → Term n) → Term n
  | 0, _, table => table 0
  | depth + 1, key, table =>
      .select 2 key (fun low =>
        selectPower depth (.descend 2 key) (fun high => table (join depth low high)))

/-- The recursive query tree returns exactly the entry at the input's finite address. -/
theorem eval_selectPower (depth : ℕ) (key : Term n) (table : Fin (3 ^ depth) → Term n)
    (state : Fin n → ℤ) :
    evalInt (selectPower depth key table) state = evalInt (table (residue depth (evalInt key state))) state := by
  induction depth generalizing key with
  | zero =>
      have empty : residue 0 (evalInt key state) = 0 := by
        apply Fin.ext
        have bounded := (residue 0 (evalInt key state)).isLt
        norm_num at bounded
        omega
      simp [selectPower, empty]
  | succ depth correct =>
      simp only [selectPower, evalInt]
      rw [correct]
      change evalInt (table (join depth (digit 2 (evalInt key state))
        (residue depth (evalInt key state / 3)))) state = _
      rw [residue_succ]

/-- The corresponding guard table uses the same finite ternary address. -/
def selectGuardPower : (depth : ℕ) → Term n → (Fin (3 ^ depth) → Guard n) → Guard n
  | 0, _, table => table 0
  | depth + 1, key, table =>
      .select 2 key (fun low =>
        selectGuardPower depth (.descend 2 key) (fun high => table (join depth low high)))

theorem eval_selectGuardPower (depth : ℕ) (key : Term n) (table : Fin (3 ^ depth) → Guard n)
    (state : Fin n → ℤ) :
    Guard.evalInt (selectGuardPower depth key table) state =
      Guard.evalInt (table (residue depth (evalInt key state))) state := by
  induction depth generalizing key with
  | zero =>
      have empty : residue 0 (evalInt key state) = 0 := by
        apply Fin.ext
        have bounded := (residue 0 (evalInt key state)).isLt
        norm_num at bounded
        omega
      simp [selectGuardPower, empty]
  | succ depth correct =>
      simp only [selectGuardPower, Guard.evalInt]
      rw [correct]
      change Guard.evalInt (table (join depth (digit 2 (evalInt key state))
        (residue depth (evalInt key state / 3)))) state = _
      rw [residue_succ]

/-- Remove a finite address by repeated descent through the cubic observation. -/
def quotientPower : ℕ → Term n → Term n
  | 0, key => key
  | depth + 1, key => quotientPower depth (.descend 2 key)

theorem eval_quotientPower (depth : ℕ) (key : Term n) (state : Fin n → ℤ) :
    evalInt (quotientPower depth key) state = evalInt key state / ((3 ^ depth : ℕ) : ℤ) := by
  induction depth generalizing key with
  | zero => simp [quotientPower]
  | succ depth correct =>
      rw [quotientPower, correct]
      change evalInt key state / 3 / ((3 ^ depth : ℕ) : ℤ) = _
      rw [Int.ediv_ediv_of_nonneg (by omega), pow_succ, Nat.cast_mul, Nat.cast_ofNat, mul_comm]

end Monodromy.CoverExpressions.Ternary

namespace Monodromy.CoverExpressions

variable {n : ℕ}

/-- All finite observations and descents in an expression have the same cover degree. -/
def UsesRadix (radix : ℕ) : Term n → Prop
  | .coord _ | .integerConst _ => True
  | .add first second => UsesRadix radix first ∧ UsesRadix radix second
  | .integerScale _ term => UsesRadix radix term
  | .select B key branches => B + 1 = radix ∧ UsesRadix radix key ∧ ∀ index, UsesRadix radix (branches index)
  | .descend B key => B + 1 = radix ∧ UsesRadix radix key

def Guard.UsesRadix (radix : ℕ) : Guard n → Prop
  | .constant _ => True
  | .select B key branches => B + 1 = radix ∧ CoverExpressions.UsesRadix radix key ∧
      ∀ index, Guard.UsesRadix radix (branches index)

namespace Ternary

theorem selectPower_usesRadix (depth : ℕ) (key : Term n) (table : Fin (3 ^ depth) → Term n)
    (key_uses : UsesRadix 3 key) (table_uses : ∀ index, UsesRadix 3 (table index)) :
    UsesRadix 3 (selectPower depth key table) := by
  induction depth generalizing key with
  | zero => exact table_uses 0
  | succ depth correct =>
      exact ⟨rfl, key_uses, fun low =>
        correct (.descend 2 key) (fun high => table (join depth low high))
          ⟨rfl, key_uses⟩ (fun high => table_uses _)⟩

theorem selectGuardPower_usesRadix (depth : ℕ) (key : Term n) (table : Fin (3 ^ depth) → Guard n)
    (key_uses : UsesRadix 3 key) (table_uses : ∀ index, Guard.UsesRadix 3 (table index)) :
    Guard.UsesRadix 3 (selectGuardPower depth key table) := by
  induction depth generalizing key with
  | zero => exact table_uses 0
  | succ depth correct =>
      exact ⟨rfl, key_uses, fun low =>
        correct (.descend 2 key) (fun high => table (join depth low high))
          ⟨rfl, key_uses⟩ (fun high => table_uses _)⟩

theorem quotientPower_usesRadix (depth : ℕ) (key : Term n) (key_uses : UsesRadix 3 key) :
    UsesRadix 3 (quotientPower depth key) := by
  induction depth generalizing key with
  | zero => exact key_uses
  | succ depth correct => exact correct (.descend 2 key) ⟨rfl, key_uses⟩

end Ternary

end Monodromy.CoverExpressions

namespace Monodromy.CoverExpressions

variable {n radix : ℕ}

/-- The analytic stopping indicator uses the same cover as its finite guard. -/
theorem Guard.compile_usesRadix (guard : Guard n) (uses : guard.UsesRadix radix) :
    CoverExpressions.UsesRadix radix guard.compile := by
  induction guard with
  | constant => trivial
  | select B key branches correct =>
      exact ⟨uses.1, uses.2.1, fun index => correct index (uses.2.2 index)⟩

/-- Internal guarding preserves the cover degree of every executed expression. -/
theorem Guard.gate_usesRadix (guard : Guard n) (yes no : Term n)
    (guard_uses : guard.UsesRadix radix) (yes_uses : CoverExpressions.UsesRadix radix yes)
    (no_uses : CoverExpressions.UsesRadix radix no) :
    CoverExpressions.UsesRadix radix (guard.gate yes no) := by
  induction guard with
  | constant value => cases value <;> assumption
  | select B key branches correct =>
      exact ⟨guard_uses.1, guard_uses.2.1, fun index => correct index (guard_uses.2.2 index)⟩

end Monodromy.CoverExpressions
