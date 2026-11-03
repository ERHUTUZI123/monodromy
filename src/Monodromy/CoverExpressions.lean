module

public import Monodromy.Radix
public import Monodromy.Resolution
public import Mathlib.Analysis.Analytic.Linear

/-!
# Finite expressions from cover observations

The integer interpretation specifies residue selection and Euclidean descent.
The real interpretation executes the same operations through cover kernels.
-/

@[expose] public section

namespace Monodromy.CoverExpressions

inductive Term (n : ℕ) : Type
  | coord (index : Fin n) : Term n
  | integerConst (value : ℤ) : Term n
  | add (first second : Term n) : Term n
  | integerScale (value : ℤ) (term : Term n) : Term n
  | select (B : ℕ) (key : Term n) (branches : Fin (B + 1) → Term n) : Term n
  | descend (B : ℕ) (key : Term n) : Term n

/-- A positive-base Euclidean remainder, represented as a finite digit. -/
def digit (B : ℕ) (value : ℤ) : Fin (B + 1) :=
  ⟨(value % ((B + 1 : ℕ) : ℤ)).toNat, by
    have lower := Int.emod_nonneg value (show ((B + 1 : ℕ) : ℤ) ≠ 0 by omega)
    have upper := Int.emod_lt_of_pos value (show 0 < ((B + 1 : ℕ) : ℤ) by omega)
    omega⟩

theorem digit_cast (B : ℕ) (value : ℤ) :
    ((digit B value).val : ℤ) = value % ((B + 1 : ℕ) : ℤ) :=
  Int.toNat_of_nonneg (Int.emod_nonneg value (by omega))

theorem decomposition (B : ℕ) (value : ℤ) :
    ((B + 1 : ℕ) : ℤ) * (value / ((B + 1 : ℕ) : ℤ)) + (digit B value).val = value := by
  rw [digit_cast]
  exact Int.mul_ediv_add_emod value ((B + 1 : ℕ) : ℤ)

theorem choose_integer (B : ℕ) (values : Fin (B + 1) → ℝ) (value : ℤ) :
    Radix.choose (B + 1) values ((2 * Real.pi) * (value : ℝ)) = values (digit B value) := by
  have angle := congrArg (fun k : ℤ => (2 * Real.pi) * (k : ℝ)) (decomposition B value).symm
  rw [angle]
  exact Radix.choose_digit (B + 1) values (value / ((B + 1 : ℕ) : ℤ)) (digit B value)

theorem quotient_real (B : ℕ) (value : ℤ) :
    ((value : ℝ) - ((digit B value).val : ℝ)) / ((B + 1 : ℕ) : ℝ) =
      ((value / ((B + 1 : ℕ) : ℤ) : ℤ) : ℝ) := by
  apply (div_eq_iff (show ((B + 1 : ℕ) : ℝ) ≠ 0 by exact_mod_cast Nat.succ_ne_zero B)).mpr
  have real_decomposition :
      ((B + 1 : ℕ) : ℝ) * ((value / ((B + 1 : ℕ) : ℤ) : ℤ) : ℝ) +
        ((digit B value).val : ℝ) = (value : ℝ) := by
    exact_mod_cast decomposition B value
  nlinarith [real_decomposition]

variable {n : ℕ}

def evalInt : Term n → (Fin n → ℤ) → ℤ
  | .coord index, point => point index
  | .integerConst value, _ => value
  | .add first second, point => evalInt first point + evalInt second point
  | .integerScale value term, point => value * evalInt term point
  | .select B key branches, point => evalInt (branches (digit B (evalInt key point))) point
  | .descend B key, point => evalInt key point / ((B + 1 : ℕ) : ℤ)

noncomputable def evalReal : Term n → (Fin n → ℝ) → ℝ
  | .coord index, point => point index
  | .integerConst value, _ => value
  | .add first second, point => evalReal first point + evalReal second point
  | .integerScale value term, point => (value : ℝ) * evalReal term point
  | .select B key branches, point =>
      Radix.choose (B + 1) (fun index => evalReal (branches index) point)
        ((2 * Real.pi) * evalReal key point)
  | .descend B key, point =>
      (evalReal key point - Radix.choose (B + 1) (fun index => (index.val : ℝ))
          ((2 * Real.pi) * evalReal key point)) / ((B + 1 : ℕ) : ℝ)

/-- Each finite expression's cover interpretation realizes its exact integer semantics. -/
theorem evalReal_int (term : Term n) (point : Fin n → ℤ) :
    evalReal term (fun index => (point index : ℝ)) = (evalInt term point : ℝ) := by
  induction term with
  | coord => rfl
  | integerConst => rfl
  | add first second first_correct second_correct =>
      simp only [evalReal, evalInt, first_correct, second_correct, Int.cast_add]
  | integerScale value term correct =>
      simp only [evalReal, evalInt, correct, Int.cast_mul]
  | select B key branches key_correct branches_correct =>
      simp only [evalReal, evalInt, key_correct]
      rw [choose_integer]
      exact branches_correct _
  | descend B key key_correct =>
      simp only [evalReal, evalInt, key_correct]
      rw [choose_integer]
      exact quotient_real B (evalInt key point)

/-- Cover observations and arithmetic make every finite expression jointly real analytic. -/
theorem analyticAt_evalReal (term : Term n) (point : Fin n → ℝ) :
    AnalyticAt ℝ (evalReal term) point := by
  induction term with
  | coord index => exact (ContinuousLinearMap.proj (R := ℝ) index).analyticAt point
  | integerConst => exact analyticAt_const
  | add first second first_analytic second_analytic => exact first_analytic.add second_analytic
  | integerScale value term analytic => exact analyticAt_const.mul analytic
  | select B key branches key_analytic branches_analytic =>
      change AnalyticAt ℝ (fun p : Fin n → ℝ =>
        ∑ index, Radix.weight (B + 1) index ((2 * Real.pi) * evalReal key p) *
          evalReal (branches index) p) point
      exact Finset.analyticAt_fun_sum Finset.univ (fun index _ =>
        ((Radix.analyticAt_weight (B + 1) index _).comp
          (f := fun p : Fin n → ℝ => (2 * Real.pi) * evalReal key p)
          (analyticAt_const.mul key_analytic)).mul (branches_analytic index))
  | descend B key key_analytic =>
      change AnalyticAt ℝ (fun p : Fin n → ℝ =>
        (evalReal key p - Radix.choose (B + 1) (fun index => (index.val : ℝ))
            ((2 * Real.pi) * evalReal key p)) / ((B + 1 : ℕ) : ℝ)) point
      exact (key_analytic.sub
        ((Radix.analyticAt_choose (B + 1) (fun index => (index.val : ℝ)) _).comp
          (f := fun p : Fin n → ℝ => (2 * Real.pi) * evalReal key p)
          (analyticAt_const.mul key_analytic))).div_const

end Monodromy.CoverExpressions

namespace Monodromy.CoverExpressions

variable {n : ℕ}

inductive Supported (M : ℤ) : Term n → Prop
  | coord (index : Fin n) : Supported M (.coord index)
  | integerConst (value : ℤ) : Supported M (.integerConst value)
  | add (first second : Term n) (first_supported : Supported M first)
      (second_supported : Supported M second) : Supported M (.add first second)
  | integerScale (value : ℤ) (term : Term n) (supported : Supported M term) :
      Supported M (.integerScale value term)
  | select (B : ℕ) (key : Term n) (branches : Fin (B + 1) → Term n)
      (divides : ((B + 1 : ℕ) : ℤ) ∣ M) (key_supported : Supported M key)
      (branches_supported : ∀ index, Supported M (branches index)) :
      Supported M (.select B key branches)

/-- Refining a supported observation preserves its syntactic certificate. -/
theorem Supported.mono {M N : ℤ} {term : Term n} (supported : Supported M term)
    (refines : M ∣ N) : Supported N term := by
  induction supported with
  | coord index => exact Supported.coord index
  | integerConst value => exact Supported.integerConst value
  | add first second _ _ first_ih second_ih =>
      exact Supported.add first second first_ih second_ih
  | integerScale value term _ ih => exact Supported.integerScale value term ih
  | select B key branches divides _ _ key_ih branches_ih =>
      exact Supported.select B key branches (divides.trans refines) key_ih branches_ih

/-- Supported expressions cannot distinguish coordinate states in the same finite quotient. -/
theorem Supported.modEq {M : ℤ} {term : Term n} (supported : Supported M term)
    {first second : Fin n → ℤ} (same : ∀ index, first index ≡ second index [ZMOD M]) :
    evalInt term first ≡ evalInt term second [ZMOD M] := by
  induction supported with
  | coord index => exact same index
  | integerConst => exact Int.ModEq.rfl
  | add _ _ _ _ first_ih second_ih => exact first_ih.add second_ih
  | integerScale value _ _ ih => exact ih.mul_left value
  | select B key branches divides _ _ key_ih branches_ih =>
      have equal_digit : digit B (evalInt key first) = digit B (evalInt key second) := by
        apply Fin.ext
        exact congrArg Int.toNat (key_ih.of_dvd divides).eq
      change evalInt (branches (digit B (evalInt key first))) first ≡
        evalInt (branches (digit B (evalInt key second))) second [ZMOD M]
      rw [equal_digit]
      exact branches_ih _

/-- The forward sublanguage uses arithmetic and residue readout, with no descent. -/
def Forward : Term n → Prop
  | .coord _ | .integerConst _ => True
  | .add first second => Forward first ∧ Forward second
  | .integerScale _ term => Forward term
  | .select _ key branches => Forward key ∧ ∀ index, Forward (branches index)
  | .descend _ _ => False

/-- A computable common observation for the forward sublanguage. -/
def forwardModulus : Term n → ℤ
  | .coord _ | .integerConst _ | .descend _ _ => 1
  | .add first second => forwardModulus first * forwardModulus second
  | .integerScale _ term => forwardModulus term
  | .select B key branches =>
      ((B + 1 : ℕ) : ℤ) * forwardModulus key * ∏ index, forwardModulus (branches index)

theorem forwardModulus_positive (term : Term n) : 0 < forwardModulus term := by
  induction term with
  | coord | integerConst | descend => exact zero_lt_one
  | add _ _ first_ih second_ih => exact mul_pos first_ih second_ih
  | integerScale _ _ ih => exact ih
  | select B _ _ key_ih branches_ih =>
      exact mul_pos (mul_pos (by exact_mod_cast Nat.succ_pos B) key_ih)
        (Finset.prod_pos (fun index _ => branches_ih index))

theorem forward_supported_modulus (term : Term n) (forward : Forward term) :
    Supported (forwardModulus term) term := by
  induction term with
  | coord index => exact Supported.coord index
  | integerConst value => exact Supported.integerConst value
  | add first second first_ih second_ih =>
      exact Supported.add first second
        ((first_ih forward.1).mono (dvd_mul_right _ _))
        ((second_ih forward.2).mono (dvd_mul_left _ _))
  | integerScale value term ih => exact Supported.integerScale value term (ih forward)
  | select B key branches key_ih branches_ih =>
      refine Supported.select B key branches ?_ ?_ ?_
      · exact ⟨forwardModulus key * ∏ index, forwardModulus (branches index), mul_assoc _ _ _⟩
      · apply (key_ih forward.1).mono
        refine ⟨((B + 1 : ℕ) : ℤ) * ∏ index, forwardModulus (branches index), ?_⟩
        dsimp [forwardModulus]
        ac_rfl
      · intro index
        exact ((branches_ih index) (forward.2 index)).mono
          ((Finset.dvd_prod_of_mem (fun branch => forwardModulus (branches branch))
            (Finset.mem_univ index)).trans (dvd_mul_left _ _))
  | descend => exact forward.elim

/-- Every finite forward expression has a positive closed observation. -/
theorem forward_supported (term : Term n) (forward : Forward term) :
    ∃ M : ℤ, 0 < M ∧ Supported M term :=
  ⟨forwardModulus term, forwardModulus_positive term, forward_supported_modulus term forward⟩

end Monodromy.CoverExpressions

namespace Monodromy.CoverExpressions

inductive Guard (n : ℕ) : Type
  | constant (value : Bool) : Guard n
  | select (B : ℕ) (key : Term n) (branches : Fin (B + 1) → Guard n) : Guard n

namespace Guard

variable {n : ℕ}

def evalInt : Guard n → (Fin n → ℤ) → Bool
  | .constant value, _ => value
  | .select B key branches, point =>
      evalInt (branches (digit B (CoverExpressions.evalInt key point))) point

def compile : Guard n → Term n
  | .constant value => .integerConst (if value then 1 else 0)
  | .select B key branches => .select B key (fun index => compile (branches index))

theorem eval_compile (guard : Guard n) (point : Fin n → ℤ) :
    CoverExpressions.evalInt (compile guard) point = if evalInt guard point then 1 else 0 := by
  induction guard with
  | constant value => cases value <;> rfl
  | select B key branches correct =>
      exact correct (digit B (CoverExpressions.evalInt key point))

/-- The guard's real indicator is built from the same finite cover expressions. -/
noncomputable def evalReal (guard : Guard n) : (Fin n → ℝ) → ℝ :=
  CoverExpressions.evalReal (compile guard)

theorem evalReal_int (guard : Guard n) (point : Fin n → ℤ) :
    evalReal guard (fun index => (point index : ℝ)) = if evalInt guard point then 1 else 0 := by
  unfold evalReal
  rw [CoverExpressions.evalReal_int, eval_compile]
  cases evalInt guard point <;> simp

theorem analyticAt_evalReal (guard : Guard n) (point : Fin n → ℝ) :
    AnalyticAt ℝ (evalReal guard) point := CoverExpressions.analyticAt_evalReal (compile guard) point

/-- Branching is compiled into finite cover observations inside the expression. -/
def gate : Guard n → Term n → Term n → Term n
  | .constant value, yes, no => if value then yes else no
  | .select B key branches, yes, no => .select B key (fun index => gate (branches index) yes no)

theorem eval_gate (guard : Guard n) (yes no : Term n) (point : Fin n → ℤ) :
    CoverExpressions.evalInt (gate guard yes no) point =
      if evalInt guard point then CoverExpressions.evalInt yes point else CoverExpressions.evalInt no point := by
  induction guard with
  | constant value => cases value <;> rfl
  | select B key branches correct =>
      exact correct (digit B (CoverExpressions.evalInt key point))

end Guard

end Monodromy.CoverExpressions

namespace Monodromy.CoverExpressions.Guard

variable {n : ℕ}

inductive Supported (M : ℤ) : Guard n → Prop
  | constant (value : Bool) : Supported M (.constant value)
  | select (B : ℕ) (key : Term n) (branches : Fin (B + 1) → Guard n)
      (divides : ((B + 1 : ℕ) : ℤ) ∣ M)
      (key_supported : CoverExpressions.Supported M key)
      (branches_supported : ∀ index, Supported M (branches index)) :
      Supported M (.select B key branches)

theorem Supported.mono {M N : ℤ} {guard : Guard n} (supported : Supported M guard)
    (refines : M ∣ N) : Supported N guard := by
  induction supported with
  | constant value => exact Supported.constant value
  | select B key branches divides key_supported _ branches_ih =>
      exact Supported.select B key branches (divides.trans refines)
        (key_supported.mono refines) branches_ih

/-- A supported guard makes exactly the same decision on congruent coordinate states. -/
theorem Supported.eval_eq {M : ℤ} {guard : Guard n} (supported : Supported M guard)
    {first second : Fin n → ℤ} (same : ∀ index, first index ≡ second index [ZMOD M]) :
    evalInt guard first = evalInt guard second := by
  induction supported with
  | constant => rfl
  | select B key branches divides key_supported _ branches_ih =>
      have equal_digit : digit B (CoverExpressions.evalInt key first) =
          digit B (CoverExpressions.evalInt key second) := by
        apply Fin.ext
        exact congrArg Int.toNat ((key_supported.modEq same).of_dvd divides).eq
      change evalInt (branches (digit B (CoverExpressions.evalInt key first))) first =
        evalInt (branches (digit B (CoverExpressions.evalInt key second))) second
      rw [equal_digit]
      exact branches_ih _

def Forward : Guard n → Prop
  | .constant _ => True
  | .select _ key branches => CoverExpressions.Forward key ∧ ∀ index, Forward (branches index)

/-- The guard's finite observation can be obtained from its syntax alone. -/
def forwardModulus : Guard n → ℤ
  | .constant _ => 1
  | .select B key branches =>
      ((B + 1 : ℕ) : ℤ) * CoverExpressions.forwardModulus key *
        ∏ index, forwardModulus (branches index)

theorem forwardModulus_positive (guard : Guard n) : 0 < forwardModulus guard := by
  induction guard with
  | constant => exact zero_lt_one
  | select B key _ branches_ih =>
      exact mul_pos (mul_pos (by exact_mod_cast Nat.succ_pos B)
        (CoverExpressions.forwardModulus_positive key))
        (Finset.prod_pos (fun index _ => branches_ih index))

theorem forward_supported_modulus (guard : Guard n) (forward : Forward guard) :
    Supported (forwardModulus guard) guard := by
  induction guard with
  | constant value => exact Supported.constant value
  | select B key branches branches_ih =>
      refine Supported.select B key branches ?_ ?_ ?_
      · exact ⟨CoverExpressions.forwardModulus key * ∏ index, forwardModulus (branches index),
          mul_assoc _ _ _⟩
      · apply (CoverExpressions.forward_supported_modulus key forward.1).mono
        refine ⟨((B + 1 : ℕ) : ℤ) * ∏ index, forwardModulus (branches index), ?_⟩
        dsimp [forwardModulus]
        ac_rfl
      · intro index
        exact ((branches_ih index) (forward.2 index)).mono
          ((Finset.dvd_prod_of_mem (fun branch => forwardModulus (branches branch))
            (Finset.mem_univ index)).trans (dvd_mul_left _ _))

/-- A finite forward guard is controlled by its computed residue observation. -/
theorem forward_supported (guard : Guard n) (forward : Forward guard) :
    ∃ M : ℤ, 0 < M ∧ Supported M guard :=
  ⟨forwardModulus guard, forwardModulus_positive guard, forward_supported_modulus guard forward⟩

end Monodromy.CoverExpressions.Guard

namespace Monodromy.CoverExpressions

variable {n : ℕ}

/-- A sufficient input modulus for a requested output modulus. -/
def demand : Term n → ℤ → ℤ
  | .coord _, m => m
  | .integerConst _, _ => 1
  | .add first second, m => demand first m * demand second m
  | .integerScale _ term, m => demand term m
  | .select B key branches, m =>
      demand key ((B + 1 : ℕ) : ℤ) * ∏ index, demand (branches index) m
  | .descend B key, m => demand key (((B + 1 : ℕ) : ℤ) * m)

theorem demand_positive (term : Term n) {m : ℤ} (positive : 0 < m) :
    0 < demand term m := by
  induction term generalizing m with
  | coord => exact positive
  | integerConst => exact zero_lt_one
  | add _ _ first_ih second_ih => exact mul_pos (first_ih positive) (second_ih positive)
  | integerScale _ _ ih => exact ih positive
  | select B _ _ key_ih branches_ih =>
      exact mul_pos (key_ih (by exact_mod_cast Nat.succ_pos B))
        (Finset.prod_pos (fun index _ => branches_ih index positive))
  | descend B _ ih =>
      exact ih (mul_pos (by exact_mod_cast Nat.succ_pos B) positive)

/-- No expression needs infinitely many input digits for a fixed output observation. -/
theorem evalInt_modEq_demand (term : Term n) (m : ℤ) {first second : Fin n → ℤ}
    (same : ∀ index, first index ≡ second index [ZMOD demand term m]) :
    evalInt term first ≡ evalInt term second [ZMOD m] := by
  induction term generalizing m with
  | coord index => exact same index
  | integerConst => exact Int.ModEq.rfl
  | add first_term second_term first_ih second_ih =>
      exact (first_ih m (fun index =>
        (same index).of_dvd (dvd_mul_right _ _))).add
        (second_ih m (fun index => (same index).of_dvd (dvd_mul_left _ _)))
  | integerScale value _ ih => exact (ih m same).mul_left value
  | select B key branches key_ih branches_ih =>
      have key_same : evalInt key first ≡ evalInt key second [ZMOD ((B + 1 : ℕ) : ℤ)] :=
        key_ih _ (fun index => (same index).of_dvd (dvd_mul_right _ _))
      have digit_same : digit B (evalInt key first) = digit B (evalInt key second) := by
        apply Fin.ext
        exact congrArg Int.toNat key_same.eq
      change evalInt (branches (digit B (evalInt key first))) first ≡
        evalInt (branches (digit B (evalInt key second))) second [ZMOD m]
      rw [digit_same]
      apply branches_ih
      intro index
      exact (same index).of_dvd
        ((Finset.dvd_prod_of_mem (fun branch => demand (branches branch) m)
          (Finset.mem_univ _)).trans (dvd_mul_left _ _))
  | descend B key ih =>
      exact Resolution.tail_modEq ((B + 1 : ℕ) : ℤ) (by exact_mod_cast Nat.succ_ne_zero B)
        (ih _ same)

end Monodromy.CoverExpressions
