module

public import Monodromy.Choice
public import Monodromy.Machine
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Algebra.Ring.Periodic

/-!
# Analytic digit readout from periodic scaling

A periodic analytic map and a scaling equation place the digit representatives
in one fiber. Distinct regular roots then provide analytic digit readout.
-/

@[expose] public section

namespace Monodromy.Scaling

variable (f : ℂ → ℂ) (period base : ℂ) (B : ℕ)

noncomputable def roots (digit : Fin B) : ℂ :=
  f ((base + period * (digit.val : ℂ)) / (B : ℂ))

noncomputable def rootAt (x : ℝ) : ℂ :=
  f ((base + period * ((x / (2 * Real.pi) : ℝ) : ℂ)) / (B : ℂ))

variable [NeZero B]

/-- Periodicity makes the lower-level root depend exactly on the radix digit. -/
theorem rootAt_digit (periodic : Function.Periodic f period) (n : ℤ) (digit : Fin B) :
    rootAt f period base B
      ((2 * Real.pi) * ((((B : ℤ) * n + digit.val : ℤ) : ℝ))) =
      roots f period base B digit := by
  have nonzero : (B : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne B
  have split :
      (base + period * (((B : ℤ) * n + digit.val : ℤ) : ℂ)) / (B : ℂ) =
        (base + period * (digit.val : ℂ)) / (B : ℂ) + (n : ℂ) * period := by
    push_cast
    field_simp [nonzero]
    ring
  unfold rootAt roots
  rw [mul_div_cancel_left₀ _ (mul_ne_zero two_ne_zero Real.pi_ne_zero)]
  rw [show (((((B : ℤ) * n + digit.val : ℤ) : ℝ)) : ℂ) =
      (((B : ℤ) * n + digit.val : ℤ) : ℂ) by norm_cast]
  rw [split]
  exact periodic.int_mul n _

/-- The scaling equation places every selected root in one fiber. -/
theorem roots_fiber (P : ℂ → ℂ)
    (periodic : Function.Periodic f period)
    (scaling : ∀ z, P (f z) = f ((B : ℂ) * z)) (digit : Fin B) :
    P (roots f period base B digit) = f base := by
  unfold roots
  rw [scaling]
  have nonzero : (B : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne B
  rw [mul_div_cancel₀ _ nonzero]
  simpa only [mul_comm period (digit.val : ℂ)] using periodic.nat_mul digit.val base

noncomputable def choose (P : ℂ → ℂ) (values : Fin B → ℝ) (x : ℝ) : ℝ :=
  (Choice.dispatch P (roots f period base B) (fun digit => (values digit : ℂ))
    (rootAt f period base B x)).re

theorem choose_digit (P : ℂ → ℂ)
    (periodic : Function.Periodic f period)
    (scaling : ∀ z, P (f z) = f ((B : ℂ) * z))
    (distinct : Function.Injective (roots f period base B))
    (regular : ∀ digit, deriv P (roots f period base B digit) ≠ 0)
    (values : Fin B → ℝ) (n : ℤ) (digit : Fin B) :
    choose f period base B P values
      ((2 * Real.pi) * ((((B : ℤ) * n + digit.val : ℤ) : ℝ))) = values digit := by
  unfold choose
  rw [rootAt_digit f period base B periodic]
  have same_fiber (first second : Fin B) :
      P (roots f period base B first) = P (roots f period base B second) :=
    (roots_fiber f period base B P periodic scaling first).trans
      (roots_fiber f period base B P periodic scaling second).symm
  rw [Choice.dispatch_root distinct same_fiber regular]
  rfl

omit [NeZero B] in
/-- Entire defining maps give an analytic readout on the whole real line. -/
theorem analyticAt_choose (P : ℂ → ℂ)
    (entire_f : ∀ z, AnalyticAt ℂ f z) (entire_P : ∀ z, AnalyticAt ℂ P z)
    (values : Fin B → ℝ) (x : ℝ) :
    AnalyticAt ℝ (choose f period base B P values) x := by
  have affine : AnalyticAt ℂ
      (fun z : ℂ => (base + period * (z / ((2 * Real.pi : ℝ) : ℂ))) / (B : ℂ)) (x : ℂ) :=
    (analyticAt_const.add (analyticAt_const.mul (analyticAt_id.div_const))).div_const
  have root_analytic : AnalyticAt ℂ
      (fun z : ℂ => f ((base + period * (z / ((2 * Real.pi : ℝ) : ℂ))) / (B : ℂ))) (x : ℂ) :=
    (entire_f _).comp affine
  have analytic : AnalyticAt ℂ
      (fun z : ℂ => Choice.dispatch P (roots f period base B) (fun digit => (values digit : ℂ))
        (f ((base + period * (z / ((2 * Real.pi : ℝ) : ℂ))) / (B : ℂ)))) (x : ℂ) :=
    (Choice.analyticAt_dispatch entire_P _ _ _).comp root_analytic
  change AnalyticAt ℝ (fun y : ℝ =>
    (Choice.dispatch P (roots f period base B) (fun digit => (values digit : ℂ))
      (f ((base + period * ((y / (2 * Real.pi) : ℝ) : ℂ)) / (B : ℂ)))).re) x
  simpa only [Complex.ofReal_div] using analytic.re_ofReal

end Monodromy.Scaling

namespace Monodromy.Scaling

variable (f : ℂ → ℂ) (period base : ℂ) (B : ℕ) [NeZero B]

noncomputable def baseAt (x : ℝ) : ℂ :=
  f (base + period * ((x / (2 * Real.pi) : ℝ) : ℂ))

omit [NeZero B] in
theorem baseAt_sheet (periodic : Function.Periodic f period) (n : ℤ) :
    baseAt f period base ((2 * Real.pi) * (n : ℝ)) = f base := by
  unfold baseAt
  rw [mul_div_cancel_left₀ _ (mul_ne_zero two_ne_zero Real.pi_ne_zero)]
  simpa only [Complex.ofReal_intCast, mul_comm period (n : ℂ)] using periodic.int_mul n base

theorem rootAt_projects (P : ℂ → ℂ)
    (scaling : ∀ z, P (f z) = f ((B : ℂ) * z)) (x : ℝ) :
    P (rootAt f period base B x) = baseAt f period base x := by
  unfold rootAt baseAt
  rw [scaling, mul_div_cancel₀ _ (show (B : ℂ) ≠ 0 by exact_mod_cast NeZero.ne B)]

namespace Continuation

variable (P : ℂ → ℂ) (target : Set ℂ)
  (scaling : ∀ z, P (f z) = f ((B : ℂ) * z))

abbrev Space := P ⁻¹' target

def projection : Space P target → target := target.restrictPreimage P

/-- The lower-level observation is retained as a point of the actual fiber. -/
noncomputable def fiberRoot (x : ℝ) (safe : baseAt f period base x ∈ target) :
    Transport.Fiber (projection P target) (⟨baseAt f period base x, safe⟩ : target) := by
  refine ⟨⟨rootAt f period base B x, ?_⟩, ?_⟩
  · change P (rootAt f period base B x) ∈ target
    rw [rootAt_projects f period base B P scaling]
    exact safe
  · apply Subtype.ext
    exact rootAt_projects f period base B P scaling x

variable (continuous : Continuous f)

/-- The upper path is generated from the same retained curve as the root observation. -/
noncomputable def basePath (curve : C(unitInterval, ℝ))
    (safe : ∀ t, baseAt f period base (curve t) ∈ target) :
    Path (⟨baseAt f period base (curve 0), safe 0⟩ : target)
      (⟨baseAt f period base (curve 1), safe 1⟩ : target) where
  toFun t := ⟨baseAt f period base (curve t), safe t⟩
  continuous_toFun := by unfold baseAt; fun_prop
  source' := rfl
  target' := rfl

noncomputable def rootCurve (curve : C(unitInterval, ℝ))
    (safe : ∀ t, baseAt f period base (curve t) ∈ target) :
    C(unitInterval, Space P target) where
  toFun t := (fiberRoot f period base B P target scaling (curve t) (safe t)).val
  continuous_toFun := by
    apply Continuous.subtype_mk
    change Continuous (fun t : unitInterval => rootAt f period base B (curve t))
    unfold rootAt
    fun_prop

/-- The scaling equation gives actual covering transport along every admissible curve. -/
theorem transport_root (covering : IsCoveringMap (projection P target))
    (curve : C(unitInterval, ℝ))
    (safe : ∀ t, baseAt f period base (curve t) ∈ target) :
    Transport.transport covering (basePath f period base target continuous curve safe)
      (fiberRoot f period base B P target scaling (curve 0) (safe 0)) =
      fiberRoot f period base B P target scaling (curve 1) (safe 1) := by
  apply Subtype.ext
  exact Transport.transport_eq_actual_lift covering
    (basePath f period base target continuous curve safe)
    (fiberRoot f period base B P target scaling (curve 0) (safe 0))
    (rootCurve f period base B P target scaling continuous curve safe)
    (funext fun t => Subtype.ext (rootAt_projects f period base B P scaling (curve t))) rfl

end Continuation

end Monodromy.Scaling

namespace Monodromy.Scaling.Stack

variable (f : ℂ → ℂ) (period base : ℂ) (P : ℂ → ℂ)

theorem choose_word {a : ℕ}
    (periodic : Function.Periodic f period)
    (scaling : ∀ z, P (f z) = f (((a + 1 : ℕ) : ℂ) * z))
    (distinct : Function.Injective (Scaling.roots f period base (a + 1)))
    (regular : ∀ digit, deriv P (Scaling.roots f period base (a + 1) digit) ≠ 0)
    (values : Fin (a + 1) → ℝ) (word : List (Fin a)) :
    Scaling.choose f period base (a + 1) P values (Radix.Stack.wordAngle word) =
      values (Radix.Stack.headDigit word) := by
  rw [Radix.Stack.wordAngle_digit]
  exact Scaling.choose_digit f period base (a + 1) P periodic scaling distinct regular values
    (Radix.Words.encode word.tail : ℤ) (Radix.Stack.headDigit word)

/-- The finite observation removes one digit before the next rescaling. -/
noncomputable def pop (a : ℕ) (x : ℝ) : ℝ :=
  (x - (2 * Real.pi) * Scaling.choose f period base (a + 1) P
    (fun digit => (digit.val : ℝ)) x) / ((a + 1 : ℕ) : ℝ)

theorem pop_word {a : ℕ}
    (periodic : Function.Periodic f period)
    (scaling : ∀ z, P (f z) = f (((a + 1 : ℕ) : ℂ) * z))
    (distinct : Function.Injective (Scaling.roots f period base (a + 1)))
    (regular : ∀ digit, deriv P (Scaling.roots f period base (a + 1) digit) ≠ 0)
    (word : List (Fin a)) :
    pop f period base P a (Radix.Stack.wordAngle word) = Radix.Stack.wordAngle word.tail := by
  unfold pop
  rw [choose_word f period base P periodic scaling distinct regular]
  apply (div_eq_iff (show ((a + 1 : ℕ) : ℝ) ≠ 0 by exact_mod_cast Nat.succ_ne_zero a)).mpr
  rw [Radix.Stack.wordAngle_digit]
  unfold Radix.Stack.wordAngle
  push_cast
  ring

theorem analyticAt_pop (a : ℕ)
    (entire_f : ∀ z, AnalyticAt ℂ f z) (entire_P : ∀ z, AnalyticAt ℂ P z) (x : ℝ) :
    AnalyticAt ℝ (pop f period base P a) x :=
  (analyticAt_id.sub (analyticAt_const.mul
    (Scaling.analyticAt_choose f period base (a + 1) P entire_f entire_P _ x))).div_const

variable {a q : ℕ} [NeZero a] [NeZero q]

/-- Only the analytic primitives read the current real-valued branch state. -/
noncomputable def next (machine : Turing.TM0.Machine (Fin a) (Fin q))
    (point : Machine.State) : Machine.State :=
  Machine.Scheme.next Radix.Stack.push (pop f period base P a)
    (Scaling.choose f period base (a + 1) P) machine point

theorem next_encode
    (periodic : Function.Periodic f period)
    (scaling : ∀ z, P (f z) = f (((a + 1 : ℕ) : ℂ) * z))
    (distinct : Function.Injective (Scaling.roots f period base (a + 1)))
    (regular : ∀ digit, deriv P (Scaling.roots f period base (a + 1) digit) ≠ 0)
    (machine : Turing.TM0.Machine (Fin a) (Fin q))
    (configuration : TwoStacks.Configuration (Fin a) (Fin q)) :
    next f period base P machine (Machine.encode configuration) =
      Machine.encode ((TwoStacks.step machine configuration).getD configuration) := by
  have reads (values : Fin a → ℝ) (word : List (Fin a)) :
      Machine.Scheme.readHead (Scaling.choose f period base (a + 1) P) values
        (Radix.Stack.wordAngle word) = values word.headI := by
    unfold Machine.Scheme.readHead
    rw [choose_word f period base P periodic scaling distinct regular]
    cases word <;> rfl
  exact Machine.Scheme.next_encode Radix.Stack.wordAngle Radix.Stack.push (pop f period base P a)
    (Scaling.choose f period base (a + 1) P) Radix.Stack.push_word
    (pop_word f period base P periodic scaling distinct regular) reads machine configuration

theorem analyticAt_next
    (entire_f : ∀ z, AnalyticAt ℂ f z) (entire_P : ∀ z, AnalyticAt ℂ P z)
    (machine : Turing.TM0.Machine (Fin a) (Fin q)) (point : Machine.State) :
    AnalyticAt ℝ (next f period base P machine) point :=
  Machine.Scheme.analyticAt_next Radix.Stack.push (pop f period base P a)
    (Scaling.choose f period base (a + 1) P) Radix.Stack.analyticAt_push
    (analyticAt_pop f period base P a entire_f entire_P)
    (Scaling.analyticAt_choose f period base (a + 1) P entire_f entire_P) machine point

/-- Different periodic analytic realizations execute the same legal branch states. -/
theorem next_eq_native
    (periodic : Function.Periodic f period)
    (scaling : ∀ z, P (f z) = f (((a + 1 : ℕ) : ℂ) * z))
    (distinct : Function.Injective (Scaling.roots f period base (a + 1)))
    (regular : ∀ digit, deriv P (Scaling.roots f period base (a + 1) digit) ≠ 0)
    (machine : Turing.TM0.Machine (Fin a) (Fin q)) (memory : Machine.Memory a q) :
    next f period base P machine memory.val = Machine.next machine memory.val := by
  obtain ⟨configuration, same⟩ := memory.property
  rw [← same, next_encode f period base P periodic scaling distinct regular]
  exact (Machine.next_encode machine configuration).symm

end Monodromy.Scaling.Stack

namespace Monodromy.Scaling.Exponential

noncomputable def period : ℂ := 2 * (Real.pi : ℂ) * Complex.I

theorem periodic : Function.Periodic Complex.exp period := Complex.exp_periodic

theorem scaling (B : ℕ) (z : ℂ) : Complex.exp z ^ B = Complex.exp ((B : ℂ) * z) :=
  (Complex.exp_nat_mul z B).symm

theorem roots_eq (B : ℕ) (digit : Fin B) :
    roots Complex.exp period 0 B digit = (Radix.omega B digit : ℂ) := by
  unfold roots period Radix.omega
  simp only [zero_add, Circle.coe_exp]
  congr 1
  push_cast
  ring

theorem rootAt_eq (B : ℕ) (x : ℝ) :
    rootAt Complex.exp period 0 B x = (Radix.readRoot B x : ℂ) := by
  have period_mul : period * ((x / (2 * Real.pi) : ℝ) : ℂ) = (x : ℂ) * Complex.I := by
    unfold period
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  unfold rootAt
  rw [zero_add, period_mul]
  simp only [Radix.readRoot, Circle.coe_exp]
  congr 1
  push_cast
  ring

theorem choose_eq (B : ℕ) [NeZero B] (values : Fin B → ℝ) (x : ℝ) :
    choose Complex.exp period 0 B (fun z : ℂ => z ^ B) values x =
      Radix.choose B values x := by
  unfold choose
  simp [Choice.dispatch, roots_eq, rootAt_eq, Radix.choose, Radix.weight, Complex.mul_re]

theorem roots_distinct (B : ℕ) [NeZero B] :
    Function.Injective (roots Complex.exp period 0 B) := by
  intro first second same
  apply Radix.omega_injective B
  exact Subtype.ext (by simpa only [roots_eq] using same)

theorem roots_regular (B : ℕ) [NeZero B] (digit : Fin B) :
    deriv (fun z : ℂ => z ^ B) (roots Complex.exp period 0 B digit) ≠ 0 := by
  simpa only [roots_eq] using Radix.omega_regular B digit

end Monodromy.Scaling.Exponential
