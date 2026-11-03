module

public import Monodromy.Scaling
public import Monodromy.Cubic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# A cubic observation of word memory

The cosine scaling equation supplies a second analytic digit readout.
Its entire retained real line lies over regular values of the cubic.
-/

@[expose] public section

namespace Monodromy.Scaling.Cosine

noncomputable def f (z : ℂ) : ℂ := 2 * Complex.cos z

noncomputable def period : ℂ := 2 * (Real.pi : ℂ)

theorem periodic : Function.Periodic f period := by
  intro z
  simp [f, period, Complex.cos_add_two_pi]

theorem scaling (z : ℂ) : Cubic.polynomial.eval (f z) = f ((3 : ℂ) * z) := by
  rw [Cubic.eval_polynomial]
  have triple := Complex.cos_three_mul z
  dsimp [f]
  linear_combination -2 * triple

theorem entire (z : ℂ) : AnalyticAt ℂ f z :=
  analyticAt_const.mul Complex.analyticAt_cos

theorem roots_eq (digit : Fin 3) :
    Scaling.roots f period Complex.I 3 digit = Cubic.root Complex.I digit := by
  unfold Scaling.roots f period Cubic.root
  congr 2
  push_cast
  ring

theorem sin_line_ne_zero (t : ℝ) : Complex.sin (Complex.I + t) ≠ 0 := by
  intro zero
  obtain ⟨n, same⟩ := Complex.sin_eq_zero_iff.mp zero
  have imaginary := congrArg Complex.im same
  norm_num at imaginary

theorem base_regular (t : ℝ) : f (Complex.I + t) ∈ Cubic.regular := by
  have sine := sin_line_ne_zero t
  simp only [Cubic.regular, Set.mem_compl_iff, Set.mem_insert_iff,
    Set.mem_singleton_iff, not_or]
  constructor <;> intro same <;> apply sine
  · apply Complex.sin_eq_zero_iff_cos_eq.mpr
    left
    dsimp [f] at same
    linear_combination (1 / 2 : ℂ) * same
  · apply Complex.sin_eq_zero_iff_cos_eq.mpr
    right
    dsimp [f] at same
    linear_combination (1 / 2 : ℂ) * same

theorem distinct : Function.Injective (Scaling.roots f period Complex.I 3) := by
  intro first second same
  apply Cubic.root_injective (by simpa using sin_line_ne_zero 0)
  simpa only [roots_eq] using same

theorem regular (digit : Fin 3) :
    deriv Cubic.polynomial.eval (Scaling.roots f period Complex.I 3 digit) ≠ 0 := by
  intro zero
  have critical : Cubic.polynomial.eval (Scaling.roots f period Complex.I 3 digit) ∈
      ({2, -2} : Set ℂ) := by
    apply Cubic.critical_values
    refine ⟨Scaling.roots f period Complex.I 3 digit, ?_, rfl⟩
    exact ((Cubic.polynomial.hasDerivAt _).deriv.symm.trans zero)
  rw [Scaling.roots_fiber f period Complex.I 3 Cubic.polynomial.eval
    periodic scaling digit] at critical
  have safe : f Complex.I ∉ ({2, -2} : Set ℂ) := by
    simpa [Cubic.regular] using base_regular 0
  exact safe critical

theorem period_normalized (x : ℝ) :
    period * (((x / (2 * Real.pi) : ℝ) : ℂ)) = (x : ℂ) := by
  unfold period
  push_cast
  field_simp

theorem rootAt_eq (x : ℝ) :
    Scaling.rootAt f period Complex.I 3 x = f ((Complex.I + x) / 3) := by
  unfold Scaling.rootAt
  rw [period_normalized]
  norm_num

/-- The full real coordinate line generates paths in the cubic's regular base. -/
theorem safe (x : ℝ) :
    f (Complex.I + period * (((x / (2 * Real.pi) : ℝ) : ℂ))) ∈ Cubic.regular := by
  rw [period_normalized]
  exact base_regular x

end Monodromy.Scaling.Cosine

namespace Monodromy.Scaling.Cosine

theorem continuous_f : Continuous f := by unfold f; fun_prop

theorem entire_projection (z : ℂ) : AnalyticAt ℂ Cubic.polynomial.eval z := by
  rw [show Cubic.polynomial.eval = (fun z : ℂ => z ^ 3 - 3 * z) by
    funext w
    exact Cubic.eval_polynomial w]
  exact (analyticAt_id.pow 3).sub (analyticAt_const.mul analyticAt_id)

/-- The cubic observation follows the very same retained real curve. -/
noncomputable def path (curve : C(unitInterval, ℝ)) :
    Path (⟨Scaling.baseAt f period Complex.I (curve 0), safe (curve 0)⟩ : Cubic.Base)
      (⟨Scaling.baseAt f period Complex.I (curve 1), safe (curve 1)⟩ : Cubic.Base) :=
  Continuation.basePath f period Complex.I Cubic.regular continuous_f curve (fun t => safe (curve t))

noncomputable def fiber (x : ℝ) :
    Transport.Fiber Cubic.projection (⟨Scaling.baseAt f period Complex.I x, safe x⟩ : Cubic.Base) :=
  Continuation.fiberRoot f period Complex.I 3 Cubic.polynomial.eval Cubic.regular scaling x (safe x)

/-- All retained curves have an actual cubic lift; the regular-value certificate is global. -/
theorem transport (curve : C(unitInterval, ℝ)) :
    Transport.transport Cubic.covering (path curve) (fiber (curve 0)) = fiber (curve 1) :=
  Continuation.transport_root f period Complex.I 3 Cubic.polynomial.eval Cubic.regular
    scaling continuous_f Cubic.covering curve (fun t => safe (curve t))

/-- Cubic and power-cover observations have the same execution on binary word memory. -/
theorem next_eq_native {q : ℕ} [NeZero q]
    (machine : Turing.TM0.Machine (Fin 2) (Fin q)) (memory : Machine.Memory 2 q) :
    Stack.next f period Complex.I Cubic.polynomial.eval machine memory.val =
      Machine.next machine memory.val :=
  Stack.next_eq_native f period Complex.I Cubic.polynomial.eval periodic scaling
    distinct regular machine memory

theorem analyticAt_next {q : ℕ} [NeZero q]
    (machine : Turing.TM0.Machine (Fin 2) (Fin q)) (point : Machine.State) :
    AnalyticAt ℝ (Stack.next f period Complex.I Cubic.polynomial.eval machine) point :=
  Stack.analyticAt_next f period Complex.I Cubic.polynomial.eval entire entire_projection machine point

end Monodromy.Scaling.Cosine
