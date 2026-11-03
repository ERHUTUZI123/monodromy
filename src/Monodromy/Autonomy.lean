module

public import Monodromy.Logarithm
public import Monodromy.Choice
public import Mathlib.Dynamics.Flow
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# A state generating its own continuation path

The exponential equation's normalized divided difference supplies an internal
real analytic observation. A fixed write-read rule generates its own paths,
carries its roots, and changes the state that determines its next response.
-/

@[expose] public section

namespace Monodromy.Logarithm

noncomputable def zeroWeight (x : ℝ) : ℝ := Real.sinc (x / 2) ^ 2

theorem continuous_zeroWeight : Continuous zeroWeight :=
  (Real.continuous_sinc.comp (continuous_id.div_const 2)).pow 2

theorem zeroWeight_sheet (k : ℤ) :
    zeroWeight ((k : ℝ) * (2 * Real.pi)) = if k = 0 then 1 else 0 := by
  by_cases zero : k = 0
  · simp [zeroWeight, zero]
  · have nonzero : (k : ℝ) * Real.pi ≠ 0 :=
      mul_ne_zero (Int.cast_ne_zero.mpr zero) Real.pi_ne_zero
    have half : (k : ℝ) * (2 * Real.pi) / 2 = (k : ℝ) * Real.pi := by ring
    simp [zeroWeight, half, Real.sinc_of_ne_zero nonzero, Real.sin_int_mul_pi, zero]

private theorem analyticAt_sinc (x : ℝ) : AnalyticAt ℝ Real.sinc x := by
  by_cases zero : x = 0
  · subst x
    rw [Real.sinc_eq_dslope]
    obtain ⟨series, analytic⟩ := (Real.analyticAt_sin : AnalyticAt ℝ Real.sin 0)
    exact ⟨series.fslope, analytic.has_fpower_series_dslope_fslope⟩
  · have analytic : AnalyticAt ℝ (fun y : ℝ => Real.sin y / y) x :=
      Real.analyticAt_sin.div analyticAt_id zero
    apply analytic.congr
    filter_upwards [isOpen_ne.mem_nhds zero] with y nonzero
    exact (Real.sinc_of_ne_zero nonzero).symm

theorem analyticAt_zeroWeight (x : ℝ) : AnalyticAt ℝ zeroWeight x :=
  ((analyticAt_sinc (x / 2)).comp (f := fun y : ℝ => y / 2)
    (analyticAt_id.div_const : AnalyticAt ℝ (fun y : ℝ => y / 2) x)).pow 2

/-- The real weight is the squared norm of the exponential equation's own selector. -/
theorem zeroWeight_eq_kernel (x : ℝ) :
    zeroWeight x = Complex.normSq (Choice.kernel Complex.exp 0 ((x : ℂ) * Complex.I)) := by
  symm
  by_cases zero : x = 0
  · subst x
    simp [zeroWeight, Choice.kernel, Complex.deriv_exp]
  have imaginary_ne : (x : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr zero) Complex.I_ne_zero
  have chord : ‖Complex.exp ((x : ℂ) * Complex.I) - 1‖ = ‖2 * Real.sin (x / 2)‖ := by
    simpa only [mul_comm Complex.I (x : ℂ)] using
      Complex.norm_exp_I_mul_ofReal_sub_one x
  rw [Choice.kernel, Complex.deriv_exp, Complex.exp_zero, div_one,
    dslope_of_ne _ imaginary_ne, slope_def_field, sub_zero, Complex.exp_zero,
    Complex.normSq_eq_norm_sq, norm_div, norm_mul, Complex.norm_real,
    Complex.norm_I, mul_one, chord, zeroWeight,
    Real.sinc_of_ne_zero (div_ne_zero zero two_ne_zero)]
  simp only [Real.norm_eq_abs, div_pow, sq_abs]
  field_simp

end Monodromy.Logarithm

namespace Monodromy.Autonomy

noncomputable def response (x : ℝ) : ℝ := 2 * Logarithm.zeroWeight x - 1

theorem continuous_response : Continuous response := by
  unfold response
  exact (continuous_const.mul Logarithm.continuous_zeroWeight).sub continuous_const

theorem analyticAt_response (x : ℝ) : AnalyticAt ℝ response x :=
  (analyticAt_const.mul (Logarithm.analyticAt_zeroWeight x)).sub analyticAt_const

/-- The path generator and the carried state share one fixed evolution law. -/
noncomputable def flow : Flow ℝ (ℝ × ℝ) where
  toFun t state := (state.1, state.2 + t * response state.1)
  cont' := continuous_snd.fst.prodMk
    (continuous_snd.snd.add (continuous_fst.mul (continuous_response.comp continuous_snd.fst)))
  map_add' s t state := by
    apply Prod.ext
    · rfl
    · dsimp
      ring
  map_zero' state := by simp

theorem flow_hasDerivAt (state : ℝ × ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (flow s state).2) (response state.1) t := by
  change HasDerivAt (fun s : ℝ => state.2 + s * response state.1) _ t
  simpa only [id_eq, one_mul] using
    ((hasDerivAt_id t).mul_const (response state.1)).const_add state.2

theorem response_sheet (k : ℤ) :
    response (Logarithm.sheet k : ℝ) = if k = 0 then 1 else -1 := by
  unfold response Logarithm.sheet
  rw [Logarithm.zeroWeight_sheet]
  split_ifs <;> norm_num

theorem flow_period (k l : ℤ) :
    flow (2 * Real.pi) ((Logarithm.sheet k : ℝ), (Logarithm.sheet l : ℝ)) =
      ((Logarithm.sheet k : ℝ),
       (Logarithm.sheet (l + if k = 0 then 1 else -1) : ℝ)) := by
  apply Prod.ext
  · rfl
  · change (Logarithm.sheet l : ℝ) + 2 * Real.pi * response (Logarithm.sheet k : ℝ) = _
    rw [response_sheet]
    split_ifs <;> simp [Logarithm.sheet] <;> ring

/-- The control is the projection of the system's own continuous trajectory. -/
noncomputable def path (k l : ℤ) : Path (1 : Circle) 1 where
  toFun t := Circle.exp
    (flow (2 * Real.pi * (t : ℝ)) ((Logarithm.sheet k : ℝ), (Logarithm.sheet l : ℝ))).2
  continuous_toFun := by fun_prop
  source' := by simp [Logarithm.sheet]
  target' := by
    change Circle.exp
      (flow (2 * Real.pi * 1) ((Logarithm.sheet k : ℝ), (Logarithm.sheet l : ℝ))).2 = 1
    rw [mul_one, flow_period]
    exact (Logarithm.sheet _).2

theorem path_eq_turn (k l : ℤ) :
    path k l = Logarithm.turn (if k = 0 then 1 else -1) := by
  apply Path.ext
  funext t
  change Circle.exp ((Logarithm.sheet l : ℝ) +
    (2 * Real.pi * (t : ℝ)) * response (Logarithm.sheet k : ℝ)) = _
  rw [Circle.exp_add, (Logarithm.sheet l).2, one_mul, response_sheet]
  split_ifs <;> simp [Logarithm.turn] <;> congr 1 <;> ring

/-- The internal response selects the operation, and its own lift executes it. -/
theorem transport_path (k l : ℤ) :
    Transport.transport Circle.isCoveringMap_exp (path k l) (Logarithm.sheet l) =
      Logarithm.sheet (l + if k = 0 then 1 else -1) := by
  rw [path_eq_turn]
  exact Logarithm.transport_turn _ _

theorem operations_differ (l : ℤ) :
    Transport.transport Circle.isCoveringMap_exp (path 0 l) (Logarithm.sheet l) ≠
      Transport.transport Circle.isCoveringMap_exp (path 1 l) (Logarithm.sheet l) := by
  rw [transport_path, transport_path]
  intro same
  have indices := Logarithm.integers.injective same
  simp at indices

noncomputable def write (t : ℝ) (state : ℝ × ℝ) : ℝ × ℝ :=
  (flow t state.swap).swap

/-- One fixed discrete return map writes, then reads the updated state. -/
noncomputable def next (state : ℝ × ℝ) : ℝ × ℝ :=
  flow (2 * Real.pi) (write (2 * Real.pi) state)

noncomputable def state (k l : ℤ) : ℝ × ℝ :=
  ((Logarithm.sheet k : ℝ), (Logarithm.sheet l : ℝ))

/-- A description of the integer action, derived from the analytic response. -/
def direction (k : ℤ) : ℤ := if k = 0 then 1 else -1

theorem next_sheet (k l : ℤ) :
    next (state k l) = state (k + direction l) (l + direction (k + direction l)) := by
  unfold next write state direction
  change flow (2 * Real.pi)
    (flow (2 * Real.pi) ((Logarithm.sheet l : ℝ), (Logarithm.sheet k : ℝ))).swap = _
  rw [flow_period]
  exact flow_period _ _

/-- Both stages are the actual lifts of the paths generated by their internal states. -/
theorem next_transport (k l : ℤ) :
    next (state k l) =
      ((Transport.transport Circle.isCoveringMap_exp (path l k) (Logarithm.sheet k) : ℝ),
       (Transport.transport Circle.isCoveringMap_exp
         (path (k + direction l) l) (Logarithm.sheet l) : ℝ)) := by
  rw [next_sheet, transport_path, transport_path]
  rfl

theorem next_inverse_sheet (k l : ℤ) :
    next (state (k - direction (l - direction k)) (l - direction k)) = state k l := by
  simpa using next_sheet (k - direction (l - direction k)) (l - direction k)

theorem next_zero : next (state 0 0) = state 1 (-1) := by
  simpa [direction] using next_sheet 0 0

theorem next_one : next (state 1 (-1)) = state 0 0 := by
  simpa [direction] using next_sheet 1 (-1)

theorem two_cycle : next (next (state 0 0)) = state 0 0 := by
  rw [next_zero, next_one]

/-- Internal writing changes the response subsequently read by the same evolution law. -/
theorem selection_reverses :
    response (state 0 0).1 = 1 ∧
      response (next (state 0 0)).1 = -1 ∧
      response (next (next (state 0 0))).1 = 1 := by
  simp only [next_zero, next_one]
  norm_num [state, response_sheet]

noncomputable def nextHomeomorph : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) :=
  ((Homeomorph.prodComm ℝ ℝ).trans (flow.toHomeomorph (2 * Real.pi))).trans
    ((Homeomorph.prodComm ℝ ℝ).trans (flow.toHomeomorph (2 * Real.pi)))

theorem next_bijective : Function.Bijective next := nextHomeomorph.bijective

def update (point : ℤ × ℤ) : ℤ × ℤ :=
  let k := point.1 + direction point.2
  (k, point.2 + direction k)

/-- The same fixed return rule governs every finite prefix of the autonomous run. -/
theorem iterate_refinement (n : ℕ) (point : ℤ × ℤ) :
    (next^[n]) (state point.1 point.2) =
      state ((update^[n]) point).1 ((update^[n]) point).2 := by
  have intertwines : Function.Semiconj (fun p : ℤ × ℤ => state p.1 p.2) update next :=
    fun p => (next_sheet p.1 p.2).symm
  exact (intertwines.iterate_right n point).symm

/-- Both projected coordinates use the same write-then-read timing. -/
noncomputable def roundPaths (point : ℤ × ℤ) :
    Path (1 : Circle) 1 × Path (1 : Circle) 1 :=
  ((path point.2 point.1).trans (Path.refl 1),
   (Path.refl 1).trans (path (point.1 + direction point.2) point.2))

theorem roundPaths_transport (point : ℤ × ℤ) :
    Transport.transport Circle.isCoveringMap_exp (roundPaths point).1
        (Logarithm.sheet point.1) = Logarithm.sheet (update point).1 ∧
    Transport.transport Circle.isCoveringMap_exp (roundPaths point).2
        (Logarithm.sheet point.2) = Logarithm.sheet (update point).2 := by
  constructor
  · simp [roundPaths, Transport.transport_trans, transport_path, update, direction]
  · simp [roundPaths, Transport.transport_trans, transport_path, update, direction]
    rfl

/-- Each finite path prefix is generated from the system's successive internal states. -/
noncomputable def runPaths : ℕ → ℤ × ℤ → Path (1 : Circle) 1 × Path (1 : Circle) 1
  | 0, _ => (Path.refl 1, Path.refl 1)
  | n + 1, point =>
      let first := roundPaths point
      let rest := runPaths n (update point)
      (first.1.trans rest.1, first.2.trans rest.2)

theorem runPaths_transport (n : ℕ) (point : ℤ × ℤ) :
    Transport.transport Circle.isCoveringMap_exp (runPaths n point).1
        (Logarithm.sheet point.1) = Logarithm.sheet ((update^[n]) point).1 ∧
    Transport.transport Circle.isCoveringMap_exp (runPaths n point).2
        (Logarithm.sheet point.2) = Logarithm.sheet ((update^[n]) point).2 := by
  induction n generalizing point with
  | zero => simp [runPaths]
  | succ n ih =>
      constructor
      · simpa only [runPaths, Transport.transport_trans,
          (roundPaths_transport point).1, Function.iterate_succ_apply] using
            (ih (update point)).1
      · simpa only [runPaths, Transport.transport_trans,
          (roundPaths_transport point).2, Function.iterate_succ_apply] using
            (ih (update point)).2

/-- Every finite autonomous run is realized by the actual lifts of its generated paths. -/
theorem iterate_transport (n : ℕ) (point : ℤ × ℤ) :
    (next^[n]) (state point.1 point.2) =
      ((Transport.transport Circle.isCoveringMap_exp (runPaths n point).1
          (Logarithm.sheet point.1) : ℝ),
       (Transport.transport Circle.isCoveringMap_exp (runPaths n point).2
          (Logarithm.sheet point.2) : ℝ)) := by
  rw [iterate_refinement, (runPaths_transport n point).1, (runPaths_transport n point).2]
  rfl

end Monodromy.Autonomy
