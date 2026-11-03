module

public import Monodromy.Paths
public import Mathlib.Dynamics.Flow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Roots steering their own motion

The inner root steers control motion. Exchanging the two phases gives memory
writing. Both motions use the quartic's same continuation rule.
-/

@[expose] public section

namespace Monodromy.Torus

private theorem exp_pi : Circle.exp Real.pi = -1 := by
  apply Circle.ext
  simp [Circle.coe_exp, Complex.exp_pi_mul_I]

noncomputable def flow (t : ℝ) (x : Circle × Circle) : Circle × Circle :=
  (x.1 * Circle.exp (t * (x.2 : ℂ).re / 2), x.2)

theorem continuous_flow : Continuous (fun p : ℝ × (Circle × Circle) => flow p.1 p.2) := by
  unfold flow
  fun_prop

theorem flow_zero (x : Circle × Circle) : flow 0 x = x := by
  simp [flow]

theorem flow_add (s t : ℝ) (x : Circle × Circle) :
    flow (s + t) x = flow s (flow t x) := by
  apply Prod.ext
  · change x.1 * Circle.exp ((s+t) * (x.2 : ℂ).re / 2) =
      (x.1 * Circle.exp (t * (x.2 : ℂ).re / 2)) *
        Circle.exp (s * (x.2 : ℂ).re / 2)
    rw [add_mul, add_div, Circle.exp_add]
    ac_rfl
  · rfl

theorem flow_reverse_parameter (t : ℝ) (a b : Circle) :
    flow t (a, -b) = ((flow (-t) (a,b)).1, -(flow (-t) (a,b)).2) := by
  apply Prod.ext
  · change a * Circle.exp (t * ((-b : Circle) : ℂ).re / 2) =
      a * Circle.exp ((-t) * (b : ℂ).re / 2)
    simp
  · rfl

theorem flow_two_pi (state : TorusCover.State) :
    flow (2 * Real.pi) state.1 = (-state.1.1, state.1.2) := by
  have binary : state.1.2 ^ 2 = 1 := congrArg Prod.snd state.2
  rcases (TorusCover.square_eq_one_iff state.1.2).mp binary with positive | negative
  · change (state.1.1 * Circle.exp (2 * Real.pi * (state.1.2 : ℂ).re / 2), state.1.2) = _
    rw [positive]
    simp only [Circle.coe_one, Complex.one_re, mul_one]
    rw [show 2 * Real.pi / 2 = Real.pi by ring, exp_pi]
    simp
  · change (state.1.1 * Circle.exp (2 * Real.pi * (state.1.2 : ℂ).re / 2), state.1.2) = _
    rw [negative]
    simp only [Circle.coe_neg, Circle.coe_one, Complex.neg_re, Complex.one_re]
    rw [show 2 * Real.pi * (-1) / 2 = -Real.pi by ring, Circle.exp_neg, exp_pi]
    simp

private lemma circle_exp_hasDerivAt (r t : ℝ) :
    HasDerivAt (fun s : ℝ => (Circle.exp (s * r) : ℂ))
      (Complex.I * (r : ℂ) * (Circle.exp (t * r) : ℂ)) t := by
  have h := ((((hasDerivAt_id t).mul_const r).ofReal_comp).mul_const Complex.I).cexp
  have h' : HasDerivAt (fun s : ℝ => (Circle.exp (s * r) : ℂ))
      ((Circle.exp (t * r) : ℂ) * ((r : ℂ) * Complex.I)) t := by
    simpa only [id_eq, one_mul, Circle.coe_exp] using h
  convert h' using 1
  ring

private lemma rotation_hasDerivAt (k : ℂ) (a : Circle) (rate t : ℝ) :
    HasDerivAt (fun s : ℝ => k * ((a * Circle.exp (s * rate / 2) : Circle) : ℂ) ^ 2)
      (Complex.I * (k * ((a * Circle.exp (t * rate / 2) : Circle) : ℂ) ^ 2) *
        (rate : ℂ)) t := by
  have scale (s : ℝ) : s * rate / 2 = s * (rate / 2) := by ring
  have h := ((circle_exp_hasDerivAt (rate / 2) t).const_mul (a : ℂ)).pow 2
  have hh := h.const_mul k
  convert hh using 1
  · ext s
    simp only [Circle.coe_mul, scale s, Pi.pow_apply]
  · simp only [Circle.coe_mul, scale t, Complex.ofReal_div, Complex.ofReal_ofNat]
    ring

/-- Exchange the roles of the two roots in the existing feedback. -/
noncomputable def write (t : ℝ) (x : Circle × Circle) : Circle × Circle :=
  (flow t x.swap).swap

theorem write_apply (t : ℝ) (x : Circle × Circle) :
    write t x = (x.1, x.2 * Circle.exp (t * (x.1 : ℂ).re / 2)) := rfl

theorem continuous_write : Continuous (fun p : ℝ × (Circle × Circle) => write p.1 p.2) :=
  continuous_swap.comp (continuous_flow.comp
    (continuous_fst.prodMk (continuous_swap.comp continuous_snd)))

theorem write_zero (x : Circle × Circle) : write 0 x = x := by
  simp [write, flow_zero]

theorem write_add (s t : ℝ) (x : Circle × Circle) :
    write (s + t) x = write s (write t x) := by
  simp [write, flow_add]

theorem write_two_pi (state : TorusCover.State) :
    write (2 * Real.pi) state.1 = (state.1.1, -state.1.2) := by
  let swapped : TorusCover.State := ⟨state.1.swap, by
    apply Prod.ext
    · exact congrArg Prod.snd state.2
    · exact congrArg Prod.fst state.2⟩
  simpa [write, swapped] using congrArg Prod.swap (flow_two_pi swapped)

theorem write_two_pi_parameter (state : TorusCover.State) :
    write (2 * Real.pi) state.1 = (parameterAction state).1 :=
  (write_two_pi state).trans (parameter_apply state).symm

/-- A chosen smooth gate: the second inner phase controls whether the first moves. -/
noncomputable def gated (t : ℝ) (x : Circle × Circle) : Circle × Circle :=
  (x.1 * Circle.exp (t * (1 + (x.2 : ℂ).re) / 4), x.2)

theorem continuous_gated : Continuous (fun p : ℝ × (Circle × Circle) => gated p.1 p.2) := by
  unfold gated
  fun_prop

theorem gated_zero (x : Circle × Circle) : gated 0 x = x := by
  simp [gated]

theorem gated_add (s t : ℝ) (x : Circle × Circle) :
    gated (s + t) x = gated s (gated t x) := by
  apply Prod.ext
  · change x.1 * Circle.exp ((s+t) * (1 + (x.2 : ℂ).re) / 4) =
      (x.1 * Circle.exp (t * (1 + (x.2 : ℂ).re) / 4)) *
        Circle.exp (s * (1 + (x.2 : ℂ).re) / 4)
    rw [add_mul, add_div, Circle.exp_add]
    ac_rfl
  · rfl

theorem gated_two_pi_positive (a b : Circle) (positive : b = 1) :
    gated (2 * Real.pi) (a, b) = (-a, b) := by
  subst b
  unfold gated
  simp only [Circle.coe_one, Complex.one_re]
  rw [show 2 * Real.pi * (1 + 1) / 4 = Real.pi by ring, exp_pi]
  simp

theorem gated_two_pi_negative (a b : Circle) (negative : b = -1) :
    gated (2 * Real.pi) (a, b) = (a, b) := by
  subst b
  simp [gated]

/-- This action is calculated from the continuous gate on every actual fiber point. -/
theorem gated_two_pi_bits (a b : Bool) :
    gated (2 * Real.pi) (TorusCover.stateOfBits (a, b)).1 =
      (TorusCover.stateOfBits ((if b then a else !a), b)).1 := by
  cases b
  · change gated (2 * Real.pi) (TorusCover.sign a, 1) = (TorusCover.sign (!a), 1)
    rw [gated_two_pi_positive _ _ rfl]
    cases a <;> simp [TorusCover.sign]
  · change gated (2 * Real.pi) (TorusCover.sign a, -1) = (TorusCover.sign a, -1)
    exact gated_two_pi_negative _ _ rfl

theorem gated_two_pi_preserves_fiber (state : TorusCover.State) :
    TorusCover.projection (gated (2 * Real.pi) state.1) = TorusCover.base := by
  obtain ⟨⟨a, b⟩, rfl⟩ := TorusCover.fiberEquivBits.symm.surjective state
  change TorusCover.projection (gated (2 * Real.pi) (TorusCover.stateOfBits (a,b)).1) = _
  rw [gated_two_pi_bits]
  exact (TorusCover.stateOfBits ((if b then a else !a), b)).2

/-- A symmetric chosen gate lets the first phase control writing the second. -/
noncomputable def gatedWrite (t : ℝ) (x : Circle × Circle) : Circle × Circle :=
  (gated t x.swap).swap

theorem continuous_gatedWrite :
    Continuous (fun p : ℝ × (Circle × Circle) => gatedWrite p.1 p.2) :=
  continuous_swap.comp (continuous_gated.comp
    (continuous_fst.prodMk (continuous_swap.comp continuous_snd)))

theorem gatedWrite_zero (x : Circle × Circle) : gatedWrite 0 x = x := by
  simp [gatedWrite, gated_zero]

theorem gatedWrite_add (s t : ℝ) (x : Circle × Circle) :
    gatedWrite (s+t) x = gatedWrite s (gatedWrite t x) := by
  simp [gatedWrite, gated_add]

theorem gatedWrite_two_pi_bits (a b : Bool) :
    gatedWrite (2 * Real.pi) (TorusCover.stateOfBits (a,b)).1 =
      (TorusCover.stateOfBits (a, if a then b else !b)).1 := by
  change (gated (2 * Real.pi) (TorusCover.stateOfBits (b,a)).1).swap = _
  rw [gated_two_pi_bits]
  rfl

end Monodromy.Torus

namespace Monodromy.Quartic

/-- The current inner root steers the control; the parameter remains fixed. -/
noncomputable def drive (state : Space) : ℂ :=
  Complex.I * (2 * (state.1.1.1 : ℂ)) * ((inner state).re : ℂ)

/-- The complete motion solving this feedback law, in proved covering coordinates. -/
noncomputable def flow : Flow ℝ Space where
  toFun t state := homeomorph (Torus.flow t (homeomorph.symm state))
  cont' := homeomorph.continuous.comp (Torus.continuous_flow.comp
    (continuous_fst.prodMk (homeomorph.symm.continuous.comp continuous_snd)))
  map_add' s t state := by simp [Torus.flow_add]
  map_zero' state := by simp [Torus.flow_zero]

private theorem flow_realize (t : ℝ) (x : Circle × Circle) :
    flow t (homeomorph x) = homeomorph (Torus.flow t x) := by
  simp [flow]

private theorem drive_realize (x : Circle × Circle) :
    drive (homeomorph x) =
      Complex.I * (2 * (x.1 : ℂ)^2) * ((x.2 : ℂ).re : ℂ) := by
  change Complex.I * (2 * (x.1 : ℂ)^2) * ((inner (homeomorph x)).re : ℂ) = _
  rw [inner_realize]

/-- The memory steering this flow is conserved throughout the motion. -/
theorem inner_flow (t : ℝ) (state : Space) : inner (flow t state) = inner state := by
  obtain ⟨x, rfl⟩ := homeomorph.surjective state
  rw [flow_realize, inner_realize, inner_realize]
  rfl

/-- The control velocity is read from the present state, at every time. -/
theorem flow_control_hasDerivAt (state : Space) (t : ℝ) :
    HasDerivAt (fun s => 2 * ((flow s state).1.1.1 : ℂ))
      (drive (flow t state)) t := by
  obtain ⟨⟨a, b⟩, rfl⟩ := homeomorph.surjective state
  simp only [flow_realize, drive_realize]
  exact Torus.rotation_hasDerivAt 2 a (b : ℂ).re t

private theorem flow_parameter_hasDerivAt (state : Space) (t : ℝ) :
    HasDerivAt (fun s => ((flow s state).1.1.2 : ℂ)) 0 t := by
  obtain ⟨⟨a, b⟩, rfl⟩ := homeomorph.surjective state
  simp only [flow_realize]
  exact hasDerivAt_const t ((b ^ 2 : Circle) : ℂ)

/-- The feedback carries the root by the same continuation law as every path. -/
theorem flow_hasDerivAt (state : Space) (t : ℝ) :
    HasDerivAt (fun s => (flow s state).1.2)
      (velocity (2 * ((flow t state).1.1.1 : ℂ)) (flow t state).1.2
        (drive (flow t state)) 0) t :=
  lift_hasDerivAt (fun s => flow s state)
    (flow.continuous continuous_id continuous_const).continuousAt
    (flow_control_hasDerivAt state t) (flow_parameter_hasDerivAt state t)

/-- On the memory fiber, the autonomous motion closes downstairs and flips the root. -/
theorem flow_two_pi (state : Memory) :
    flow (2 * Real.pi) state.1 = (control state).1 := by
  obtain ⟨e, rfl⟩ := coordinates.surjective state
  rw [← coordinates_control]
  change flow (2 * Real.pi) (homeomorph e.1) = homeomorph (Torus.controlAction e).1
  rw [flow_realize, Torus.flow_two_pi, Torus.control_apply]

/-- Parameter writing reverses the subsequent base path. -/
theorem parameter_reverses_flow (t : ℝ) (state : Memory) :
    projection (flow t (parameter state).1) = projection (flow (-t) state.1) := by
  obtain ⟨e, rfl⟩ := coordinates.surjective state
  rw [← coordinates_parameter]
  change projection (flow t (homeomorph (Torus.parameterAction e).1)) =
    projection (flow (-t) (homeomorph e.1))
  rw [flow_realize, flow_realize, Torus.parameter_apply, Torus.flow_reverse_parameter]
  change ((Torus.flow (-t) e.1).1 ^ 2, (-(Torus.flow (-t) e.1).2) ^ 2) =
    ((Torus.flow (-t) e.1).1 ^ 2, (Torus.flow (-t) e.1).2 ^ 2)
  apply Prod.ext
  · rfl
  · apply Circle.ext
    simp

theorem parameter_negates_drive (state : Memory) :
    drive (parameter state).1 = -drive state.1 := by
  obtain ⟨e, rfl⟩ := coordinates.surjective state
  rw [← coordinates_parameter]
  change drive (homeomorph (Torus.parameterAction e).1) = -drive (homeomorph e.1)
  rw [Torus.parameter_apply, drive_realize, drive_realize]
  simp

private theorem memory_drive_ne_zero (state : Memory) : drive state.1 ≠ 0 := by
  obtain ⟨e, rfl⟩ := coordinates.surjective state
  change drive (homeomorph e.1) ≠ 0
  rw [drive_realize]
  have rate : (e.1.2 : ℂ).re ≠ 0 := by
    have binary : e.1.2 ^ 2 = 1 := congrArg Prod.snd e.2
    rcases (TorusCover.square_eq_one_iff e.1.2).mp binary with positive | negative
    · simp [positive]
    · simp [negative]
  exact mul_ne_zero
    (mul_ne_zero Complex.I_ne_zero (mul_ne_zero two_ne_zero (pow_ne_zero 2 e.1.1.coe_ne_zero)))
    (Complex.ofReal_ne_zero.mpr rate)

theorem parameter_changes_drive (state : Memory) :
    drive (parameter state).1 ≠ drive state.1 := by
  rw [parameter_negates_drive]
  exact fun same => memory_drive_ne_zero state (CharZero.neg_eq_self_iff.mp same)

open Set Filter Topology in
private theorem different_future {f g : ℝ → ℂ} {df dg : ℂ}
    (hf : HasDerivAt f df 0) (hg : HasDerivAt g dg 0) (different : df ≠ dg) :
    ∃ t > 0, f t ≠ g t := by
  by_contra absent
  push Not at absent
  have near : f =ᶠ[𝓝[>] (0 : ℝ)] g := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact absent t ht
  have initial : f 0 = g 0 := tendsto_nhds_unique_of_eventuallyEq
    (hf.continuousAt.continuousWithinAt : ContinuousWithinAt f (Ioi 0) 0)
    (hg.continuousAt.continuousWithinAt : ContinuousWithinAt g (Ioi 0) 0) near
  apply different
  exact (uniqueDiffWithinAt_Ioi 0).eq_deriv _ hf.hasDerivWithinAt
    (hg.hasDerivWithinAt.congr (fun t ht => absent t ht) initial)

/-- The same feedback law produces different future paths after parameter writing. -/
theorem parameter_changes_path (state : Memory) :
    ∃ t > 0, projection (flow t (parameter state).1) ≠ projection (flow t state.1) := by
  have changed := flow_control_hasDerivAt (parameter state).1 0
  have original := flow_control_hasDerivAt state.1 0
  simp only [Flow.map_zero_apply] at changed original
  obtain ⟨t, positive, different⟩ :=
    different_future changed original (parameter_changes_drive state)
  refine ⟨t, positive, ?_⟩
  intro same
  exact different (congrArg (fun point : Circle × Circle => 2 * (point.1 : ℂ)) same)

/-- The same feedback, now allowing the inner memory to move. -/
noncomputable def write : Flow ℝ Space where
  toFun t state := homeomorph (Torus.write t (homeomorph.symm state))
  cont' := homeomorph.continuous.comp (Torus.continuous_write.comp
    (continuous_fst.prodMk (homeomorph.symm.continuous.comp continuous_snd)))
  map_add' s t state := by simp [Torus.write_add]
  map_zero' state := by simp [Torus.write_zero]

private theorem write_realize (t : ℝ) (x : Circle × Circle) :
    write t (homeomorph x) = homeomorph (Torus.write t x) := by
  simp [write]

theorem write_two_pi_memory (state : Memory) :
    write (2 * Real.pi) state.1 = (parameter state).1 := by
  obtain ⟨e, rfl⟩ := coordinates.surjective state
  rw [← coordinates_parameter]
  change write (2 * Real.pi) (homeomorph e.1) = homeomorph (Torus.parameterAction e).1
  rw [write_realize, Torus.write_two_pi_parameter]

theorem write_changes_inner (state : Memory) :
    ∃ t > 0, inner (write t state.1) ≠ inner state.1 := by
  refine ⟨2 * Real.pi, mul_pos two_pos Real.pi_pos, ?_⟩
  obtain ⟨e, rfl⟩ := coordinates.surjective state
  change inner (write (2 * Real.pi) (homeomorph e.1)) ≠ inner (homeomorph e.1)
  rw [write_realize, Torus.write_two_pi, inner_realize, inner_realize]
  change -(e.1.2 : ℂ) ≠ (e.1.2 : ℂ)
  intro same
  exact e.1.2.coe_ne_zero (CharZero.neg_eq_self_iff.mp same)

/-- The current outer phase steers writing of the inner branch. -/
noncomputable def writeDrive (state : Space) : ℂ :=
  Complex.I * (state.1.1.2 : ℂ) * ((outer state : ℂ).re : ℂ)

private theorem writeDrive_realize (x : Circle × Circle) :
    writeDrive (homeomorph x) =
      Complex.I * (x.2 : ℂ)^2 * ((x.1 : ℂ).re : ℂ) := by
  change Complex.I * (x.2 : ℂ)^2 * ((outer (homeomorph x) : ℂ).re : ℂ) = _
  rw [outer_realize]

theorem outer_write (t : ℝ) (state : Space) : outer (write t state) = outer state := by
  obtain ⟨x, rfl⟩ := homeomorph.surjective state
  rw [write_realize, outer_realize, outer_realize]
  rfl

private theorem write_control_hasDerivAt (state : Space) (t : ℝ) :
    HasDerivAt (fun s => 2 * ((write s state).1.1.1 : ℂ)) 0 t := by
  obtain ⟨⟨a, b⟩, rfl⟩ := homeomorph.surjective state
  simp only [write_realize]
  exact hasDerivAt_const t (2 * ((a ^ 2 : Circle) : ℂ))

theorem write_parameter_hasDerivAt (state : Space) (t : ℝ) :
    HasDerivAt (fun s => ((write s state).1.1.2 : ℂ))
      (writeDrive (write t state)) t := by
  obtain ⟨⟨a, b⟩, rfl⟩ := homeomorph.surjective state
  simp only [write_realize, writeDrive_realize]
  change HasDerivAt
    (fun s : ℝ => ((b * Circle.exp (s * (a : ℂ).re / 2) : Circle) : ℂ)^2)
    (Complex.I * ((b * Circle.exp (t * (a : ℂ).re / 2) : Circle) : ℂ)^2 *
      ((a : ℂ).re : ℂ)) t
  simpa only [one_mul] using Torus.rotation_hasDerivAt 1 b (a : ℂ).re t

theorem write_hasDerivAt (state : Space) (t : ℝ) :
    HasDerivAt (fun s => (write s state).1.2)
      (velocity (2 * ((write t state).1.1.1 : ℂ)) (write t state).1.2
        0 (writeDrive (write t state))) t :=
  lift_hasDerivAt (fun s => write s state)
    (write.continuous continuous_id continuous_const).continuousAt
    (write_control_hasDerivAt state t) (write_parameter_hasDerivAt state t)

noncomputable def gated : Flow ℝ Space where
  toFun t state := homeomorph (Torus.gated t (homeomorph.symm state))
  cont' := homeomorph.continuous.comp (Torus.continuous_gated.comp
    (continuous_fst.prodMk (homeomorph.symm.continuous.comp continuous_snd)))
  map_add' s t state := by simp [Torus.gated_add]
  map_zero' state := by simp [Torus.gated_zero]

noncomputable def gatedWrite : Flow ℝ Space where
  toFun t state := homeomorph (Torus.gatedWrite t (homeomorph.symm state))
  cont' := homeomorph.continuous.comp (Torus.continuous_gatedWrite.comp
    (continuous_fst.prodMk (homeomorph.symm.continuous.comp continuous_snd)))
  map_add' s t state := by simp [Torus.gatedWrite_add]
  map_zero' state := by simp [Torus.gatedWrite_zero]

private theorem gated_realize (t : ℝ) (x : Circle × Circle) :
    gated t (homeomorph x) = homeomorph (Torus.gated t x) := by simp [gated]

private theorem gatedWrite_realize (t : ℝ) (x : Circle × Circle) :
    gatedWrite t (homeomorph x) = homeomorph (Torus.gatedWrite t x) := by simp [gatedWrite]

theorem gated_closes (state : Memory) :
    projection (gated (2 * Real.pi) state.1) = TorusCover.base := by
  obtain ⟨e, rfl⟩ := coordinates.surjective state
  change projection (gated (2 * Real.pi) (homeomorph e.1)) = TorusCover.base
  rw [gated_realize]
  exact Torus.gated_two_pi_preserves_fiber e

theorem gatedWrite_closes (state : Memory) :
    projection (gatedWrite (2 * Real.pi) state.1) = TorusCover.base := by
  obtain ⟨e, rfl⟩ := coordinates.surjective state
  obtain ⟨⟨a,b⟩, rfl⟩ := TorusCover.fiberEquivBits.symm.surjective e
  change projection (gatedWrite (2 * Real.pi)
    (homeomorph (TorusCover.stateOfBits (a,b)).1)) = TorusCover.base
  rw [gatedWrite_realize, Torus.gatedWrite_two_pi_bits]
  exact (TorusCover.stateOfBits (a, if a then b else !b)).2

/-- The actual returning flow endpoint, with reversibility inherited from the flow. -/
noncomputable def gateControl : Equiv.Perm Memory := by
  let endpoint : Memory → Memory := fun state =>
    ⟨gated (2 * Real.pi) state.1, gated_closes state⟩
  have injective : Function.Injective endpoint := by
    intro state other same
    apply Subtype.ext
    exact (gated.toHomeomorph (2 * Real.pi)).injective (congrArg Subtype.val same)
  exact Equiv.ofBijective endpoint ⟨injective, Finite.surjective_of_injective injective⟩

noncomputable def gateWrite : Equiv.Perm Memory := by
  let endpoint : Memory → Memory := fun state =>
    ⟨gatedWrite (2 * Real.pi) state.1, gatedWrite_closes state⟩
  have injective : Function.Injective endpoint := by
    intro state other same
    apply Subtype.ext
    exact (gatedWrite.toHomeomorph (2 * Real.pi)).injective (congrArg Subtype.val same)
  exact Equiv.ofBijective endpoint ⟨injective, Finite.surjective_of_injective injective⟩

/-- Labels describe the complete physical memory fiber. -/
noncomputable def bits : Memory ≃ Logic.Bits :=
  coordinates.symm.trans TorusCover.fiberEquivBits

private theorem gateControl_encoded (a b : Bool) :
    gateControl (bits.symm (a,b)) = bits.symm (Logic.control (a,b)) := by
  apply Subtype.ext
  change gated (2 * Real.pi) (homeomorph (TorusCover.stateOfBits (a,b)).1) =
    homeomorph (TorusCover.stateOfBits (Logic.control (a,b))).1
  rw [gated_realize, Torus.gated_two_pi_bits, Logic.control_apply]

private theorem gateWrite_encoded (a b : Bool) :
    gateWrite (bits.symm (a,b)) = bits.symm (Logic.write (a,b)) := by
  apply Subtype.ext
  change gatedWrite (2 * Real.pi) (homeomorph (TorusCover.stateOfBits (a,b)).1) =
    homeomorph (TorusCover.stateOfBits (Logic.write (a,b))).1
  rw [gatedWrite_realize, Torus.gatedWrite_two_pi_bits, Logic.write_apply]

theorem bits_gateControl (state : Memory) :
    bits (gateControl state) = Logic.control (bits state) := by
  obtain ⟨⟨a,b⟩, rfl⟩ := bits.symm.surjective state
  simpa only [Equiv.apply_symm_apply] using congrArg bits (gateControl_encoded a b)

theorem bits_gateWrite (state : Memory) :
    bits (gateWrite state) = Logic.write (bits state) := by
  obtain ⟨⟨a,b⟩, rfl⟩ := bits.symm.surjective state
  simpa only [Equiv.apply_symm_apply] using congrArg bits (gateWrite_encoded a b)

private theorem control_encoded (a b : Bool) :
    control (bits.symm (a,b)) = bits.symm (Logic.old (a,b)) := by
  change control (coordinates (TorusCover.stateOfBits (a,b))) =
    coordinates (TorusCover.stateOfBits (Logic.old (a,b)))
  rw [← coordinates_control, Logic.old_apply]
  apply congrArg coordinates
  apply Subtype.ext
  rw [Torus.control_apply]
  cases a <;> simp [TorusCover.stateOfBits, TorusCover.sign]

theorem bits_control (state : Memory) : bits (control state) = Logic.old (bits state) := by
  obtain ⟨⟨a,b⟩, rfl⟩ := bits.symm.surjective state
  simpa only [Equiv.apply_symm_apply] using congrArg bits (control_encoded a b)

/-- The same continuous phase weight selects the control motion. -/
noncomputable def gateDrive (state : Space) : ℂ :=
  Complex.I * (2 * (state.1.1.1 : ℂ)) * (weight (inner state) : ℂ)

/-- Exchange the roles of the phases to select memory writing. -/
noncomputable def gateWriteDrive (state : Space) : ℂ :=
  Complex.I * (state.1.1.2 : ℂ) * (weight (outer state) : ℂ)

private theorem gateDrive_realize (x : Circle × Circle) :
    gateDrive (homeomorph x) = Complex.I * (2 * (x.1 : ℂ)^2) * (weight x.2 : ℂ) := by
  change Complex.I * (2 * (x.1 : ℂ)^2) * (weight (inner (homeomorph x)) : ℂ) = _
  rw [inner_realize]

private theorem gateWriteDrive_realize (x : Circle × Circle) :
    gateWriteDrive (homeomorph x) = Complex.I * (x.2 : ℂ)^2 * (weight x.1 : ℂ) := by
  change Complex.I * (x.2 : ℂ)^2 * (weight (outer (homeomorph x)) : ℂ) = _
  rw [outer_realize]

theorem gated_control_hasDerivAt (state : Space) (t : ℝ) :
    HasDerivAt (fun s => 2 * ((gated s state).1.1.1 : ℂ)) (gateDrive (gated t state)) t := by
  obtain ⟨⟨a, b⟩, rfl⟩ := homeomorph.surjective state
  simp only [gated_realize, gateDrive_realize]
  change HasDerivAt
    (fun s : ℝ => 2 * ((a * Circle.exp (s * (1 + (b : ℂ).re) / 4) : Circle) : ℂ)^2)
    (Complex.I * (2 * ((a * Circle.exp (t * (1 + (b : ℂ).re) / 4) : Circle) : ℂ)^2) *
      (weight b : ℂ)) t
  have scale (s : ℝ) : s * (1 + (b : ℂ).re) / 4 = s * weight b / 2 := by
    dsimp [weight]
    ring
  simpa only [scale] using Torus.rotation_hasDerivAt 2 a (weight b) t

private theorem gated_parameter_hasDerivAt (state : Space) (t : ℝ) :
    HasDerivAt (fun s => ((gated s state).1.1.2 : ℂ)) 0 t := by
  obtain ⟨⟨a, b⟩, rfl⟩ := homeomorph.surjective state
  simp only [gated_realize]
  exact hasDerivAt_const t ((b ^ 2 : Circle) : ℂ)

theorem gated_hasDerivAt (state : Space) (t : ℝ) :
    HasDerivAt (fun s => (gated s state).1.2)
      (velocity (2 * ((gated t state).1.1.1 : ℂ)) (gated t state).1.2
        (gateDrive (gated t state)) 0) t :=
  lift_hasDerivAt (fun s => gated s state)
    (gated.continuous continuous_id continuous_const).continuousAt
    (gated_control_hasDerivAt state t) (gated_parameter_hasDerivAt state t)

private theorem gatedWrite_control_hasDerivAt (state : Space) (t : ℝ) :
    HasDerivAt (fun s => 2 * ((gatedWrite s state).1.1.1 : ℂ)) 0 t := by
  obtain ⟨⟨a, b⟩, rfl⟩ := homeomorph.surjective state
  simp only [gatedWrite_realize]
  exact hasDerivAt_const t (2 * ((a ^ 2 : Circle) : ℂ))

theorem gatedWrite_parameter_hasDerivAt (state : Space) (t : ℝ) :
    HasDerivAt (fun s => ((gatedWrite s state).1.1.2 : ℂ))
      (gateWriteDrive (gatedWrite t state)) t := by
  obtain ⟨⟨a, b⟩, rfl⟩ := homeomorph.surjective state
  simp only [gatedWrite_realize, gateWriteDrive_realize]
  change HasDerivAt
    (fun s : ℝ => ((b * Circle.exp (s * (1 + (a : ℂ).re) / 4) : Circle) : ℂ)^2)
    (Complex.I * ((b * Circle.exp (t * (1 + (a : ℂ).re) / 4) : Circle) : ℂ)^2 *
      (weight a : ℂ)) t
  have scale (s : ℝ) : s * (1 + (a : ℂ).re) / 4 = s * weight a / 2 := by
    dsimp [weight]
    ring
  simpa only [one_mul, scale] using Torus.rotation_hasDerivAt 1 b (weight a) t

theorem gatedWrite_hasDerivAt (state : Space) (t : ℝ) :
    HasDerivAt (fun s => (gatedWrite s state).1.2)
      (velocity (2 * ((gatedWrite t state).1.1.1 : ℂ)) (gatedWrite t state).1.2
        0 (gateWriteDrive (gatedWrite t state))) t :=
  lift_hasDerivAt (fun s => gatedWrite s state)
    (gatedWrite.continuous continuous_id continuous_const).continuousAt
    (gatedWrite_control_hasDerivAt state t) (gatedWrite_parameter_hasDerivAt state t)

/-- These are closed feedback operations on the same physical memory fiber. -/
theorem gates_noncommute : gateControl * gateWrite ≠ gateWrite * gateControl :=
  Logic.noncommutation_of_correspondence bits gateControl gateWrite
    bits_gateControl bits_gateWrite

/-- The two conditional gates and the old flip generate every four-root permutation. -/
theorem gates_generate_all :
    Subgroup.closure ({gateControl, gateWrite, control} : Set (Equiv.Perm Memory)) = ⊤ :=
  Logic.generates_all_of_correspondence bits gateControl gateWrite control
    bits_gateControl bits_gateWrite bits_control

end Monodromy.Quartic
