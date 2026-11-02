module

public import Monodromy.Quartic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

@[expose] public section

/-!
# Coordinates for the quartic paths

One actual four-point fiber carries both operations. A continuous rectangle
protects the control operation during the parameter operation. Every path
confined to the original parameter slice preserves the second lifted
coordinate, so it cannot perform the parameter operation.
-/


namespace Monodromy.Torus

open unitInterval TorusCover

/-- One complete traversal of the control circle. -/
noncomputable def turn : Path (1 : Circle) 1 where
  toFun t := Circle.exp (2 * ((t : ℝ) * Real.pi))
  continuous_toFun := Circle.exp.continuous.comp
    (continuous_const.mul (continuous_subtype_val.mul continuous_const))
  source' := by simp
  target' := by simp

noncomputable def control : Path base base := turn.prod (Path.refl 1)

noncomputable def parameter : Path base base := (Path.refl 1).prod turn

/-- These are the actual covering-space transports, not prescribed sign tables. -/
noncomputable def controlAction : Equiv.Perm State :=
  Transport.transportEquiv isCoveringMap_projection control

noncomputable def parameterAction : Equiv.Perm State :=
  Transport.transportEquiv isCoveringMap_projection parameter

private theorem exp_pi : Circle.exp Real.pi = -1 := by
  apply Circle.ext
  simp [Circle.coe_exp, Complex.exp_pi_mul_I]

private noncomputable def controlLift (state : State) : C(I, Circle × Circle) where
  toFun t := (state.1.1 * Circle.exp ((t : ℝ) * Real.pi), state.1.2)
  continuous_toFun :=
    (continuous_const.mul (Circle.exp.continuous.comp
      (continuous_subtype_val.mul continuous_const))).prodMk continuous_const

private noncomputable def parameterLift (state : State) : C(I, Circle × Circle) where
  toFun t := (state.1.1, state.1.2 * Circle.exp ((t : ℝ) * Real.pi))
  continuous_toFun := continuous_const.prodMk
    (continuous_const.mul (Circle.exp.continuous.comp
      (continuous_subtype_val.mul continuous_const)))

/-- The continuous lift determines the control action on the entire actual fiber. -/
theorem control_apply (state : State) :
    (controlAction state).1 = (-state.1.1, state.1.2) := by
  have first : state.1.1 ^ 2 = 1 := congrArg Prod.fst state.2
  have second : state.1.2 ^ 2 = 1 := congrArg Prod.snd state.2
  have projects : projection ∘ controlLift state = control := by
    funext t
    apply Prod.ext
    · change (state.1.1 * Circle.exp ((t : ℝ) * Real.pi)) ^ 2 = turn t
      rw [mul_pow, first, one_mul, ← Circle.exp_natCast_mul]
      rfl
    · exact second
  have endpoint := Transport.transport_eq_actual_lift isCoveringMap_projection
    control state (controlLift state) projects (by simp [controlLift])
  simpa [controlAction, Transport.transportEquiv, controlLift, exp_pi] using endpoint

/-- A parameter loop also writes persistent state while both controls return home. -/
theorem parameter_apply (state : State) :
    (parameterAction state).1 = (state.1.1, -state.1.2) := by
  have first : state.1.1 ^ 2 = 1 := congrArg Prod.fst state.2
  have second : state.1.2 ^ 2 = 1 := congrArg Prod.snd state.2
  have projects : projection ∘ parameterLift state = parameter := by
    funext t
    apply Prod.ext
    · exact first
    · change (state.1.2 * Circle.exp ((t : ℝ) * Real.pi)) ^ 2 = turn t
      rw [mul_pow, second, one_mul, ← Circle.exp_natCast_mul]
      rfl
  have endpoint := Transport.transport_eq_actual_lift isCoveringMap_projection
    parameter state (parameterLift state) projects (by simp [parameterLift])
  simpa [parameterAction, Transport.transportEquiv, parameterLift, exp_pi] using endpoint

/-- A geometric family of control loops, with the parameter loop along both ends. -/
noncomputable def rectangle : C(I × I, Circle × Circle) where
  toFun st := (turn st.2, turn st.1)
  continuous_toFun := (turn.continuous.comp continuous_snd).prodMk
    (turn.continuous.comp continuous_fst)

/-- Protection follows from the filled rectangle in the actual covering base. -/
theorem parameter_protects_control :
    Algebra.Intertwines parameterAction controlAction controlAction := by
  exact Protection.loop_family_intertwines isCoveringMap_projection
    control control parameter rectangle
    (by intro t; change (turn t, turn 0) = (turn t, 1); rw [turn.source])
    (by intro t; change (turn t, turn 1) = (turn t, 1); rw [turn.target])
    (by intro s; change (turn 0, turn s) = (1, turn s); rw [turn.source])
    (by intro s; change (turn 1, turn s) = (1, turn s); rw [turn.target])

/-- A lift confined to the old parameter slice cannot change its second coordinate. -/
theorem fixed_parameter_preserves (γ : Path base base)
    (fixed : ∀ t, (γ t).2 = 1) (state : State) :
    (Transport.transport isCoveringMap_projection γ state).1.2 = state.1.2 := by
  obtain ⟨Γ, projects, starts, endpoint⟩ :=
    Transport.continuous_lift_exists isCoveringMap_projection γ state
  have square (t : I) : (Γ t).2 ^ 2 = 1 :=
    (congrArg Prod.snd (congrFun projects t)).trans (fixed t)
  have constant := isCoveringMap_square.const_of_comp
    (continuous_snd.comp Γ.continuous) (fun t s => (square t).trans (square s).symm)
    (1 : I) 0
  calc
    (Transport.transport isCoveringMap_projection γ state).1.2 = (Γ 1).2 :=
      congrArg Prod.snd endpoint.symm
    _ = (Γ 0).2 := constant
    _ = state.1.2 := congrArg Prod.snd starts

/-- No old-slice path realizes the new operation, even from a single chosen state. -/
theorem parameter_not_fixed_slice (γ : Path base base)
    (fixed : ∀ t, (γ t).2 = 1) (state : State) :
    Transport.transport isCoveringMap_projection γ state ≠ parameterAction state := by
  intro same
  have coordinates := congrArg (fun e : State => e.1.2) same
  have parameter_second := congrArg Prod.snd (parameter_apply state)
  rw [fixed_parameter_preserves γ fixed state, parameter_second] at coordinates
  exact Circle.neg_ne_self state.1.2 coordinates.symm

end Monodromy.Torus

/-!
# Paths acting on roots

Memory is a root of `(z²-u)²=θ`. Control and parameter paths use the same
covering-space transport. Torus coordinates serve only to prove their actions.
-/


namespace Monodromy.Quartic

abbrev Memory := Transport.Fiber projection TorusCover.base

noncomputable def coordinates : TorusCover.State ≃ Memory :=
  Transport.fiberEquiv (p := TorusCover.projection) (q := projection)
    homeomorph rfl TorusCover.base

/-- Read the carried complex root. -/
def value (state : Memory) : ℂ := state.1.1.2

/-- Walk once around the control circle, carrying the current root. -/
noncomputable def control : Equiv.Perm Memory :=
  Transport.transportEquiv isCoveringMap_projection Torus.control

/-- Walk once around the parameter circle by the same lifting rule. -/
noncomputable def parameter : Equiv.Perm Memory :=
  Transport.transportEquiv isCoveringMap_projection Torus.parameter

theorem coordinates_transport (γ : Path TorusCover.base TorusCover.base)
    (state : TorusCover.State) :
    coordinates (Transport.transport TorusCover.isCoveringMap_projection γ state) =
      Transport.transport isCoveringMap_projection γ (coordinates state) :=
  Transport.fiberEquiv_transport TorusCover.isCoveringMap_projection
    isCoveringMap_projection homeomorph rfl γ state

theorem coordinates_control (state : TorusCover.State) :
    coordinates (Torus.controlAction state) = control (coordinates state) :=
  coordinates_transport Torus.control state

theorem coordinates_parameter (state : TorusCover.State) :
    coordinates (Torus.parameterAction state) = parameter (coordinates state) :=
  coordinates_transport Torus.parameter state

theorem control_value (state : Memory) : value (control state) = -value state := by
  obtain ⟨e, rfl⟩ := coordinates.surjective state
  rw [← coordinates_control]
  change root (Torus.controlAction e).1.1 (Torus.controlAction e).1.2 = -root e.1.1 e.1.2
  rw [congrArg Prod.fst (Torus.control_apply e), congrArg Prod.snd (Torus.control_apply e)]
  exact root_neg_control e.1.1 e.1.2

theorem parameter_changes_value (state : Memory) :
    value (parameter state) ≠ value state := by
  obtain ⟨e, rfl⟩ := coordinates.surjective state
  rw [← coordinates_parameter]
  change root (Torus.parameterAction e).1.1 (Torus.parameterAction e).1.2 ≠ root e.1.1 e.1.2
  rw [congrArg Prod.fst (Torus.parameter_apply e), congrArg Prod.snd (Torus.parameter_apply e)]
  exact root_parameter_distinct e.1.1 e.1.2

/-- The geometric rectangle protects the old computation on actual quartic roots. -/
theorem parameter_protects_control : Algebra.Intertwines parameter control control := by
  intro state
  obtain ⟨e, rfl⟩ := coordinates.surjective state
  simpa only [coordinates_control, coordinates_parameter] using
    congrArg coordinates (Torus.parameter_protects_control e)

theorem parameter_protects_words (word : List Unit) (state : Memory) :
    Growth.run (fun _ : Unit => control) word (parameter state) =
      parameter (Growth.run (fun _ : Unit => control) word state) :=
  Growth.run_intertwines (fun _ e => parameter_protects_control e) word state

/-- Within this covering, every path with `|u|=2, θ=1` misses this operation. -/
theorem parameter_not_fixed_slice (γ : Path TorusCover.base TorusCover.base)
    (fixed : ∀ t, (γ t).2 = 1) (state : Memory) :
    Transport.transport isCoveringMap_projection γ state ≠ parameter state := by
  obtain ⟨e, rfl⟩ := coordinates.surjective state
  intro same
  apply Torus.parameter_not_fixed_slice γ fixed e
  apply coordinates.injective
  rw [coordinates_transport, coordinates_parameter]
  exact same

noncomputable instance : Fintype Memory := Fintype.ofEquiv TorusCover.State coordinates

theorem card_memory : Fintype.card Memory = 4 := by
  rw [← Fintype.card_congr coordinates]
  exact TorusCover.card_state

private theorem square_lift {f z : ℝ → ℂ} {t : ℝ} {v : ℂ}
    (continuous : ContinuousAt z t) (square : ∀ s, z s ^ 2 = f s)
    (regular : z t ≠ 0) (hf : HasDerivAt f v t) :
    HasDerivAt z (v / (2 * z t)) t := by
  let inverse : ℂ →L[ℝ] ℂ :=
    ((1 : ℂ →L[ℂ] ℂ).smulRight ((2 * z t)⁻¹)).restrictScalars ℝ
  have outer := (hasDerivAt_pow 2 (z t)).hasFDerivAt.restrictScalars ℝ
  have composed : (fun x : ℂ => x ^ 2) ∘ z =ᶠ[nhds t] f :=
    Filter.Eventually.of_forall square
  have left : Function.LeftInverse inverse
      (((1 : ℂ →L[ℂ] ℂ).smulRight ((2 : ℂ) * z t ^ (2 - 1))).restrictScalars ℝ) := by
    intro x
    simp [inverse]
    field_simp
  have result := outer.of_comp_of_leftInverse continuous hf.hasFDerivAt composed left
  simpa [inverse, div_eq_mul_inv] using result.hasDerivAt

/-- Continuity and differentiable controls force the carried root to obey the rule. -/
theorem lift_hasDerivAt (Γ : ℝ → Space) {t : ℝ} {du dθ : ℂ}
    (continuous : ContinuousAt Γ t)
    (control : HasDerivAt (fun s => 2 * ((Γ s).1.1.1 : ℂ)) du t)
    (parameter : HasDerivAt (fun s => ((Γ s).1.1.2 : ℂ)) dθ t) :
    HasDerivAt (fun s => (Γ s).1.2)
      (velocity (2 * ((Γ t).1.1.1 : ℂ)) (Γ t).1.2 du dθ) t := by
  let u : ℝ → ℂ := fun s => 2 * ((Γ s).1.1.1 : ℂ)
  let z : ℝ → ℂ := fun s => (Γ s).1.2
  let b : ℝ → ℂ := fun s => z s ^ 2 - u s
  have zcont : ContinuousAt z t :=
    continuous_snd.continuousAt.comp (continuous_subtype_val.continuousAt.comp continuous)
  have bcont : ContinuousAt b t := (zcont.pow 2).sub control.continuousAt
  have regular := space_regular (Γ t)
  have znonzero : z t ≠ 0 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp regular).1).2
  have bnonzero : b t ≠ 0 := (mul_ne_zero_iff.mp regular).2
  have db : HasDerivAt b (dθ / (2 * b t)) t :=
    square_lift bcont (fun s => (Γ s).2) bnonzero parameter
  have square (s : ℝ) : z s ^ 2 = u s + b s := by dsimp [b]; ring
  have hz := square_lift zcont square znonzero (control.add db)
  have forced := derivative_eq_velocity control parameter hz
    (Filter.Eventually.of_forall (fun s => (Γ s).2)) regular
  rwa [forced] at hz

private theorem residue_eq_initial {f : ℝ → ℂ}
    (stationary : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt f 0 t) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, f t = f 0 := by
  apply constant_of_has_deriv_right_zero
  · intro t ht
    exact (stationary t ht).continuousAt.continuousWithinAt
  · intro t ht
    exact (stationary t (Set.Ico_subset_Icc_self ht)).hasDerivWithinAt

/-- The differential rule preserves the equation from its initial value. -/
theorem equation_of_velocity {u θ z du dθ : ℝ → ℂ}
    (hu : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt u (du t) t)
    (hθ : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt θ (dθ t) t)
    (hz : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt z (velocity (u t) (z t) (du t) (dθ t)) t)
    (regular : ∀ t ∈ Set.Icc (0 : ℝ) 1, 4 * z t * (z t ^ 2 - u t) ≠ 0)
    (initial : (z 0 ^ 2 - u 0) ^ 2 = θ 0) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, (z t ^ 2 - u t) ^ 2 = θ t := by
  have stationary := fun t ht =>
    residual_hasDerivAt_velocity (hu t ht) (hθ t ht) (hz t ht) (regular t ht)
  intro t ht
  have conserved := residue_eq_initial stationary t ht
  simpa only [initial, sub_self, sub_eq_zero] using conserved

/-- A regular solution of the differential rule executes the actual path lift. -/
theorem velocity_transport
    (γ : C(ℝ, Circle × Circle)) (z : C(ℝ, ℂ)) (du dθ : ℝ → ℂ)
    (hu : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun s => 2 * ((γ s).1 : ℂ)) (du t) t)
    (hθ : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun s => ((γ s).2 : ℂ)) (dθ t) t)
    (hz : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt z (velocity (2 * ((γ t).1 : ℂ)) (z t) (du t) (dθ t)) t)
    (regular : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      4 * z t * (z t ^ 2 - 2 * ((γ t).1 : ℂ)) ≠ 0)
    (state : Transport.Fiber projection (γ 0)) (initial : z 0 = state.1.1.2) :
    z 1 = (Transport.transport isCoveringMap_projection
      ((Path.segment (0 : ℝ) 1).map γ.continuous) state).1.1.2 := by
  have initial_equation : (z 0 ^ 2 - 2 * ((γ 0).1 : ℂ)) ^ 2 = ((γ 0).2 : ℂ) := by
    have equation :
        (state.1.1.2 ^ 2 - 2 * ((projection state.1).1 : ℂ)) ^ 2 =
          ((projection state.1).2 : ℂ) := state.1.2
    rw [state.2] at equation
    simpa only [initial] using equation
  have equation := equation_of_velocity hu hθ hz regular initial_equation
  let Γ : C(unitInterval, Space) :=
    ⟨fun t => ⟨(γ (t : ℝ), z (t : ℝ)), equation (t : ℝ) t.2⟩,
      ((γ.continuous.prodMk z.continuous).comp continuous_subtype_val).subtype_mk _⟩
  have projects : projection ∘ Γ = (Path.segment (0 : ℝ) 1).map γ.continuous := by
    funext t
    change γ (t : ℝ) = γ ((Path.segment (0 : ℝ) 1) t)
    congr 1
    simp [Path.segment_apply, AffineMap.lineMap_apply, smul_eq_mul]
  have starts : Γ 0 = (state : Space) := by
    apply Subtype.ext
    exact Prod.ext state.2.symm initial
  have endpoint := Transport.transport_eq_actual_lift isCoveringMap_projection
    ((Path.segment (0 : ℝ) 1).map γ.continuous) state Γ projects starts
  exact (congrArg (fun point : Space => point.1.2) endpoint).symm

end Monodromy.Quartic
