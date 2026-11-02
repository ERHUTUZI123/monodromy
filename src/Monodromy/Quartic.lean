module

public import Monodromy.Covering
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.OpenPartialHomeomorph.Constructions
public import Mathlib.Analysis.Complex.SqrtDeriv
public import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# A joint covering with two independent branch directions

Both coordinates are continuous geometric controls. Each squaring map is a
genuine circle covering; compactness turns the product of their local charts
into a covering of the torus. No endpoint action is supplied as an axiom.
-/


namespace Monodromy.TorusCover

/-- The two geometric controls forget the signs of the carried state. -/
noncomputable def projection (state : Circle × Circle) : Circle × Circle :=
  (state.1 ^ 2, state.2 ^ 2)

/-- The squaring map used in each branch direction is an actual covering. -/
theorem isCoveringMap_square : IsCoveringMap (fun z : Circle => z ^ 2) :=
  (Circle.isQuotientCoveringMap_npow 2).isCoveringMap

/-- The joint projection is locally a product of two actual inverse charts. -/
theorem isCoveringMap_projection : IsCoveringMap projection := by
  apply isLocalHomeomorph_iff_isCoveringMap.mp
  intro state
  obtain ⟨e, hx, he⟩ := isCoveringMap_square.isLocalHomeomorph state.1
  obtain ⟨f, hy, hf⟩ := isCoveringMap_square.isLocalHomeomorph state.2
  refine ⟨e.prod f, ⟨hx, hy⟩, ?_⟩
  funext x
  exact Prod.ext (congrFun he x.1) (congrFun hf x.2)

/-- Each coordinate of the fiber over one has exactly the two possible signs. -/
theorem square_eq_one_iff (z : Circle) : z ^ 2 = 1 ↔ z = 1 ∨ z = -1 := by
  constructor
  · intro square
    have complex := congrArg (fun w : Circle => (w : ℂ)) square
    change (z : ℂ) ^ 2 = 1 at complex
    rcases sq_eq_one_iff.mp complex with positive | negative
    · exact Or.inl (Circle.ext positive)
    · exact Or.inr (Circle.ext negative)
  · rintro (rfl | rfl)
    · simp
    · apply Circle.ext
      simp

/-- Both geometric controls return to this point after an operation. -/
noncomputable def base : Circle × Circle := (1, 1)

/-- A state is an actual point of the covering fiber, with its equation. -/
abbrev State := Transport.Fiber projection base

/-- Labels describe the two geometric roots; they do not define transport. -/
noncomputable def sign (bit : Bool) : Circle := if bit then -1 else 1

@[simp] theorem sign_square (bit : Bool) : sign bit ^ 2 = 1 := by
  cases bit <;> apply Circle.ext <;> simp [sign]

/-- The four explicit points of the actual base fiber. -/
noncomputable def stateOfBits (bits : Bool × Bool) : State :=
  ⟨(sign bits.1, sign bits.2), Prod.ext (sign_square bits.1) (sign_square bits.2)⟩

/-- The base fiber has precisely the four sign pairs, with no omitted states. -/
noncomputable def fiberEquivBits : State ≃ Bool × Bool := by
  classical
  exact {
    toFun := fun state =>
      (if state.1.1 = 1 then false else true, if state.1.2 = 1 then false else true)
    invFun := stateOfBits
    left_inv := by
      intro state
      apply Subtype.ext
      apply Prod.ext
      · have square : state.1.1 ^ 2 = 1 := congrArg Prod.fst state.2
        rcases (square_eq_one_iff state.1.1).mp square with positive | negative
        · simp [stateOfBits, sign, positive]
        · simp [stateOfBits, sign, negative, Circle.neg_ne_self]
      · have square : state.1.2 ^ 2 = 1 := congrArg Prod.snd state.2
        rcases (square_eq_one_iff state.1.2).mp square with positive | negative
        · simp [stateOfBits, sign, positive]
        · simp [stateOfBits, sign, negative, Circle.neg_ne_self]
    right_inv := by
      rintro ⟨a, b⟩
      cases a <;> cases b <;> simp [stateOfBits, sign, Circle.neg_ne_self]
  }

noncomputable instance : Fintype State := Fintype.ofEquiv (Bool × Bool) fiberEquivBits.symm

/-- This is a finite four-sheet memory fiber, proved from the continuous model. -/
theorem card_state : Fintype.card State = 4 := by
  rw [Fintype.card_congr fiberEquivBits]
  decide

end Monodromy.TorusCover

/-!
# A continuous root of the nested quartic on its covering torus

The circle coordinates `a,b` project to `u = 2a², θ = b²`. The argument of the
principal square root stays in the right half-plane, so the root expression
is continuous on the whole covering torus. Sign changes of its coordinates
give distinct roots over the same projected control and parameter.
-/


namespace Monodromy.Quartic

private lemma sqrt_sq (z : ℂ) : Complex.sqrt z ^ 2 = z := by
  simp [Complex.sqrt]

/-- A root carried continuously by the two covering coordinates. -/
noncomputable def root (a b : Circle) : ℂ :=
  Complex.sqrt 2 * (a : ℂ) * Complex.sqrt (1 + (b : ℂ) / (2 * (a : ℂ)^2))

theorem root_sq (a b : Circle) : root a b ^ 2 = 2 * (a : ℂ)^2 + (b : ℂ) := by
  simp only [root, mul_pow, sqrt_sq]
  field_simp

theorem quartic_relation (a b : Circle) :
    (root a b ^ 2 - 2 * (a : ℂ)^2)^2 = (b : ℂ)^2 := by
  rw [root_sq]
  ring

theorem quartic_hasDerivAt (θ u z : ℂ) :
    HasDerivAt (fun w : ℂ => (w ^ 2 - u)^2 - θ) (4 * z * (z^2 - u)) z := by
  convert (((hasDerivAt_pow 2 z).sub_const u).pow 2).sub_const θ using 1
  ring

private lemma branch_norm (a b : Circle) :
    ‖(b : ℂ) / (2 * (a : ℂ)^2)‖ = (1/2 : ℝ) := by
  simp

theorem branch_re_pos (a b : Circle) :
    0 < (1 + (b : ℂ) / (2 * (a : ℂ)^2)).re := by
  have h := Complex.abs_re_le_norm ((b : ℂ) / (2 * (a : ℂ)^2))
  rw [branch_norm] at h
  have lower := (abs_le.mp h).1
  simp only [Complex.add_re, Complex.one_re]
  linarith

theorem continuous_root : Continuous (fun x : Circle × Circle => root x.1 x.2) := by
  apply Continuous.mul
  · exact continuous_const.mul (continuous_subtype_val.comp continuous_fst)
  · apply ContinuousOn.comp_continuous Complex.continuousOn_sqrt
    · exact continuous_const.add ((continuous_subtype_val.comp continuous_snd).div
        (continuous_const.mul ((continuous_subtype_val.comp continuous_fst).pow 2))
        (by intro x; exact mul_ne_zero two_ne_zero (pow_ne_zero 2 x.1.coe_ne_zero)))
    · intro x
      exact Or.inl (branch_re_pos x.1 x.2)

theorem root_neg_control (a b : Circle) : root (-a) b = -root a b := by
  simp [root]

theorem root_parameter_distinct (a b : Circle) : root a (-b) ≠ root a b := by
  intro same
  have squares := congrArg (fun z : ℂ => z ^ 2) same
  rw [root_sq, root_sq, Circle.coe_neg] at squares
  exact b.coe_ne_zero (CharZero.neg_eq_self_iff.mp (add_left_cancel squares))

theorem root_ne_zero (a b : Circle) : root a b ≠ 0 := by
  intro zero
  have impossible : 2 * (a : ℂ)^2 = -(b : ℂ) := by
    calc
      2 * (a : ℂ)^2 = (2 * (a : ℂ)^2 + (b : ℂ)) - (b : ℂ) := by ring
      _ = -(b : ℂ) := by rw [← root_sq, zero]; simp
  have := congrArg (fun z : ℂ => ‖z‖) impossible
  norm_num at this

theorem root_control_distinct (a b : Circle) : root (-a) b ≠ root a b := by
  rw [root_neg_control]
  exact fun same => root_ne_zero a b (CharZero.neg_eq_self_iff.mp same)

/-- Distinct covering coordinates over the same control give distinct roots. -/
theorem root_fiber_injective {a a' b b' : Circle}
    (control : (a : ℂ)^2 = (a' : ℂ)^2) (same : root a b = root a' b') :
    a = a' ∧ b = b' := by
  have squares := congrArg (fun z : ℂ => z ^ 2) same
  rw [root_sq, root_sq, control] at squares
  have parameter : b = b' := Circle.coe_injective (add_left_cancel squares)
  subst b'
  refine ⟨?_, rfl⟩
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp control with equal | opposite
  · exact Circle.coe_injective equal
  · have equal : a = -a' := Circle.coe_injective (by simpa using opposite)
    rw [equal] at same
    exact False.elim (root_control_distinct a' b same)

/-- No carried root meets a zero of the quartic's z-derivative. -/
theorem root_regular (a b : Circle) :
    4 * root a b * (root a b ^ 2 - 2 * (a : ℂ)^2) ≠ 0 := by
  have inner : root a b ^ 2 - 2 * (a : ℂ)^2 = (b : ℂ) := by
    rw [root_sq]
    ring
  rw [inner]
  exact mul_ne_zero (mul_ne_zero (by norm_num) (root_ne_zero a b)) b.coe_ne_zero

/-- The quartic itself, over `u = 2c` and `θ` on their two circles. -/
abbrev Space := {x : (Circle × Circle) × ℂ //
  (x.2 ^ 2 - 2 * (x.1.1 : ℂ)) ^ 2 = (x.1.2 : ℂ)}

noncomputable def realize (x : Circle × Circle) : Space :=
  ⟨(TorusCover.projection x, root x.1 x.2), by
    simpa [TorusCover.projection] using quartic_relation x.1 x.2⟩

theorem continuous_realize : Continuous realize :=
  (TorusCover.isCoveringMap_projection.continuous.prodMk continuous_root).subtype_mk _

theorem realize_injective : Function.Injective realize := by
  intro x y same
  have control := congrArg (fun q : Space => (q.1.1.1 : ℂ)) same
  have roots := congrArg (fun q : Space => q.1.2) same
  exact Prod.ext (root_fiber_injective control roots).1 (root_fiber_injective control roots).2

theorem realize_surjective : Function.Surjective realize := by
  rintro ⟨⟨⟨u, θ⟩, z⟩, equation⟩
  have norm_sq : ‖z ^ 2 - 2 * (u : ℂ)‖ ^ 2 = 1 := by
    rw [← norm_pow, equation, Circle.norm_coe]
  have unit : ‖z ^ 2 - 2 * (u : ℂ)‖ = 1 := by
    nlinarith [norm_nonneg (z ^ 2 - 2 * (u : ℂ))]
  let b : Circle := ⟨z ^ 2 - 2 * (u : ℂ), mem_sphere_zero_iff_norm.mpr unit⟩
  have parameter : b ^ 2 = θ := Circle.ext equation
  obtain ⟨a, control⟩ := (Circle.isQuotientCoveringMap_npow 2).surjective u
  have control' : (a : ℂ)^2 = (u : ℂ) := congrArg (fun c : Circle => (c : ℂ)) control
  have square : root a b ^ 2 = z ^ 2 := by
    rw [root_sq, control']
    change 2 * (u : ℂ) + (z ^ 2 - 2 * (u : ℂ)) = z ^ 2
    ring
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp square with positive | negative
  · refine ⟨(a, b), Subtype.ext (Prod.ext (Prod.ext control parameter) positive)⟩
  · refine ⟨(-a, b), Subtype.ext (Prod.ext (Prod.ext ?_ parameter) ?_)⟩
    · change (-a) ^ 2 = u
      apply Circle.ext
      simpa only [Circle.coe_pow, Circle.coe_neg, neg_sq] using control'
    · change root (-a) b = z
      rw [root_neg_control, negative, neg_neg]

/-- The torus is a global coordinate system for this actual quartic space. -/
noncomputable def homeomorph : (Circle × Circle) ≃ₜ Space :=
  (isHomeomorph_iff_continuous_bijective.mpr
    ⟨continuous_realize, realize_injective, realize_surjective⟩).homeomorph realize

def projection (state : Space) : Circle × Circle := state.1.1

/-- The inner root, recovered from the carried root and control. -/
noncomputable def inner (state : Space) : ℂ :=
  state.1.2 ^ 2 - 2 * (state.1.1.1 : ℂ)

@[simp] theorem inner_realize (x : Circle × Circle) :
    inner (homeomorph x) = (x.2 : ℂ) := by
  change root x.1 x.2 ^ 2 - 2 * (x.1 : ℂ)^2 = (x.2 : ℂ)
  rw [root_sq]
  ring

theorem isCoveringMap_projection : IsCoveringMap projection := by
  have covering := TorusCover.isCoveringMap_projection.comp_homeomorph homeomorph.symm
  convert covering using 1
  funext state
  change state.1.1 = (homeomorph (homeomorph.symm state)).1.1
  rw [homeomorph.apply_symm_apply]


/-- Every state of the actual quartic covering has a nonzero continuation denominator. -/
theorem space_regular (state : Space) :
    4 * state.1.2 * (state.1.2 ^ 2 - 2 * (state.1.1.1 : ℂ)) ≠ 0 := by
  obtain ⟨⟨a, b⟩, rfl⟩ := realize_surjective state
  exact root_regular a b

/-- The single continuation rule for control and parameter motion. -/
noncomputable def velocity (u z du dθ : ℂ) : ℂ :=
  (2 * (z ^ 2 - u) * du + dθ) / (4 * z * (z ^ 2 - u))

theorem velocity_eq_iff {u z du dθ dz : ℂ}
    (regular : 4 * z * (z ^ 2 - u) ≠ 0) :
    dz = velocity u z du dθ ↔
      4 * z * (z ^ 2 - u) * dz = 2 * (z ^ 2 - u) * du + dθ := by
  simp only [velocity, eq_div_iff regular, mul_comm dz]

/-- Differentiating the actual quartic constraint along a real-time trace. -/
theorem residual_hasDerivAt {u θ z : ℝ → ℂ} {t : ℝ} {du dθ dz : ℂ}
    (hu : HasDerivAt u du t) (hθ : HasDerivAt θ dθ t) (hz : HasDerivAt z dz t) :
    HasDerivAt (fun s => (z s ^ 2 - u s) ^ 2 - θ s)
      (4 * z t * (z t ^ 2 - u t) * dz - 2 * (z t ^ 2 - u t) * du - dθ) t := by
  convert (((hz.pow 2).sub hu).pow 2).sub hθ using 1
  simp only [Pi.sub_apply, Pi.pow_apply]
  ring

/-- The continuation rule makes the constraint residual stationary. -/
theorem residual_hasDerivAt_velocity {u θ z : ℝ → ℂ} {t : ℝ} {du dθ : ℂ}
    (hu : HasDerivAt u du t) (hθ : HasDerivAt θ dθ t)
    (hz : HasDerivAt z (velocity (u t) (z t) du dθ) t)
    (regular : 4 * z t * (z t ^ 2 - u t) ≠ 0) :
    HasDerivAt (fun s => (z s ^ 2 - u s) ^ 2 - θ s) 0 t := by
  have balance : 4 * z t * (z t ^ 2 - u t) * velocity (u t) (z t) du dθ =
      2 * (z t ^ 2 - u t) * du + dθ := (velocity_eq_iff regular).mp rfl
  convert residual_hasDerivAt hu hθ hz using 1
  rw [balance]
  ring

/-- On a regular differentiable trace, the equation determines the root velocity. -/
theorem derivative_eq_velocity {u θ z : ℝ → ℂ} {t : ℝ} {du dθ dz : ℂ}
    (hu : HasDerivAt u du t) (hθ : HasDerivAt θ dθ t) (hz : HasDerivAt z dz t)
    (equation : ∀ᶠ s in nhds t, (z s ^ 2 - u s) ^ 2 = θ s)
    (regular : 4 * z t * (z t ^ 2 - u t) ≠ 0) :
    dz = velocity (u t) (z t) du dθ := by
  have zero : HasDerivAt (fun s => (z s ^ 2 - u s) ^ 2 - θ s) 0 t :=
    (hasDerivAt_const t (0 : ℂ)).congr_of_eventuallyEq
      (equation.mono fun _ h => sub_eq_zero.mpr h)
  have balance := (residual_hasDerivAt hu hθ hz).unique zero
  apply (velocity_eq_iff regular).mpr
  apply sub_eq_zero.mp
  calc
    4 * z t * (z t ^ 2 - u t) * dz - (2 * (z t ^ 2 - u t) * du + dθ) =
        4 * z t * (z t ^ 2 - u t) * dz - 2 * (z t ^ 2 - u t) * du - dθ := by ring
    _ = 0 := balance
private theorem recover_outer (x : Circle × Circle) :
    (homeomorph x).1.2 / (Complex.sqrt 2 * Complex.sqrt
      (1 + inner (homeomorph x) / (2 * ((homeomorph x).1.1.1 : ℂ)))) = (x.1 : ℂ) := by
  change root x.1 x.2 / (Complex.sqrt 2 * Complex.sqrt
    (1 + inner (homeomorph x) / (2 * (x.1 : ℂ)^2))) = (x.1 : ℂ)
  rw [inner_realize]
  have regular :
      (Complex.sqrt 2 * (x.1 : ℂ)) *
        Complex.sqrt (1 + (x.2 : ℂ) / (2 * (x.1 : ℂ)^2)) ≠ 0 :=
    root_ne_zero x.1 x.2
  have denominator := mul_ne_zero
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp regular).1).1
    (mul_ne_zero_iff.mp regular).2
  apply (div_eq_iff denominator).mpr
  dsimp [root]
  ring

/-- The outer phase, recovered directly from the root and its inner branch. -/
noncomputable def outer (state : Space) : Circle :=
  ⟨state.1.2 / (Complex.sqrt 2 * Complex.sqrt
    (1 + inner state / (2 * (state.1.1.1 : ℂ)))), by
      apply mem_sphere_zero_iff_norm.mpr
      obtain ⟨x, rfl⟩ := homeomorph.surjective state
      rw [recover_outer]
      exact x.1.norm_coe⟩

@[simp] theorem outer_realize (x : Circle × Circle) :
    outer (homeomorph x) = x.1 := Circle.ext (recover_outer x)

theorem continuous_outer : Continuous outer := by
  apply (continuous_fst.comp homeomorph.symm.continuous).congr
  intro state
  obtain ⟨x, rfl⟩ := homeomorph.surjective state
  simp

/-- A phase weight; its geometric meaning on the unit circle is squared overlap. -/
noncomputable def weight (phase : ℂ) : ℝ := (1 + phase.re) / 2

theorem weight_geometry (phase : Circle) :
    weight phase = ‖(1 : ℂ) + (phase : ℂ)‖ ^ 2 / 4 := by
  rw [Complex.sq_norm, Complex.normSq_add]
  simp only [map_one, Circle.normSq_coe, one_mul, Complex.conj_re]
  dsimp [weight]
  ring

theorem weight_bounds (phase : Circle) : 0 ≤ weight phase ∧ weight phase ≤ 1 := by
  have bounded := Complex.abs_re_le_norm (phase : ℂ)
  rw [phase.norm_coe] at bounded
  obtain ⟨lower, upper⟩ := abs_le.mp bounded
  dsimp [weight]
  constructor <;> linarith

theorem weight_complement (phase : ℂ) : weight (-phase) = 1 - weight phase := by
  simp only [weight, Complex.neg_re]
  ring

@[simp] theorem weight_one : weight 1 = 1 := by norm_num [weight]
@[simp] theorem weight_neg_one : weight (-1) = 0 := by norm_num [weight]

end Monodromy.Quartic
