module

public import Monodromy.Covering
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.Complex.CoveringMap
public import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# The branches of the logarithm

Restricting the exponential to imaginary arguments gives the circle covering.
Its fiber over one retains an integer. A loop transports every initial
branch by addition, proved from its actual continuous lift. Nested complex
exponentials supply a conditional upper write: the actual lower lift winds
around the upper logarithm's omitted point only on the zero branch.
-/

@[expose] public section

namespace Monodromy.Logarithm

open unitInterval

abbrev Memory := Transport.Fiber Circle.exp (1 : Circle)

noncomputable def sheet (k : ℤ) : Memory :=
  ⟨(k : ℝ) * (2 * Real.pi), Circle.exp_int_mul_two_pi k⟩

noncomputable def integers : ℤ ≃ Memory := Equiv.ofBijective sheet ⟨by
    intro k n same
    have values := congrArg Subtype.val same
    change (k : ℝ) * (2 * Real.pi) = (n : ℝ) * (2 * Real.pi) at values
    exact Int.cast_injective (mul_right_cancel₀
      (mul_ne_zero two_ne_zero Real.pi_ne_zero) values), by
    intro root
    obtain ⟨k, same⟩ := Circle.exp_eq_one.mp root.2
    exact ⟨k, Subtype.ext same.symm⟩⟩

noncomputable def turn (n : ℤ) : Path (1 : Circle) 1 where
  toFun t := Circle.exp (((n : ℝ) * (t : ℝ)) * (2 * Real.pi))
  continuous_toFun := Circle.exp.continuous.comp
    ((continuous_const.mul continuous_subtype_val).mul continuous_const)
  source' := by simp
  target' := by simp

noncomputable def lift (k n : ℤ) : C(I, ℝ) where
  toFun t := ((k : ℝ) + (n : ℝ) * (t : ℝ)) * (2 * Real.pi)
  continuous_toFun := (continuous_const.add
    (continuous_const.mul continuous_subtype_val)).mul continuous_const

theorem transport_turn (k n : ℤ) :
    Transport.transport Circle.isCoveringMap_exp (turn n) (sheet k) = sheet (k + n) := by
  have projects : Circle.exp ∘ lift k n = turn n := by
    funext t
    simp [lift, turn, add_mul, Circle.exp_add]
  have starts : lift k n 0 = (sheet k : ℝ) := by simp [lift, sheet]
  apply Subtype.ext
  calc
    (Transport.transport Circle.isCoveringMap_exp (turn n) (sheet k) : ℝ) =
        lift k n 1 := Transport.transport_eq_actual_lift
          Circle.isCoveringMap_exp (turn n) (sheet k) (lift k n) projects starts
    _ = (sheet (k + n) : ℝ) := by simp [lift, sheet]

/-- Every fixed loop translates all branches by the same integer. -/
theorem transport_translation (γ : Path (1 : Circle) 1) (k : ℤ) :
    Transport.transport Circle.isCoveringMap_exp γ (sheet k) =
      sheet (k + integers.symm
        (Transport.transport Circle.isCoveringMap_exp γ (sheet 0))) := by
  let deck : C(ℝ, ℝ) :=
    ⟨fun x => x + (k : ℝ) * (2 * Real.pi), continuous_id.add continuous_const⟩
  have square : Circle.exp ∘ deck = Circle.exp := by
    funext x
    simp [deck, Circle.exp_add]
  have mapped (j : ℤ) : Transport.mapFiber deck square (sheet j) = sheet (j + k) := by
    apply Subtype.ext
    simp [Transport.mapFiber, deck, sheet, add_mul]
  have natural := Transport.transport_naturality
    Circle.isCoveringMap_exp Circle.isCoveringMap_exp deck square γ (sheet 0)
  rw [mapped, zero_add] at natural
  have endpoint : sheet (integers.symm
      (Transport.transport Circle.isCoveringMap_exp γ (sheet 0))) =
      Transport.transport Circle.isCoveringMap_exp γ (sheet 0) :=
    integers.apply_symm_apply _
  rw [← endpoint, mapped] at natural
  simpa [add_comm] using natural

end Monodromy.Logarithm


/-! Two successive logarithmic lifts and their fixed-loop actions. -/

noncomputable section

namespace Monodromy.NestedContinuation

open unitInterval

abbrev Punctured := {z : ℂ // z ≠ 0}

def expCover (z : ℂ) : Punctured := ⟨Complex.exp z, Complex.exp_ne_zero z⟩

theorem covering : IsCoveringMap expCover := Complex.isCoveringMap_exp

def period (k : ℤ) : ℂ := (k : ℂ) * (2 * Real.pi * Complex.I)

theorem exp_period (k : ℤ) : Complex.exp (period k) = 1 :=
  Complex.exp_eq_one_iff.mpr ⟨k, rfl⟩

def rotor (t : I) : ℂ := (Circle.exp ((2 * Real.pi) * (t : ℝ)) : ℂ)

theorem continuous_rotor : Continuous rotor := by unfold rotor; fun_prop

@[simp] theorem rotor_zero : rotor 0 = 1 := by simp [rotor]
@[simp] theorem rotor_one : rotor 1 = 1 := by simp [rotor]

theorem rotor_ne_zero (t : I) : rotor t ≠ 0 := (Circle.exp _).coe_ne_zero

theorem rotor_norm (t : I) : ‖rotor t‖ = 1 := (Circle.exp _).norm_coe

def firstRoot (k : ℤ) : ℂ := 1 + period k

theorem firstRoot_slit (k : ℤ) : firstRoot k ∈ Complex.slitPlane := by
  left
  simp [firstRoot, period]

theorem firstRoot_ne_zero (k : ℤ) : firstRoot k ≠ 0 :=
  Complex.slitPlane_ne_zero (firstRoot_slit k)

def secondRoot (k m : ℤ) : ℂ := Complex.log (firstRoot k) + period m

theorem exp_secondRoot (k m : ℤ) : Complex.exp (secondRoot k m) = firstRoot k := by
  rw [secondRoot, Complex.exp_add, exp_period, mul_one, Complex.exp_log (firstRoot_ne_zero k)]

def base : Punctured := expCover 1

theorem exp_firstRoot (k : ℤ) : expCover (firstRoot k) = base := by
  apply Subtype.ext
  change Complex.exp (1 + period k) = Complex.exp 1
  rw [Complex.exp_add, exp_period, mul_one]

/-- One fixed base loop, independent of both branch indices. -/
def loop : Path base base where
  toFun t := expCover (rotor t)
  continuous_toFun := by unfold expCover rotor; fun_prop
  source' := by simp [base]
  target' := by simp [base]

/-- This is the actual first lift supplied by the covering, not a prescribed successor. -/
private def firstLift (k : ℤ) : C(I, ℂ) :=
  covering.liftPath loop (firstRoot k) (loop.source.trans (exp_firstRoot k).symm)

private def firstWitness (k : ℤ) : C(I, ℂ) where
  toFun t := rotor t + period k
  continuous_toFun := continuous_rotor.add continuous_const

private theorem firstWitness_projects (k : ℤ) : expCover ∘ firstWitness k = loop := by
  funext t
  apply Subtype.ext
  change Complex.exp (rotor t + period k) = Complex.exp (rotor t)
  rw [Complex.exp_add, exp_period, mul_one]

/-- The explicit circle is identified with the unique first lift only in the proof. -/
private theorem firstLift_eq (k : ℤ) (t : I) : firstLift k t = rotor t + period k := by
  have same : firstWitness k = firstLift k :=
    (covering.eq_liftPath_iff' (loop.source.trans (exp_firstRoot k).symm)).mpr
      ⟨firstWitness_projects k, by simp [firstWitness, firstRoot]⟩
  exact congrArg (fun curve : C(I, ℂ) => curve t) same.symm

/-- Every nonzero first-level index keeps its circle in one logarithm chart. -/
private theorem firstLift_slit {k : ℤ} (nonzero : k ≠ 0) (t : I) :
    firstLift k t ∈ Complex.slitPlane := by
  rw [firstLift_eq]
  apply Or.inr
  have bound : |(rotor t).im| ≤ 1 := (Complex.abs_im_le_norm _).trans_eq (rotor_norm t)
  have imag : (period k).im = (k : ℝ) * (2 * Real.pi) := by simp [period]
  simp only [Complex.add_im, imag]
  intro zero
  rcases lt_or_gt_of_ne nonzero with negative | positive
  · have integer : (k : ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
    have lower : -1 ≤ (rotor t).im := (abs_le.mp bound).1
    have upper : (rotor t).im ≤ 1 := (abs_le.mp bound).2
    nlinarith [Real.pi_gt_three, Real.pi_pos]
  · have integer : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
    have lower : -1 ≤ (rotor t).im := (abs_le.mp bound).1
    have upper : (rotor t).im ≤ 1 := (abs_le.mp bound).2
    nlinarith [Real.pi_gt_three, Real.pi_pos]

private theorem firstLift_ne_zero (k : ℤ) (t : I) : firstLift k t ≠ 0 := by
  by_cases zero : k = 0
  · subst k
    simpa [firstLift_eq, period] using rotor_ne_zero t
  · exact Complex.slitPlane_ne_zero (firstLift_slit zero t)

/-- The next covering receives the actual first lift, preserving its nonzero values. -/
private def firstPath (k : ℤ) : Path
    (⟨firstRoot k, firstRoot_ne_zero k⟩ : Punctured)
    ⟨firstRoot k, firstRoot_ne_zero k⟩ where
  toFun t := ⟨firstLift k t, firstLift_ne_zero k t⟩
  continuous_toFun := (firstLift k).continuous.subtype_mk _
  source' := by apply Subtype.ext; simp [firstLift_eq, firstRoot]
  target' := by apply Subtype.ext; simp [firstLift_eq, firstRoot]

/-- The second lift is generated from the first actual lift and the initial branch alone. -/
private def secondLift (k m : ℤ) : C(I, ℂ) :=
  covering.liftPath (firstPath k) (secondRoot k m)
    ((firstPath k).source.trans (by apply Subtype.ext; exact (exp_secondRoot k m).symm))

private def zeroWitness (m : ℤ) : C(I, ℂ) where
  toFun t := ((2 * Real.pi) * (t : ℝ) : ℂ) * Complex.I + period m
  continuous_toFun := by fun_prop

private theorem zeroWitness_projects (m : ℤ) : expCover ∘ zeroWitness m = firstPath 0 := by
  funext t
  apply Subtype.ext
  change Complex.exp (((2 * Real.pi) * (t : ℝ) : ℂ) * Complex.I + period m) = firstLift 0 t
  rw [Complex.exp_add, exp_period, mul_one, firstLift_eq]
  simp [period, rotor, Circle.coe_exp]

private def nonzeroWitness (k m : ℤ) (nonzero : k ≠ 0) : C(I, ℂ) where
  toFun t := Complex.log (firstLift k t) + period m
  continuous_toFun := ((firstLift k).continuous.clog (firstLift_slit nonzero)).add continuous_const

private theorem nonzeroWitness_projects (k m : ℤ) (nonzero : k ≠ 0) :
    expCover ∘ nonzeroWitness k m nonzero = firstPath k := by
  funext t
  apply Subtype.ext
  change Complex.exp (Complex.log (firstLift k t) + period m) = firstLift k t
  rw [Complex.exp_add, exp_period, mul_one, Complex.exp_log (firstLift_ne_zero k t)]

/-- Native conditional execution comes from two actual lifts of one fixed loop. -/
private theorem secondLift_end (k m : ℤ) :
    secondLift k m 1 = secondRoot k (m + if k = 0 then 1 else 0) := by
  by_cases zero : k = 0
  · subst k
    have same : zeroWitness m = secondLift 0 m :=
      (covering.eq_liftPath_iff'
        ((firstPath 0).source.trans (by apply Subtype.ext; exact (exp_secondRoot 0 m).symm))).mpr
        ⟨zeroWitness_projects m, by simp [zeroWitness, secondRoot, firstRoot, period]⟩
    rw [← same]
    simp [zeroWitness, secondRoot, firstRoot, period]
    ring
  · have same : nonzeroWitness k m zero = secondLift k m :=
      (covering.eq_liftPath_iff'
        ((firstPath k).source.trans (by apply Subtype.ext; exact (exp_secondRoot k m).symm))).mpr
        ⟨nonzeroWitness_projects k m zero, by simp [nonzeroWitness, firstLift_eq, secondRoot, firstRoot]⟩
    rw [← same]
    simp [nonzeroWitness, firstLift_eq, secondRoot, firstRoot, zero]


/-- Both layers project to the same fixed base path throughout execution. -/
private theorem firstLift_projects (k : ℤ) : expCover ∘ firstLift k = loop :=
  covering.liftPath_lifts loop (firstRoot k) (loop.source.trans (exp_firstRoot k).symm)

private theorem firstLift_start (k : ℤ) : firstLift k 0 = firstRoot k :=
  covering.liftPath_zero loop (firstRoot k) (loop.source.trans (exp_firstRoot k).symm)

private theorem secondLift_exp (k m : ℤ) (t : I) :
    Complex.exp (secondLift k m t) = firstLift k t := by
  have projects := covering.liftPath_lifts (firstPath k) (secondRoot k m)
    ((firstPath k).source.trans (by apply Subtype.ext; exact (exp_secondRoot k m).symm))
  exact congrArg Subtype.val (congrFun projects t)

private theorem secondLift_start (k m : ℤ) : secondLift k m 0 = secondRoot k m :=
  covering.liftPath_zero (firstPath k) (secondRoot k m)
    ((firstPath k).source.trans (by apply Subtype.ext; exact (exp_secondRoot k m).symm))

private theorem secondLift_projects (k m : ℤ) (t : I) :
    expCover (Complex.exp (secondLift k m t)) = loop t := by
  rw [secondLift_exp]
  exact congrFun (firstLift_projects k) t

/-- The fixed base path avoids the second singular value. -/
theorem loop_avoids_one (t : I) : loop t ≠ (⟨1, one_ne_zero⟩ : Punctured) := by
  intro same
  have exponential : Complex.exp (rotor t) = 1 := congrArg Subtype.val same
  obtain ⟨n, period_eq⟩ := Complex.exp_eq_one_iff.mp exponential
  have zero : firstLift (-n) t = 0 := by
    rw [firstLift_eq]
    rw [show rotor t = period n from period_eq]
    simp [period]
  exact firstLift_ne_zero (-n) t zero

/-- A native state is the retained root value, with no integer indices in the runtime interface. -/
abbrev Memory := Transport.Fiber (fun z : ℂ => expCover (Complex.exp z)) base

def prepare (k m : ℤ) : Memory :=
  ⟨secondRoot k m, by
    change expCover (Complex.exp (secondRoot k m)) = base
    rw [exp_secondRoot, exp_firstRoot]⟩

/-- The first lift starts at the exponential of the retained root itself. -/
def firstRaw (path : Path base base) (state : Memory) : C(I, ℂ) :=
  covering.liftPath path (Complex.exp state.val) (path.source.trans state.property.symm)

theorem firstRaw_projects (path : Path base base) (state : Memory) :
    expCover ∘ firstRaw path state = path :=
  covering.liftPath_lifts path (Complex.exp state.val) (path.source.trans state.property.symm)

theorem firstRaw_start (path : Path base base) (state : Memory) :
    firstRaw path state 0 = Complex.exp state.val :=
  covering.liftPath_zero path (Complex.exp state.val) (path.source.trans state.property.symm)

theorem firstRaw_ne_zero (path : Path base base)
    (avoids : ∀ t, path t ≠ (⟨1, one_ne_zero⟩ : Punctured)) (state : Memory) (t : I) :
    firstRaw path state t ≠ 0 := by
  intro zero
  have projects := congrFun (firstRaw_projects path state) t
  apply avoids t
  calc
    path t = expCover (firstRaw path state t) := projects.symm
    _ = expCover 0 := congrArg expCover zero
    _ = (⟨1, one_ne_zero⟩ : Punctured) := Subtype.ext Complex.exp_zero

/-- The upper covering receives exactly the actual first lift. -/
def firstRawPath (path : Path base base)
    (avoids : ∀ t, path t ≠ (⟨1, one_ne_zero⟩ : Punctured)) (state : Memory) :
    Path (expCover state.val)
      ⟨firstRaw path state 1, firstRaw_ne_zero path avoids state 1⟩ where
  toFun t := ⟨firstRaw path state t, firstRaw_ne_zero path avoids state t⟩
  continuous_toFun := (firstRaw path state).continuous.subtype_mk _
  source' := by apply Subtype.ext; exact firstRaw_start path state
  target' := rfl

def secondRaw (path : Path base base)
    (avoids : ∀ t, path t ≠ (⟨1, one_ne_zero⟩ : Punctured)) (state : Memory) : C(I, ℂ) :=
  covering.liftPath (firstRawPath path avoids state) state.val (firstRawPath path avoids state).source

theorem secondRaw_exp (path : Path base base)
    (avoids : ∀ t, path t ≠ (⟨1, one_ne_zero⟩ : Punctured)) (state : Memory) (t : I) :
    Complex.exp (secondRaw path avoids state t) = firstRaw path state t := by
  have projects := covering.liftPath_lifts (firstRawPath path avoids state) state.val
    (firstRawPath path avoids state).source
  exact congrArg Subtype.val (congrFun projects t)

theorem secondRaw_start (path : Path base base)
    (avoids : ∀ t, path t ≠ (⟨1, one_ne_zero⟩ : Punctured)) (state : Memory) :
    secondRaw path avoids state 0 = state.val :=
  covering.liftPath_zero (firstRawPath path avoids state) state.val
    (firstRawPath path avoids state).source

theorem secondRaw_projects (path : Path base base)
    (avoids : ∀ t, path t ≠ (⟨1, one_ne_zero⟩ : Punctured)) (state : Memory) (t : I) :
    expCover (Complex.exp (secondRaw path avoids state t)) = path t := by
  rw [secondRaw_exp]
  exact congrFun (firstRaw_projects path state) t

/-- Execution uses only the fixed path and the actual retained root. -/
def execute (path : Path base base)
    (avoids : ∀ t, path t ≠ (⟨1, one_ne_zero⟩ : Punctured)) (state : Memory) : Memory :=
  ⟨secondRaw path avoids state 1, (secondRaw_projects path avoids state 1).trans path.target⟩

private theorem firstRaw_prepare (k m : ℤ) : firstRaw loop (prepare k m) = firstLift k :=
  (covering.eq_liftPath_iff' (loop.source.trans (exp_firstRoot k).symm)).mpr
    ⟨firstRaw_projects loop (prepare k m), by
      rw [firstRaw_start]
      exact exp_secondRoot k m⟩

private theorem secondRaw_prepare (k m : ℤ) :
    secondRaw loop loop_avoids_one (prepare k m) = secondLift k m := by
  have projects : expCover ∘ secondRaw loop loop_avoids_one (prepare k m) = firstPath k := by
    funext t
    apply Subtype.ext
    change Complex.exp (secondRaw loop loop_avoids_one (prepare k m) t) = firstLift k t
    rw [secondRaw_exp, firstRaw_prepare]
  exact (covering.eq_liftPath_iff'
    ((firstPath k).source.trans (by apply Subtype.ext; exact (exp_secondRoot k m).symm))).mpr
    ⟨projects, secondRaw_start loop loop_avoids_one (prepare k m)⟩

theorem execute_prepare (k m : ℤ) :
    execute loop loop_avoids_one (prepare k m) = prepare k (m + if k = 0 then 1 else 0) := by
  apply Subtype.ext
  change secondRaw loop loop_avoids_one (prepare k m) 1 = _
  rw [secondRaw_prepare, secondLift_end]
  rfl

/-- A second fixed base loop uses the same two coverings. -/
def advanceLoop : Path base base where
  toFun t := expCover (1 + (((2 * Real.pi) * (t : ℝ) : ℝ) : ℂ) * Complex.I)
  continuous_toFun := by unfold expCover; fun_prop
  source' := by apply Subtype.ext; simp [base, expCover]
  target' := by
    apply Subtype.ext
    change Complex.exp (1 + (((2 * Real.pi) * (1 : ℝ) : ℝ) : ℂ) * Complex.I) = Complex.exp 1
    have turn : (((2 * Real.pi) * (1 : ℝ) : ℝ) : ℂ) * Complex.I = period 1 := by simp [period]
    rw [turn]
    exact congrArg Subtype.val (exp_firstRoot 1)

theorem advanceLoop_avoids_one (t : I) : advanceLoop t ≠ (⟨1, one_ne_zero⟩ : Punctured) := by
  intro same
  have exponential : Complex.exp (1 + (((2 * Real.pi) * (t : ℝ) : ℝ) : ℂ) * Complex.I) = 1 :=
    congrArg Subtype.val same
  obtain ⟨n, period_eq⟩ := Complex.exp_eq_one_iff.mp exponential
  have real_eq := congrArg Complex.re period_eq
  simp at real_eq

private def advanceWitness (k : ℤ) : C(I, ℂ) where
  toFun t := firstRoot k + (((2 * Real.pi) * (t : ℝ) : ℝ) : ℂ) * Complex.I
  continuous_toFun := by fun_prop

private theorem advanceWitness_start (k : ℤ) : advanceWitness k 0 = firstRoot k := by
  simp [advanceWitness]

private theorem advanceWitness_end (k : ℤ) : advanceWitness k 1 = firstRoot (k + 1) := by
  simp [advanceWitness, firstRoot, period]
  ring

private theorem advanceWitness_slit (k : ℤ) (t : I) : advanceWitness k t ∈ Complex.slitPlane := by
  left
  simp [advanceWitness, firstRoot, period]

private theorem advanceWitness_projects (k : ℤ) : expCover ∘ advanceWitness k = advanceLoop := by
  funext t
  apply Subtype.ext
  change Complex.exp (firstRoot k + (((2 * Real.pi) * (t : ℝ) : ℝ) : ℂ) * Complex.I) =
    Complex.exp (1 + (((2 * Real.pi) * (t : ℝ) : ℝ) : ℂ) * Complex.I)
  unfold firstRoot
  rw [add_right_comm, Complex.exp_add, exp_period, mul_one]

private theorem advance_firstRaw (k m : ℤ) : firstRaw advanceLoop (prepare k m) = advanceWitness k := by
  have same : advanceWitness k = firstRaw advanceLoop (prepare k m) :=
    (covering.eq_liftPath_iff' (advanceLoop.source.trans (prepare k m).property.symm)).mpr
      ⟨advanceWitness_projects k, by rw [advanceWitness_start]; exact (exp_secondRoot k m).symm⟩
  exact same.symm

private def advanceSecondWitness (k m : ℤ) : C(I, ℂ) where
  toFun t := Complex.log (advanceWitness k t) + period m
  continuous_toFun := ((advanceWitness k).continuous.clog (advanceWitness_slit k)).add continuous_const

private theorem advance_secondRaw (k m : ℤ) :
    secondRaw advanceLoop advanceLoop_avoids_one (prepare k m) = advanceSecondWitness k m := by
  have projects : expCover ∘ advanceSecondWitness k m = firstRawPath advanceLoop advanceLoop_avoids_one (prepare k m) := by
    funext t
    apply Subtype.ext
    change Complex.exp (Complex.log (advanceWitness k t) + period m) = firstRaw advanceLoop (prepare k m) t
    rw [Complex.exp_add, exp_period, mul_one,
      Complex.exp_log (Complex.slitPlane_ne_zero (advanceWitness_slit k t)), advance_firstRaw]
  have same : advanceSecondWitness k m = secondRaw advanceLoop advanceLoop_avoids_one (prepare k m) :=
    (covering.eq_liftPath_iff' (firstRawPath advanceLoop advanceLoop_avoids_one (prepare k m)).source).mpr
      ⟨projects, by
        change Complex.log (advanceWitness k 0) + period m = secondRoot k m
        rw [advanceWitness_start]
        rfl⟩
  exact same.symm

/-- The other fixed loop advances the lower branch, retaining the upper branch. -/
theorem execute_advance (k m : ℤ) :
    execute advanceLoop advanceLoop_avoids_one (prepare k m) = prepare (k + 1) m := by
  apply Subtype.ext
  change secondRaw advanceLoop advanceLoop_avoids_one (prepare k m) 1 = secondRoot (k + 1) m
  rw [advance_secondRaw]
  change Complex.log (advanceWitness k 1) + period m = _
  rw [advanceWitness_end]
  rfl

end Monodromy.NestedContinuation


namespace Monodromy.NestedContinuation

theorem period_injective : Function.Injective period := by
  intro first second same
  have factor : (2 * Real.pi * Complex.I : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  unfold period at same
  exact_mod_cast mul_right_cancel₀ factor same

theorem firstRoot_injective : Function.Injective firstRoot := by
  intro first second same
  exact period_injective (add_left_cancel same)

theorem secondRoot_injective : Function.Injective (fun state : ℤ × ℤ => secondRoot state.1 state.2) := by
  rintro ⟨first_lower, first_upper⟩ ⟨second_lower, second_upper⟩ same
  change secondRoot first_lower first_upper = secondRoot second_lower second_upper at same
  have roots : firstRoot first_lower = firstRoot second_lower := by
    rw [← exp_secondRoot first_lower first_upper, ← exp_secondRoot second_lower second_upper, same]
  have controls := firstRoot_injective roots
  subst second_lower
  have memories : first_upper = second_upper := by
    apply period_injective
    exact add_left_cancel same
  subst second_upper
  rfl

/-- The branch indices are a proof-level presentation of the whole nested exponential fiber. -/
theorem secondRoot_complete (z : ℂ)
    (in_fiber : Complex.exp (Complex.exp z) = Complex.exp 1) :
    ∃ k m : ℤ, z = secondRoot k m := by
  obtain ⟨k, control⟩ := Complex.exp_eq_exp_iff_exists_int.mp in_fiber
  have first : Complex.exp z = firstRoot k := control
  have logs : Complex.exp z = Complex.exp (Complex.log (firstRoot k)) := by
    rw [Complex.exp_log (firstRoot_ne_zero k)]
    exact first
  obtain ⟨m, memory⟩ := Complex.exp_eq_exp_iff_exists_int.mp logs
  exact ⟨k, m, memory⟩


end Monodromy.NestedContinuation

namespace Monodromy.NestedContinuation

open unitInterval

/-- Two actual covering uniqueness laws give uniqueness of the nested lift. -/
theorem nested_curve_unique (first second : C(I, ℂ))
    (projects : ∀ t, expCover (Complex.exp (first t)) = expCover (Complex.exp (second t)))
    (starts : first 0 = second 0) : first = second := by
  have middle : (fun t => Complex.exp (first t)) = (fun t => Complex.exp (second t)) :=
    covering.eq_of_comp_eq
      (Complex.continuous_exp.comp first.continuous)
      (Complex.continuous_exp.comp second.continuous)
      (funext projects) 0 (congrArg Complex.exp starts)
  have upper : expCover ∘ first = expCover ∘ second := by
    funext t
    apply Subtype.ext
    exact congrFun middle t
  ext t
  exact congrFun (covering.eq_of_comp_eq first.continuous second.continuous upper 0 starts) t

/-- A composite program still avoids the excluded singular value. -/
theorem avoids_trans (first second : Path base base)
    (first_avoids : ∀ t, first t ≠ (⟨1, one_ne_zero⟩ : Punctured))
    (second_avoids : ∀ t, second t ≠ (⟨1, one_ne_zero⟩ : Punctured)) :
    ∀ t, (first.trans second) t ≠ (⟨1, one_ne_zero⟩ : Punctured) := by
  intro t
  rw [Path.trans_apply]
  split_ifs
  · exact first_avoids _
  · exact second_avoids _

theorem avoids_symm (path : Path base base)
    (avoids : ∀ t, path t ≠ (⟨1, one_ne_zero⟩ : Punctured)) :
    ∀ t, path.symm t ≠ (⟨1, one_ne_zero⟩ : Punctured) := by
  intro t
  exact avoids (σ t)

/-- This path is the actual second lift itself, with its proved start and end. -/
def executionPath (path : Path base base)
    (avoids : ∀ t, path t ≠ (⟨1, one_ne_zero⟩ : Punctured)) (state : Memory) :
    Path state.val (execute path avoids state).val where
  toFun := secondRaw path avoids state
  continuous_toFun := (secondRaw path avoids state).continuous
  source' := secondRaw_start path avoids state
  target' := rfl

theorem executionPath_projects (path : Path base base)
    (avoids : ∀ t, path t ≠ (⟨1, one_ne_zero⟩ : Punctured)) (state : Memory) (t : I) :
    expCover (Complex.exp (executionPath path avoids state t)) = path t :=
  secondRaw_projects path avoids state t

/-- Later execution begins at the actual retained endpoint of the preceding lift. -/
def sequentialPath (first second : Path base base)
    (first_avoids : ∀ t, first t ≠ (⟨1, one_ne_zero⟩ : Punctured))
    (second_avoids : ∀ t, second t ≠ (⟨1, one_ne_zero⟩ : Punctured)) (state : Memory) :
    Path state.val (execute second second_avoids (execute first first_avoids state)).val :=
  (executionPath first first_avoids state).trans
    (executionPath second second_avoids (execute first first_avoids state))

theorem sequentialPath_projects (first second : Path base base)
    (first_avoids : ∀ t, first t ≠ (⟨1, one_ne_zero⟩ : Punctured))
    (second_avoids : ∀ t, second t ≠ (⟨1, one_ne_zero⟩ : Punctured)) (state : Memory) (t : I) :
    expCover (Complex.exp (sequentialPath first second first_avoids second_avoids state t)) =
      (first.trans second) t := by
  unfold sequentialPath
  simp only [Path.trans_apply]
  split_ifs
  · exact executionPath_projects first first_avoids state _
  · exact executionPath_projects second second_avoids (execute first first_avoids state) _

/-- Program concatenation composes actual nested execution, without decoding branch indices. -/
theorem execute_trans (first second : Path base base)
    (first_avoids : ∀ t, first t ≠ (⟨1, one_ne_zero⟩ : Punctured))
    (second_avoids : ∀ t, second t ≠ (⟨1, one_ne_zero⟩ : Punctured)) (state : Memory) :
    execute (first.trans second) (avoids_trans first second first_avoids second_avoids) state =
      execute second second_avoids (execute first first_avoids state) := by
  apply Subtype.ext
  let joined := sequentialPath first second first_avoids second_avoids state
  have same : secondRaw (first.trans second)
      (avoids_trans first second first_avoids second_avoids) state = joined.toContinuousMap :=
    nested_curve_unique _ _
      (fun t => (secondRaw_projects (first.trans second)
        (avoids_trans first second first_avoids second_avoids) state t).trans
          (sequentialPath_projects first second first_avoids second_avoids state t).symm)
      ((secondRaw_start (first.trans second)
        (avoids_trans first second first_avoids second_avoids) state).trans joined.source.symm)
  exact (congrArg (fun curve : C(I, ℂ) => curve 1) same).trans joined.target

/-- Reversing the fixed base path reverses the actual complete nested lift. -/
theorem execute_reverse (path : Path base base)
    (avoids : ∀ t, path t ≠ (⟨1, one_ne_zero⟩ : Punctured)) (state : Memory) :
    execute path.symm (avoids_symm path avoids) (execute path avoids state) = state := by
  apply Subtype.ext
  let backwards := (executionPath path avoids state).symm
  have projects : ∀ t, expCover (Complex.exp (backwards t)) = path.symm t := by
    intro t
    exact executionPath_projects path avoids state (σ t)
  have same : secondRaw path.symm (avoids_symm path avoids) (execute path avoids state) =
      backwards.toContinuousMap :=
    nested_curve_unique _ _
      (fun t => (secondRaw_projects path.symm (avoids_symm path avoids)
        (execute path avoids state) t).trans (projects t).symm)
      ((secondRaw_start path.symm (avoids_symm path avoids)
        (execute path avoids state)).trans backwards.source.symm)
  exact (congrArg (fun curve : C(I, ℂ) => curve 1) same).trans backwards.target

/-- Every actual nested-execution state has one of the displayed branch presentations. -/
theorem prepare_surjective : Function.Surjective (fun state : ℤ × ℤ => prepare state.1 state.2) := by
  intro state
  obtain ⟨k, m, same⟩ := secondRoot_complete state.val (congrArg Subtype.val state.property)
  refine ⟨(k, m), ?_⟩
  apply Subtype.ext
  exact same.symm

theorem prepare_injective : Function.Injective (fun state : ℤ × ℤ => prepare state.1 state.2) := by
  intro first second same
  exact secondRoot_injective (congrArg Subtype.val same)

end Monodromy.NestedContinuation

namespace Monodromy.NestedContinuation

/-- Repetition uses the raw root operation; integer labels appear only in this theorem. -/
theorem iterate_execute_prepare (k m : ℤ) (rounds : ℕ) :
    (execute loop loop_avoids_one)^[rounds] (prepare k m) =
      prepare k (m + (rounds : ℤ) * if k = 0 then 1 else 0) := by
  induction rounds with
  | zero => simp
  | succ rounds induction_hypothesis =>
      rw [Function.iterate_succ_apply', induction_hypothesis, execute_prepare]
      congr 1
      push_cast
      ring

/-- Zero memory changes the actual retained control root. -/
theorem execute_zero_changes (m : ℤ) :
    execute loop loop_avoids_one (prepare 0 m) ≠ prepare 0 m := by
  rw [execute_prepare]
  intro same
  have roots := congrArg Subtype.val same
  have labels : ((0 : ℤ), m + 1) = (0, m) := secondRoot_injective roots
  have memories := congrArg Prod.snd labels
  omega

theorem execute_zero_value_ne (m : ℤ) :
    (execute loop loop_avoids_one (prepare 0 m)).val ≠ (prepare 0 m).val := by
  intro same
  exact execute_zero_changes m (Subtype.ext same)

/-- Every nonzero memory branch fixes the retained control under the same loop. -/
theorem execute_nonzero_stays {k : ℤ} (nonzero : k ≠ 0) (m : ℤ) :
    execute loop loop_avoids_one (prepare k m) = prepare k m := by
  rw [execute_prepare]
  simp [nonzero]

end Monodromy.NestedContinuation


namespace Monodromy.NestedContinuation

/-- A hand-verifiable path program: shift, conditional write, shift, conditional write. -/
theorem example_run :
    execute loop loop_avoids_one
      (execute advanceLoop advanceLoop_avoids_one
        (execute loop loop_avoids_one
          (execute advanceLoop advanceLoop_avoids_one (prepare (-1) 0)))) =
      prepare 1 1 := by
  rw [execute_advance, execute_prepare, execute_advance, execute_prepare]
  norm_num

/-- The two fixed-loop operations compose noncommutatively on the same retained root. -/
theorem operations_noncommute :
    ¬ Function.Commute (execute advanceLoop advanceLoop_avoids_one)
      (execute loop loop_avoids_one) := by
  intro commutes
  have same := commutes (prepare 0 0)
  rw [execute_prepare, execute_advance, execute_advance, execute_prepare] at same
  have endpoints : prepare 1 1 = prepare 1 0 := by simpa using same
  have labels : ((1 : ℤ), (1 : ℤ)) = (1, 0) := @prepare_injective (1, 1) (1, 0) endpoints
  norm_num at labels

end Monodromy.NestedContinuation


namespace Monodromy.NestedContinuation

theorem execute_after_reverse (path : Path base base)
    (avoids : ∀ t, path t ≠ (⟨1, one_ne_zero⟩ : Punctured)) (state : Memory) :
    execute path avoids (execute path.symm (avoids_symm path avoids) state) = state := by
  have reversed := execute_reverse path.symm (avoids_symm path avoids) state
  simpa only [Path.symm_symm] using reversed


end Monodromy.NestedContinuation


namespace Monodromy.NestedRestricted

open unitInterval

noncomputable section

def baseSet : Set ℂ := {value | value ≠ 0 ∧ value ≠ 1}
def firstSet : Set ℂ := Complex.exp ⁻¹' baseSet
def secondSet : Set ℂ := Complex.exp ⁻¹' firstSet

def firstProjection : firstSet → baseSet := baseSet.restrictPreimage Complex.exp
def secondProjection : secondSet → firstSet := firstSet.restrictPreimage Complex.exp

theorem firstCovering : IsCoveringMap firstProjection :=
  (Complex.isCoveringMapOn_exp.mono (by
    intro value valid
    exact valid.1)).isCoveringMap_restrictPreimage

theorem firstSet_nonzero {value : ℂ} (valid : value ∈ firstSet) : value ≠ 0 := by
  intro zero
  have avoids_one : Complex.exp value ≠ 1 := valid.2
  apply avoids_one
  simp [zero]

theorem secondCovering : IsCoveringMap secondProjection :=
  (Complex.isCoveringMapOn_exp.mono (by
    intro value valid
    exact firstSet_nonzero valid)).isCoveringMap_restrictPreimage

@[simp] theorem firstProjection_value (value : firstSet) :
    (firstProjection value : ℂ) = Complex.exp (value : ℂ) := rfl

@[simp] theorem secondProjection_value (value : secondSet) :
    (secondProjection value : ℂ) = Complex.exp (value : ℂ) := rfl

theorem composite_value (value : secondSet) :
    (firstProjection (secondProjection value) : ℂ) =
      Complex.exp (Complex.exp (value : ℂ)) := rfl

/-- The fixed admissible paths are paths in the common twice-punctured base. -/
def basePath {start finish : {value : ℂ // value ≠ 0}}
    (path : Path start finish) (avoids_one : ∀ t : I, (path t : ℂ) ≠ 1) :
    Path (⟨start.val, start.property, by simpa using avoids_one 0⟩ : baseSet)
      ⟨finish.val, finish.property, by simpa using avoids_one 1⟩ where
  toFun t := ⟨path t, (path t).property, avoids_one t⟩
  continuous_toFun := (path.continuous.subtype_val).subtype_mk _
  source' := by
    apply Subtype.ext
    exact congrArg (fun value : {value : ℂ // value ≠ 0} => (value : ℂ)) path.source
  target' := by
    apply Subtype.ext
    exact congrArg (fun value : {value : ℂ // value ≠ 0} => (value : ℂ)) path.target

end

end Monodromy.NestedRestricted


namespace Monodromy.NestedContinuation

open unitInterval

/-- The actual first lift stays in the total space of the first restricted cover. -/
theorem firstRaw_mem (path : Path base base)
    (avoids : ∀ t, path t ≠ (⟨1, one_ne_zero⟩ : Punctured)) (state : Memory) (t : I) :
    firstRaw path state t ∈ NestedRestricted.firstSet := by
  change Complex.exp (firstRaw path state t) ≠ 0 ∧ Complex.exp (firstRaw path state t) ≠ 1
  refine ⟨Complex.exp_ne_zero _, ?_⟩
  intro one
  apply avoids t
  apply Subtype.ext
  exact (congrArg Subtype.val (congrFun (firstRaw_projects path state) t)).symm.trans one

/-- The actual second lift stays in the total space of the second restricted cover. -/
theorem secondRaw_mem (path : Path base base)
    (avoids : ∀ t, path t ≠ (⟨1, one_ne_zero⟩ : Punctured)) (state : Memory) (t : I) :
    secondRaw path avoids state t ∈ NestedRestricted.secondSet := by
  change Complex.exp (secondRaw path avoids state t) ∈ NestedRestricted.firstSet
  rw [secondRaw_exp]
  exact firstRaw_mem path avoids state t

def lowerCurve (path : Path base base)
    (avoids : ∀ t, path t ≠ (⟨1, one_ne_zero⟩ : Punctured)) (state : Memory) :
    C(I, NestedRestricted.firstSet) where
  toFun t := ⟨firstRaw path state t, firstRaw_mem path avoids state t⟩
  continuous_toFun := (firstRaw path state).continuous.subtype_mk _

def upperCurve (path : Path base base)
    (avoids : ∀ t, path t ≠ (⟨1, one_ne_zero⟩ : Punctured)) (state : Memory) :
    C(I, NestedRestricted.secondSet) where
  toFun t := ⟨secondRaw path avoids state t, secondRaw_mem path avoids state t⟩
  continuous_toFun := (secondRaw path avoids state).continuous.subtype_mk _

/-- The two restricted covering maps carry the entire actual execution diagram. -/
theorem restricted_projection (path : Path base base)
    (avoids : ∀ t, path t ≠ (⟨1, one_ne_zero⟩ : Punctured)) (state : Memory) (t : I) :
    NestedRestricted.secondProjection (upperCurve path avoids state t) = lowerCurve path avoids state t ∧
      (NestedRestricted.firstProjection (lowerCurve path avoids state t) : ℂ) = (path t : ℂ) := by
  constructor
  · apply Subtype.ext
    exact secondRaw_exp path avoids state t
  · exact congrArg Subtype.val (congrFun (firstRaw_projects path state) t)

end Monodromy.NestedContinuation
