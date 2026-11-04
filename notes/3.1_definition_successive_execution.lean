module

public import Monodromy.Logarithm
public import Monodromy.Radix
public import Mathlib.Computability.StateTransition
public import Mathlib.Data.Fintype.Card
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Analytic.Linear
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

@[expose] public section

/-!
# Coupled analytic continuation

Two retained logarithmic memory roots share one upper control root through
`F(w₁,w₂,z) = (exp w₁, exp w₂, exp z / (w₁*w₂))`. The two actual lower
lifts generate the upper input path. The returned root is the actual upper
lift endpoint; integer labels occur only in preparation and proofs.

The matching lower product covering and upper pullback covering are explicit.
Their actual lifts agree with the complete runtime curves. Five fixed loops
provide memory shifts, zero-conditional control writes and a control shift.
Concatenation and reversal follow from lift uniqueness. A finite power-root
observation routes whole base paths by normalized analytic kernels at returns.

Five oriented loops give a finite word language and finite root-controlled
program tables with internal stopping. Effective semantics and machine
simulation are proved in the subsequent research layers.
-/

noncomputable section

namespace Monodromy.CoupledContinuation

open unitInterval

abbrev Punctured := NestedContinuation.Punctured
abbrev Point := (Punctured × Punctured) × ℂ
abbrev Base := (Punctured × Punctured) × Punctured

abbrev one : Punctured := ⟨1, one_ne_zero⟩
def base : Base := ((NestedContinuation.base, NestedContinuation.base), one)

/-- One three-dimensional projection couples the upper logarithm to both lower roots. -/
def projection (point : Point) : Base :=
  ((NestedContinuation.expCover point.1.1.val, NestedContinuation.expCover point.1.2.val),
    ⟨Complex.exp point.2 / (point.1.1.val * point.1.2.val),
      div_ne_zero (Complex.exp_ne_zero _) (mul_ne_zero point.1.1.property point.1.2.property)⟩)

/-- Its coordinate expression on the open domain of nonzero lower coordinates. -/
def formula (point : (ℂ × ℂ) × ℂ) : (ℂ × ℂ) × ℂ :=
  ((Complex.exp point.1.1, Complex.exp point.1.2),
    Complex.exp point.2 / (point.1.1 * point.1.2))

attribute [local fun_prop] analyticAt_fst analyticAt_snd

theorem analyticAt_formula (point : (ℂ × ℂ) × ℂ)
    (left : point.1.1 ≠ 0) (right : point.1.2 ≠ 0) : AnalyticAt ℂ formula point := by
  unfold formula
  fun_prop (disch := aesop)

abbrev Memory := Transport.Fiber projection base

def lowerLeft (state : Memory) : Transport.Fiber NestedContinuation.expCover NestedContinuation.base :=
  ⟨state.val.1.1.val, congrArg (fun value : Base => value.1.1) state.property⟩

def lowerRight (state : Memory) : Transport.Fiber NestedContinuation.expCover NestedContinuation.base :=
  ⟨state.val.1.2.val, congrArg (fun value : Base => value.1.2) state.property⟩

theorem coherent (state : Memory) :
    Complex.exp state.val.2 = state.val.1.1.val * state.val.1.2.val := by
  have equality := congrArg (fun value : Base => value.2.val) state.property
  exact (div_eq_one_iff_eq (mul_ne_zero state.val.1.1.property state.val.1.2.property)).mp equality

/-- A driver is one based path in each coordinate of the same base space. -/
structure Driver where
  left : Path NestedContinuation.base NestedContinuation.base
  right : Path NestedContinuation.base NestedContinuation.base
  control : Path one one
  left_avoids : ∀ t, left t ≠ one
  right_avoids : ∀ t, right t ≠ one

def Driver.path (driver : Driver) : Path base base where
  toFun t := ((driver.left t, driver.right t), driver.control t)
  continuous_toFun := (driver.left.continuous.prodMk driver.right.continuous).prodMk driver.control.continuous
  source' := by simp [base]
  target' := by simp [base]

/-- Both lower trajectories are actual lifts from their retained root values. -/
def lower (path : Path NestedContinuation.base NestedContinuation.base) (root : Transport.Fiber NestedContinuation.expCover NestedContinuation.base) : C(I, ℂ) :=
  NestedContinuation.covering.liftPath path root.val (path.source.trans root.property.symm)

theorem lower_projects (path : Path NestedContinuation.base NestedContinuation.base) (root : Transport.Fiber NestedContinuation.expCover NestedContinuation.base) :
    NestedContinuation.expCover ∘ lower path root = path :=
  NestedContinuation.covering.liftPath_lifts path root.val (path.source.trans root.property.symm)

theorem lower_start (path : Path NestedContinuation.base NestedContinuation.base) (root : Transport.Fiber NestedContinuation.expCover NestedContinuation.base) :
    lower path root 0 = root.val :=
  NestedContinuation.covering.liftPath_zero path root.val (path.source.trans root.property.symm)

theorem lower_ne_zero (path : Path NestedContinuation.base NestedContinuation.base) (avoids : ∀ t, path t ≠ one)
    (root : Transport.Fiber NestedContinuation.expCover NestedContinuation.base) (t : I) : lower path root t ≠ 0 := by
  intro zero
  apply avoids t
  calc
    path t = NestedContinuation.expCover (lower path root t) := (congrFun (lower_projects path root) t).symm
    _ = NestedContinuation.expCover 0 := congrArg NestedContinuation.expCover zero
    _ = one := Subtype.ext Complex.exp_zero

def feed (driver : Driver) (state : Memory) : C(I, Punctured) where
  toFun t := ⟨(driver.control t).val *
      (lower driver.left (lowerLeft state) t * lower driver.right (lowerRight state) t),
    mul_ne_zero (driver.control t).property
      (mul_ne_zero (lower_ne_zero driver.left driver.left_avoids (lowerLeft state) t)
        (lower_ne_zero driver.right driver.right_avoids (lowerRight state) t))⟩
  continuous_toFun := ((continuous_subtype_val.comp driver.control.continuous).mul
    ((lower driver.left (lowerLeft state)).continuous.mul
      (lower driver.right (lowerRight state)).continuous)).subtype_mk _

/-- The upper input path is generated by the two actual lower lifts and the third base drive. -/
def upperPath (driver : Driver) (state : Memory) :
    Path (NestedContinuation.expCover state.val.2) (feed driver state 1) where
  toFun := feed driver state
  continuous_toFun := (feed driver state).continuous
  source' := by
    apply Subtype.ext
    change (driver.control 0).val *
      (lower driver.left (lowerLeft state) 0 * lower driver.right (lowerRight state) 0) =
      Complex.exp state.val.2
    rw [driver.control.source, lower_start, lower_start]
    exact (one_mul _).trans (coherent state).symm
  target' := rfl

/-- Upper computation is another actual lift, with no target state supplied. -/
def upper (driver : Driver) (state : Memory) : C(I, ℂ) :=
  NestedContinuation.covering.liftPath (upperPath driver state) state.val.2 (upperPath driver state).source

theorem upper_projects (driver : Driver) (state : Memory) (t : I) :
    Complex.exp (upper driver state t) =
      (driver.control t).val *
        (lower driver.left (lowerLeft state) t * lower driver.right (lowerRight state) t) := by
  have projects := NestedContinuation.covering.liftPath_lifts (upperPath driver state) state.val.2
    (upperPath driver state).source
  exact congrArg Subtype.val (congrFun projects t)

theorem upper_start (driver : Driver) (state : Memory) : upper driver state 0 = state.val.2 :=
  NestedContinuation.covering.liftPath_zero (upperPath driver state) state.val.2 (upperPath driver state).source

def trajectory (driver : Driver) (state : Memory) : C(I, Point) where
  toFun t := ((⟨lower driver.left (lowerLeft state) t,
      lower_ne_zero driver.left driver.left_avoids (lowerLeft state) t⟩,
    ⟨lower driver.right (lowerRight state) t,
      lower_ne_zero driver.right driver.right_avoids (lowerRight state) t⟩), upper driver state t)
  continuous_toFun := (((lower driver.left (lowerLeft state)).continuous.subtype_mk _).prodMk
    ((lower driver.right (lowerRight state)).continuous.subtype_mk _)).prodMk
      (upper driver state).continuous

theorem trajectory_start (driver : Driver) (state : Memory) : trajectory driver state 0 = state.val := by
  apply Prod.ext
  · apply Prod.ext <;> apply Subtype.ext
    · exact lower_start driver.left (lowerLeft state)
    · exact lower_start driver.right (lowerRight state)
  · exact upper_start driver state

/-- The whole three-dimensional trajectory follows the one fixed coupled projection. -/
theorem trajectory_projects (driver : Driver) (state : Memory) (t : I) :
    projection (trajectory driver state t) = driver.path t := by
  apply Prod.ext
  · apply Prod.ext
    · exact congrFun (lower_projects driver.left (lowerLeft state)) t
    · exact congrFun (lower_projects driver.right (lowerRight state)) t
  · apply Subtype.ext
    change Complex.exp (upper driver state t) /
      (lower driver.left (lowerLeft state) t * lower driver.right (lowerRight state) t) =
      (driver.control t).val
    rw [upper_projects]
    exact mul_div_cancel_right₀ _
      (mul_ne_zero (lower_ne_zero driver.left driver.left_avoids (lowerLeft state) t)
        (lower_ne_zero driver.right driver.right_avoids (lowerRight state) t))

def execute (driver : Driver) (state : Memory) : Memory :=
  ⟨trajectory driver state 1, (trajectory_projects driver state 1).trans driver.path.target⟩

def rotorPath : Path one one where
  toFun t := ⟨NestedContinuation.rotor t, NestedContinuation.rotor_ne_zero t⟩
  continuous_toFun := NestedContinuation.continuous_rotor.subtype_mk _
  source' := by apply Subtype.ext; exact NestedContinuation.rotor_zero
  target' := by apply Subtype.ext; exact NestedContinuation.rotor_one

theorem base_ne_one : NestedContinuation.base ≠ one := by
  intro same
  exact NestedContinuation.advanceLoop_avoids_one 0 (NestedContinuation.advanceLoop.source.trans same)

/-- This fixed base loop rotates the control drive and holds both lower inputs fixed. -/
def controlTurn : Driver where
  left := Path.refl NestedContinuation.base
  right := Path.refl NestedContinuation.base
  control := rotorPath
  left_avoids := fun _ => base_ne_one
  right_avoids := fun _ => base_ne_one

theorem lower_refl (root : Transport.Fiber NestedContinuation.expCover NestedContinuation.base) (t : I) :
    lower (Path.refl NestedContinuation.base) root t = root.val := by
  let curve : C(I, ℂ) := ContinuousMap.const I root.val
  have same : curve = lower (Path.refl NestedContinuation.base) root :=
    (NestedContinuation.covering.eq_liftPath_iff' ((Path.refl NestedContinuation.base).source.trans root.property.symm)).mpr
      ⟨by funext u; exact root.property, rfl⟩
  exact congrArg (fun value : C(I, ℂ) => value t) same.symm

private def controlWitness (state : Memory) : C(I, ℂ) where
  toFun t := state.val.2 + (((2 * Real.pi) * (t : ℝ) : ℝ) : ℂ) * Complex.I
  continuous_toFun := by fun_prop

private theorem controlWitness_projects (state : Memory) :
    NestedContinuation.expCover ∘ controlWitness state = upperPath controlTurn state := by
  funext t
  apply Subtype.ext
  change Complex.exp (state.val.2 + (((2 * Real.pi) * (t : ℝ) : ℝ) : ℂ) * Complex.I) =
    NestedContinuation.rotor t *
      (lower (Path.refl NestedContinuation.base) (lowerLeft state) t * lower (Path.refl NestedContinuation.base) (lowerRight state) t)
  rw [Complex.exp_add, lower_refl, lower_refl, coherent]
  rw [show Complex.exp ((((2 * Real.pi) * (t : ℝ) : ℝ) : ℂ) * Complex.I) = NestedContinuation.rotor t from
    (Circle.coe_exp _).symm]
  dsimp only [lowerLeft, lowerRight]
  ring

private theorem upper_controlTurn (state : Memory) : upper controlTurn state = controlWitness state := by
  have same : controlWitness state = upper controlTurn state :=
    (NestedContinuation.covering.eq_liftPath_iff' (upperPath controlTurn state).source).mpr
      ⟨controlWitness_projects state, by simp [controlWitness]⟩
  exact same.symm

/-- The control primitive is proved from its actual upper lift; both memories persist. -/
theorem execute_controlTurn (state : Memory) :
    (execute controlTurn state).val.1 = state.val.1 ∧
      (execute controlTurn state).val.2 = state.val.2 + NestedContinuation.period 1 := by
  constructor
  · apply Prod.ext <;> apply Subtype.ext
    · exact lower_refl (lowerLeft state) 1
    · exact lower_refl (lowerRight state) 1
  · change upper controlTurn state 1 = _
    rw [upper_controlTurn]
    simp [controlWitness, NestedContinuation.period]


/-- The three independent branch labels occur only in preparation and correctness statements. -/
def upperRoot (left right control : ℤ) : ℂ :=
  Complex.log (NestedContinuation.firstRoot left) +
    Complex.log (NestedContinuation.firstRoot right) + NestedContinuation.period control

theorem exp_upperRoot (left right control : ℤ) :
    Complex.exp (upperRoot left right control) =
      NestedContinuation.firstRoot left * NestedContinuation.firstRoot right := by
  rw [upperRoot, Complex.exp_add, Complex.exp_add, NestedContinuation.exp_period,
    Complex.exp_log (NestedContinuation.firstRoot_ne_zero left),
    Complex.exp_log (NestedContinuation.firstRoot_ne_zero right), mul_one]

def prepare (left right control : ℤ) : Memory :=
  ⟨((⟨NestedContinuation.firstRoot left, NestedContinuation.firstRoot_ne_zero left⟩,
    ⟨NestedContinuation.firstRoot right, NestedContinuation.firstRoot_ne_zero right⟩),
      upperRoot left right control), by
    apply Prod.ext
    · apply Prod.ext
      · exact NestedContinuation.exp_firstRoot left
      · exact NestedContinuation.exp_firstRoot right
    · apply Subtype.ext
      change Complex.exp (upperRoot left right control) /
        (NestedContinuation.firstRoot left * NestedContinuation.firstRoot right) = 1
      rw [exp_upperRoot, div_self
        (mul_ne_zero (NestedContinuation.firstRoot_ne_zero left)
          (NestedContinuation.firstRoot_ne_zero right))]⟩

theorem execute_control_prepare (left right control : ℤ) :
    execute controlTurn (prepare left right control) = prepare left right (control + 1) := by
  apply Subtype.ext
  apply Prod.ext
  · exact (execute_controlTurn (prepare left right control)).1
  · rw [(execute_controlTurn (prepare left right control)).2]
    change upperRoot left right control + NestedContinuation.period 1 =
      upperRoot left right (control + 1)
    simp [upperRoot, NestedContinuation.period]
    ring


/-- The same fixed lower loop can act on the left memory while the other base coordinates rest. -/
def leftDriver (path : Path NestedContinuation.base NestedContinuation.base)
    (avoids : ∀ t, path t ≠ one) : Driver where
  left := path
  right := Path.refl NestedContinuation.base
  control := Path.refl one
  left_avoids := avoids
  right_avoids := fun _ => base_ne_one

private theorem lower_left_prepare (path : Path NestedContinuation.base NestedContinuation.base)
    (left right control : ℤ) :
    lower path (lowerLeft (prepare left right control)) =
      NestedContinuation.firstRaw path (NestedContinuation.prepare left control) :=
  (NestedContinuation.covering.eq_liftPath_iff'
    (path.source.trans (NestedContinuation.prepare left control).property.symm)).mpr
    ⟨lower_projects path (lowerLeft (prepare left right control)), by
      rw [lower_start]
      exact (NestedContinuation.exp_secondRoot left control).symm⟩

/-- A proof witness reuses the already verified nested lift; it is absent from execution. -/
private def leftWitness (path : Path NestedContinuation.base NestedContinuation.base)
    (avoids : ∀ t, path t ≠ one) (left right control : ℤ) : C(I, ℂ) where
  toFun t := NestedContinuation.secondRaw path avoids
    (NestedContinuation.prepare left control) t + Complex.log (NestedContinuation.firstRoot right)
  continuous_toFun := (NestedContinuation.secondRaw path avoids
    (NestedContinuation.prepare left control)).continuous.add continuous_const

private theorem leftWitness_projects (path : Path NestedContinuation.base NestedContinuation.base)
    (avoids : ∀ t, path t ≠ one) (left right control : ℤ) :
    NestedContinuation.expCover ∘ leftWitness path avoids left right control =
      upperPath (leftDriver path avoids) (prepare left right control) := by
  funext t
  apply Subtype.ext
  change Complex.exp (NestedContinuation.secondRaw path avoids
      (NestedContinuation.prepare left control) t + Complex.log (NestedContinuation.firstRoot right)) =
    (1 : ℂ) * (lower path (lowerLeft (prepare left right control)) t *
      lower (Path.refl NestedContinuation.base) (lowerRight (prepare left right control)) t)
  rw [Complex.exp_add, Complex.exp_log (NestedContinuation.firstRoot_ne_zero right),
    NestedContinuation.secondRaw_exp, one_mul, lower_refl, lower_left_prepare]
  rfl

private theorem upper_left_prepare (path : Path NestedContinuation.base NestedContinuation.base)
    (avoids : ∀ t, path t ≠ one) (left right control : ℤ) :
    upper (leftDriver path avoids) (prepare left right control) = leftWitness path avoids left right control := by
  have same : leftWitness path avoids left right control =
      upper (leftDriver path avoids) (prepare left right control) :=
    (NestedContinuation.covering.eq_liftPath_iff'
      (upperPath (leftDriver path avoids) (prepare left right control)).source).mpr
      ⟨leftWitness_projects path avoids left right control, by
        change NestedContinuation.secondRaw path avoids
          (NestedContinuation.prepare left control) 0 + Complex.log (NestedContinuation.firstRoot right) =
          upperRoot left right control
        rw [NestedContinuation.secondRaw_start]
        change NestedContinuation.secondRoot left control + Complex.log (NestedContinuation.firstRoot right) = _
        unfold NestedContinuation.secondRoot upperRoot
        ring⟩
  exact same.symm

/-- A native nested-loop action lifts to the coupled space with the opposite memory retained. -/
theorem execute_left_refinement (path : Path NestedContinuation.base NestedContinuation.base)
    (avoids : ∀ t, path t ≠ one) (left right control nextLeft nextControl : ℤ)
    (result : NestedContinuation.execute path avoids (NestedContinuation.prepare left control) =
      NestedContinuation.prepare nextLeft nextControl) :
    execute (leftDriver path avoids) (prepare left right control) = prepare nextLeft right nextControl := by
  have endpoint := congrArg (fun state : NestedContinuation.Memory => state.val) result
  change NestedContinuation.secondRaw path avoids (NestedContinuation.prepare left control) 1 =
    NestedContinuation.secondRoot nextLeft nextControl at endpoint
  apply Subtype.ext
  apply Prod.ext
  · apply Prod.ext <;> apply Subtype.ext
    · change lower path (lowerLeft (prepare left right control)) 1 = NestedContinuation.firstRoot nextLeft
      rw [lower_left_prepare, ← NestedContinuation.secondRaw_exp path avoids
        (NestedContinuation.prepare left control) 1, endpoint, NestedContinuation.exp_secondRoot]
    · exact lower_refl (lowerRight (prepare left right control)) 1
  · change upper (leftDriver path avoids) (prepare left right control) 1 = upperRoot nextLeft right nextControl
    rw [upper_left_prepare]
    change NestedContinuation.secondRaw path avoids (NestedContinuation.prepare left control) 1 +
      Complex.log (NestedContinuation.firstRoot right) = _
    rw [endpoint]
    unfold NestedContinuation.secondRoot upperRoot
    ring

def A_left : Driver :=
  leftDriver NestedContinuation.advanceLoop NestedContinuation.advanceLoop_avoids_one

def B_left : Driver :=
  leftDriver NestedContinuation.loop NestedContinuation.loop_avoids_one

theorem execute_A_left (left right control : ℤ) :
    execute A_left (prepare left right control) = prepare (left + 1) right control :=
  execute_left_refinement _ _ left right control (left + 1) control
    (NestedContinuation.execute_advance left control)

theorem execute_B_left (left right control : ℤ) :
    execute B_left (prepare left right control) = prepare left right (control + if left = 0 then 1 else 0) :=
  execute_left_refinement _ _ left right control left (control + if left = 0 then 1 else 0)
    (NestedContinuation.execute_prepare left control)


/-- The fixed coupled projection determines every continuous lift from its initial point. -/
theorem coupled_curve_unique (first second : C(I, Point))
    (projects : ∀ t, projection (first t) = projection (second t))
    (starts : first 0 = second 0) : first = second := by
  have left_same : (fun t => (first t).1.1.val) = (fun t => (second t).1.1.val) :=
    NestedContinuation.covering.eq_of_comp_eq
      (by fun_prop) (by fun_prop)
      (funext (fun t => congrArg (fun value : Base => value.1.1) (projects t))) 0
      (congrArg (fun value : Point => value.1.1.val) starts)
  have right_same : (fun t => (first t).1.2.val) = (fun t => (second t).1.2.val) :=
    NestedContinuation.covering.eq_of_comp_eq
      (by fun_prop) (by fun_prop)
      (funext (fun t => congrArg (fun value : Base => value.1.2) (projects t))) 0
      (congrArg (fun value : Point => value.1.2.val) starts)
  have upper_projects : NestedContinuation.expCover ∘ (fun t => (first t).2) =
      NestedContinuation.expCover ∘ (fun t => (second t).2) := by
    funext t
    apply Subtype.ext
    have ratio := congrArg (fun value : Base => value.2.val) (projects t)
    change Complex.exp (first t).2 / ((first t).1.1.val * (first t).1.2.val) =
      Complex.exp (second t).2 / ((second t).1.1.val * (second t).1.2.val) at ratio
    rw [congrFun left_same t, congrFun right_same t] at ratio
    exact (div_left_inj' (mul_ne_zero (second t).1.1.property (second t).1.2.property)).mp ratio
  have upper_same : (fun t => (first t).2) = (fun t => (second t).2) :=
    NestedContinuation.covering.eq_of_comp_eq (by fun_prop) (by fun_prop) upper_projects 0
      (congrArg (fun value : Point => value.2) starts)
  apply ContinuousMap.ext
  intro t
  apply Prod.ext
  · apply Prod.ext <;> apply Subtype.ext
    · exact congrFun left_same t
    · exact congrFun right_same t
  · exact congrFun upper_same t


/-- Exchange is a relabelling of the two existing memory coordinates. -/
private def exchangePoint (point : Point) : Point := (point.1.swap, point.2)

private def exchangeBase (value : Base) : Base := (value.1.swap, value.2)

private theorem projection_exchange (point : Point) :
    projection (exchangePoint point) = exchangeBase (projection point) := by
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    change Complex.exp point.2 / (point.1.2.val * point.1.1.val) =
      Complex.exp point.2 / (point.1.1.val * point.1.2.val)
    rw [mul_comm point.1.2.val point.1.1.val]

private def exchange (state : Memory) : Memory :=
  ⟨exchangePoint state.val, by
    change projection (exchangePoint state.val) = base
    rw [projection_exchange, state.property]
    rfl⟩

private theorem exchange_prepare (left right control : ℤ) :
    exchange (prepare left right control) = prepare right left control := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change upperRoot left right control = upperRoot right left control
    unfold upperRoot
    ring

/-- The same prescribed base paths with their two memory roles exchanged. -/
def Driver.exchange (driver : Driver) : Driver where
  left := driver.right
  right := driver.left
  control := driver.control
  left_avoids := driver.right_avoids
  right_avoids := driver.left_avoids

private def exchangedTrajectory (driver : Driver) (state : Memory) : C(I, Point) where
  toFun t := exchangePoint (trajectory driver state t)
  continuous_toFun := ((trajectory driver state).continuous.fst.snd.prodMk
    (trajectory driver state).continuous.fst.fst).prodMk (trajectory driver state).continuous.snd

private theorem trajectory_exchange (driver : Driver) (state : Memory) :
    trajectory driver.exchange (exchange state) = exchangedTrajectory driver state := by
  apply coupled_curve_unique
  · intro t
    calc
      projection (trajectory driver.exchange (exchange state) t) = driver.exchange.path t :=
        trajectory_projects driver.exchange (exchange state) t
      _ = exchangeBase (driver.path t) := rfl
      _ = projection (exchangePoint (trajectory driver state t)) :=
        ((projection_exchange _).trans (congrArg exchangeBase (trajectory_projects driver state t))).symm
  · change trajectory driver.exchange (exchange state) 0 = exchangePoint (trajectory driver state 0)
    exact (trajectory_start driver.exchange (exchange state)).trans
      (congrArg exchangePoint (trajectory_start driver state).symm)

private theorem execute_exchange (driver : Driver) (state : Memory) :
    execute driver.exchange (exchange state) = exchange (execute driver state) := by
  apply Subtype.ext
  change trajectory driver.exchange (exchange state) 1 = exchangePoint (trajectory driver state 1)
  exact congrArg (fun curve : C(I, Point) => curve 1) (trajectory_exchange driver state)

def A_right : Driver := A_left.exchange

def B_right : Driver := B_left.exchange

theorem execute_A_right (left right control : ℤ) :
    execute A_right (prepare left right control) = prepare left (right + 1) control := by
  have result := execute_exchange A_left (prepare right left control)
  rw [exchange_prepare, execute_A_left, exchange_prepare] at result
  exact result

theorem execute_B_right (left right control : ℤ) :
    execute B_right (prepare left right control) = prepare left right (control + if right = 0 then 1 else 0) := by
  have result := execute_exchange B_left (prepare right left control)
  rw [exchange_prepare, execute_B_left, exchange_prepare] at result
  exact result

end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation

open unitInterval

/-- Driver composition concatenates the three fixed base paths. -/
def Driver.concat (first second : Driver) : Driver where
  left := first.left.trans second.left
  right := first.right.trans second.right
  control := first.control.trans second.control
  left_avoids := by
    intro t
    rw [Path.trans_apply]
    split_ifs
    · exact first.left_avoids _
    · exact second.left_avoids _
  right_avoids := by
    intro t
    rw [Path.trans_apply]
    split_ifs
    · exact first.right_avoids _
    · exact second.right_avoids _

def Driver.reverse (driver : Driver) : Driver where
  left := driver.left.symm
  right := driver.right.symm
  control := driver.control.symm
  left_avoids := fun t => driver.left_avoids (σ t)
  right_avoids := fun t => driver.right_avoids (σ t)

theorem Driver.concat_path (first second : Driver) :
    (first.concat second).path = first.path.trans second.path := by
  apply Path.ext
  funext t
  change (((first.left.trans second.left) t, (first.right.trans second.right) t),
    (first.control.trans second.control) t) = (first.path.trans second.path) t
  simp only [Path.trans_apply]
  split_ifs <;> rfl

theorem Driver.reverse_path (driver : Driver) : driver.reverse.path = driver.path.symm := rfl

theorem Driver.reverse_reverse (driver : Driver) : driver.reverse.reverse = driver := by
  cases driver
  simp [Driver.reverse]

/-- The path consists of the actual three-coordinate lift, rather than an endpoint interpolation. -/
def executionPath (driver : Driver) (state : Memory) : Path state.val (execute driver state).val where
  toFun := trajectory driver state
  continuous_toFun := (trajectory driver state).continuous
  source' := trajectory_start driver state
  target' := rfl

def sequentialPath (first second : Driver) (state : Memory) :
    Path state.val (execute second (execute first state)).val :=
  (executionPath first state).trans (executionPath second (execute first state))

theorem sequentialPath_projects (first second : Driver) (state : Memory) (t : I) :
    projection (sequentialPath first second state t) = (first.concat second).path t := by
  unfold sequentialPath
  rw [Driver.concat_path]
  simp only [Path.trans_apply]
  split_ifs
  · exact trajectory_projects first state _
  · exact trajectory_projects second (execute first state) _

/-- Concatenation composes actual coupled execution on the whole retained geometric state. -/
theorem execute_driver_trans (first second : Driver) (state : Memory) :
    execute (first.concat second) state = execute second (execute first state) := by
  apply Subtype.ext
  let joined := sequentialPath first second state
  have same : trajectory (first.concat second) state = joined.toContinuousMap :=
    coupled_curve_unique _ _
      (fun t => (trajectory_projects (first.concat second) state t).trans
        (sequentialPath_projects first second state t).symm)
      ((trajectory_start (first.concat second) state).trans joined.source.symm)
  exact (congrArg (fun curve : C(I, Point) => curve 1) same).trans joined.target

/-- The reverse driver reverses the actual coupled lifted path. -/
theorem execute_driver_reverse (driver : Driver) (state : Memory) :
    execute driver.reverse (execute driver state) = state := by
  apply Subtype.ext
  let backwards := (executionPath driver state).symm
  have projects : ∀ t, projection (backwards t) = driver.reverse.path t := by
    intro t
    exact trajectory_projects driver state (σ t)
  have same : trajectory driver.reverse (execute driver state) = backwards.toContinuousMap :=
    coupled_curve_unique _ _
      (fun t => (trajectory_projects driver.reverse (execute driver state) t).trans (projects t).symm)
      ((trajectory_start driver.reverse (execute driver state)).trans backwards.source.symm)
  exact (congrArg (fun curve : C(I, Point) => curve 1) same).trans backwards.target

theorem execute_after_driver_reverse (driver : Driver) (state : Memory) :
    execute driver (execute driver.reverse state) = state := by
  have reversed := execute_driver_reverse driver.reverse state
  simpa only [Driver.reverse_reverse] using reversed

end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation

/-- The upper cover is observed relative to the canonical lower logarithm charts. -/
def controlRoot (degree : ℕ) (state : Memory) : ℂ :=
  Complex.exp ((state.val.2 - Complex.log state.val.1.1.val -
    Complex.log state.val.1.2.val) / (degree : ℂ))

theorem controlRoot_pow (degree : ℕ) [NeZero degree] (state : Memory) :
    controlRoot degree state ^ degree = 1 := by
  have degree_ne : (degree : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne degree
  have normalized : Complex.exp (state.val.2 - Complex.log state.val.1.1.val -
      Complex.log state.val.1.2.val) = 1 := by
    rw [Complex.exp_sub, Complex.exp_sub,
      Complex.exp_log state.val.1.1.property, Complex.exp_log state.val.1.2.property,
      coherent]
    field_simp [state.val.1.1.property, state.val.1.2.property]
  unfold controlRoot
  rw [← Complex.exp_nat_mul]
  have cancel : (degree : ℂ) *
      ((state.val.2 - Complex.log state.val.1.1.val - Complex.log state.val.1.2.val) /
        (degree : ℂ)) = state.val.2 - Complex.log state.val.1.1.val - Complex.log state.val.1.2.val := by
    field_simp [degree_ne]
  rw [cancel, normalized]

theorem controlRoot_prepare (degree : ℕ) [NeZero degree] (left right control : ℤ) :
    controlRoot degree (prepare left right control) =
      (Radix.readRoot degree ((2 * Real.pi) * (control : ℝ)) : ℂ) := by
  change Complex.exp ((upperRoot left right control -
    Complex.log (NestedContinuation.firstRoot left) -
    Complex.log (NestedContinuation.firstRoot right)) / (degree : ℂ)) = _
  have residual : upperRoot left right control -
      Complex.log (NestedContinuation.firstRoot left) -
      Complex.log (NestedContinuation.firstRoot right) = NestedContinuation.period control := by
    unfold upperRoot
    ring
  rw [residual]
  simp only [Radix.readRoot, Circle.coe_exp]
  congr 1
  unfold NestedContinuation.period
  push_cast
  ring

/-- Reading returns an actual root in the finite power covering, without decoding an integer. -/
def readControl (degree : ℕ) [NeZero degree] (state : Memory) : Radix.Tower.Roots degree :=
  ⟨⟨controlRoot degree state, Complex.exp_ne_zero _⟩, by
    apply Subtype.ext
    exact controlRoot_pow degree state⟩

end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation

/-- Every root in the entire coupled fiber has exactly three branch labels. -/
theorem prepare_surjective : Function.Surjective
    (fun labels : (ℤ × ℤ) × ℤ => prepare labels.1.1 labels.1.2 labels.2) := by
  intro state
  obtain ⟨left, left_eq⟩ := Complex.exp_eq_exp_iff_exists_int.mp
    (congrArg Subtype.val (lowerLeft state).property)
  obtain ⟨right, right_eq⟩ := Complex.exp_eq_exp_iff_exists_int.mp
    (congrArg Subtype.val (lowerRight state).property)
  have left_value : state.val.1.1.val = NestedContinuation.firstRoot left := left_eq
  have right_value : state.val.1.2.val = NestedContinuation.firstRoot right := right_eq
  have upper_exp : Complex.exp state.val.2 =
      Complex.exp (Complex.log (NestedContinuation.firstRoot left) +
        Complex.log (NestedContinuation.firstRoot right)) := by
    rw [Complex.exp_add, Complex.exp_log (NestedContinuation.firstRoot_ne_zero left),
      Complex.exp_log (NestedContinuation.firstRoot_ne_zero right)]
    simpa only [left_value, right_value] using coherent state
  obtain ⟨control, control_eq⟩ := Complex.exp_eq_exp_iff_exists_int.mp upper_exp
  have upper_value : state.val.2 = upperRoot left right control := control_eq
  refine ⟨((left, right), control), ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · apply Prod.ext <;> apply Subtype.ext
    · exact left_value.symm
    · exact right_value.symm
  · exact upper_value.symm

theorem prepare_injective : Function.Injective
    (fun labels : (ℤ × ℤ) × ℤ => prepare labels.1.1 labels.1.2 labels.2) := by
  rintro ⟨⟨left, right⟩, control⟩ ⟨⟨left', right'⟩, control'⟩ same
  have left_eq : left = left' := NestedContinuation.firstRoot_injective
    (congrArg (fun state : Memory => state.val.1.1.val) same)
  have right_eq : right = right' := NestedContinuation.firstRoot_injective
    (congrArg (fun state : Memory => state.val.1.2.val) same)
  subst left'
  subst right'
  have upper_eq := congrArg (fun state : Memory => state.val.2) same
  change upperRoot left right control = upperRoot left right control' at upper_eq
  unfold upperRoot at upper_eq
  have control_eq := NestedContinuation.period_injective (add_left_cancel upper_eq)
  subst control'
  rfl

end Monodromy.CoupledContinuation


namespace Monodromy.CoupledPullback

abbrev Punctured := {value : ℂ // value ≠ 0}
abbrev Root := NestedRestricted.firstSet
abbrev Lower := (Root × Root) × Punctured
abbrev Point := (Root × Root) × ℂ

theorem root_ne_zero (root : Root) : root.val ≠ 0 :=
  NestedRestricted.firstSet_nonzero root.property

def exponential (value : ℂ) : Punctured := ⟨Complex.exp value, Complex.exp_ne_zero value⟩

def feed (point : Lower) : Punctured :=
  ⟨point.2.val * (point.1.1.val * point.1.2.val),
    mul_ne_zero point.2.property (mul_ne_zero (root_ne_zero point.1.1) (root_ne_zero point.1.2))⟩

theorem feed_continuous : Continuous feed := by unfold feed; fun_prop

def toPullback (point : Point) : CoverPullback.Space exponential feed :=
  ⟨((point.1, ⟨Complex.exp point.2 / (point.1.1.val * point.1.2.val),
      div_ne_zero (Complex.exp_ne_zero point.2)
        (mul_ne_zero (root_ne_zero point.1.1) (root_ne_zero point.1.2))⟩), point.2), by
    apply Subtype.ext
    exact (div_mul_cancel₀ (Complex.exp point.2)
      (mul_ne_zero (root_ne_zero point.1.1) (root_ne_zero point.1.2))).symm⟩

def fromPullback (point : CoverPullback.Space exponential feed) : Point :=
  (point.val.1.1, point.val.2)

def chart : Point ≃ₜ CoverPullback.Space exponential feed where
  toFun := toPullback
  invFun := fromPullback
  left_inv _ := rfl
  right_inv point := by
    apply Subtype.ext
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · apply Subtype.ext
        change Complex.exp point.val.2 /
          (point.val.1.1.1.val * point.val.1.1.2.val) = point.val.1.2.val
        have relation := congrArg Subtype.val point.property
        change Complex.exp point.val.2 =
          point.val.1.2.val * (point.val.1.1.1.val * point.val.1.1.2.val) at relation
        rw [relation]
        exact mul_div_cancel_right₀ _
          (mul_ne_zero (root_ne_zero point.val.1.1.1) (root_ne_zero point.val.1.1.2))
    · rfl
  continuous_toFun := by
    have denominator_nonzero : ∀ point : Point, point.1.1.val * point.1.2.val ≠ 0 :=
      fun point => mul_ne_zero (root_ne_zero point.1.1) (root_ne_zero point.1.2)
    unfold toPullback
    fun_prop (disch := aesop)
  continuous_invFun := by unfold fromPullback; fun_prop

/-- The coupled upper relation is a genuine exponential pullback covering. -/
def upperProjection (point : Point) : Lower :=
  (point.1, ⟨Complex.exp point.2 / (point.1.1.val * point.1.2.val),
    div_ne_zero (Complex.exp_ne_zero point.2)
      (mul_ne_zero (root_ne_zero point.1.1) (root_ne_zero point.1.2))⟩)

theorem upperCovering : IsCoveringMap upperProjection :=
  (CoverPullback.covering (p := exponential) Complex.isCoveringMap_exp feed_continuous).comp_homeomorph chart

end Monodromy.CoupledPullback


namespace Monodromy.CoupledPullback

abbrev Base := (NestedRestricted.baseSet × NestedRestricted.baseSet) × Punctured

def lowerProjection : Lower → Base :=
  Prod.map (Prod.map NestedRestricted.firstProjection NestedRestricted.firstProjection) id

/-- The two lower exponential restrictions and the unchanged control coordinate form a cover. -/
theorem lowerCovering : IsCoveringMap lowerProjection :=
  CoverPullback.prodMap
    (CoverPullback.prodMap NestedRestricted.firstCovering NestedRestricted.firstCovering)
    CoverPullback.identity

def values (point : Base) : (ℂ × ℂ) × ℂ := ((point.1.1.val, point.1.2.val), point.2.val)

/-- The two matching covering levels give exactly the coupled coordinate expression. -/
theorem composite_formula (point : Point) :
    values (lowerProjection (upperProjection point)) =
      ((Complex.exp point.1.1.val, Complex.exp point.1.2.val),
        Complex.exp point.2 / (point.1.1.val * point.1.2.val)) := rfl

end Monodromy.CoupledPullback

namespace Monodromy.CoupledContinuation

/-- Reversing a fixed memory loop decrements its branch without a decoded target. -/
theorem execute_A_left_reverse (left right control : ℤ) :
    execute A_left.reverse (prepare left right control) = prepare (left - 1) right control := by
  have result := execute_driver_reverse A_left (prepare (left - 1) right control)
  rw [execute_A_left] at result
  simpa only [sub_add_cancel] using result

theorem execute_A_right_reverse (left right control : ℤ) :
    execute A_right.reverse (prepare left right control) = prepare left (right - 1) control := by
  have result := execute_driver_reverse A_right (prepare left (right - 1) control)
  rw [execute_A_right] at result
  simpa only [sub_add_cancel] using result

theorem execute_control_reverse (left right control : ℤ) :
    execute controlTurn.reverse (prepare left right control) = prepare left right (control - 1) := by
  have result := execute_driver_reverse controlTurn (prepare left right (control - 1))
  rw [execute_control_prepare] at result
  simpa only [sub_add_cancel] using result

/-- Conditional transport retains both actual lower roots throughout the return. -/
theorem execute_B_left_memories (state : Memory) :
    (execute B_left state).val.1 = state.val.1 := by
  obtain ⟨⟨⟨left, right⟩, control⟩, rfl⟩ := prepare_surjective state
  rw [execute_B_left]
  rfl

/-- The geometric zero condition can be stated on the retained root itself. -/
theorem execute_B_left_zero (state : Memory) (zero : state.val.1.1.val = 1) :
    (execute B_left state).val.2 = state.val.2 + NestedContinuation.period 1 := by
  obtain ⟨⟨⟨left, right⟩, control⟩, rfl⟩ := prepare_surjective state
  have left_zero : left = 0 := NestedContinuation.firstRoot_injective (by
    simpa only [prepare, NestedContinuation.firstRoot, NestedContinuation.period,
      Int.cast_zero, zero_mul, add_zero] using zero)
  subst left
  rw [execute_B_left]
  change upperRoot 0 right (control + if (0 : ℤ) = 0 then 1 else 0) =
    upperRoot 0 right control + NestedContinuation.period 1
  simp only [ite_true]
  simp only [upperRoot, NestedContinuation.period, Int.cast_add, Int.cast_one]
  ring

/-- Every other actual branch is fixed by the same prescribed base loop. -/
theorem execute_B_left_nonzero (state : Memory) (nonzero : state.val.1.1.val ≠ 1) :
    execute B_left state = state := by
  obtain ⟨⟨⟨left, right⟩, control⟩, rfl⟩ := prepare_surjective state
  have left_ne : left ≠ 0 := by
    intro zero
    subst left
    apply nonzero
    simp [prepare, NestedContinuation.firstRoot, NestedContinuation.period]
  simpa only [ite_eq_right left_ne, add_zero] using execute_B_left left right control

/-- This finite word reads each zero branch by the same geometric mechanism. -/
def exampleDriver : Driver :=
  (((A_left.concat B_left).concat B_right).concat A_right.reverse).concat B_right

theorem example_run :
    execute exampleDriver (prepare (-1) 1 0) = prepare 0 0 2 := by
  simp only [exampleDriver, execute_driver_trans]
  rw [execute_A_left, execute_B_left, execute_B_right, execute_A_right_reverse,
    execute_B_right]
  norm_num

theorem example_reverse :
    execute exampleDriver.reverse (prepare 0 0 2) = prepare (-1) 1 0 := by
  rw [← example_run]
  exact execute_driver_reverse exampleDriver _

end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation

/-- Every return lies in the canonical logarithm charts of the two lower roots. -/
theorem lower_roots_slit (state : Memory) :
    state.val.1.1.val ∈ Complex.slitPlane ∧ state.val.1.2.val ∈ Complex.slitPlane := by
  obtain ⟨⟨⟨left, right⟩, control⟩, rfl⟩ := prepare_surjective state
  exact ⟨NestedContinuation.firstRoot_slit left, NestedContinuation.firstRoot_slit right⟩

attribute [local fun_prop] analyticAt_fst analyticAt_snd

/-- The finite-root observation has a complex analytic extension near every return. -/
theorem analyticAt_control_observation (degree : ℕ) (state : Memory) :
    AnalyticAt ℂ (fun point : (ℂ × ℂ) × ℂ =>
      Complex.exp ((point.2 - Complex.log point.1.1 - Complex.log point.1.2) / (degree : ℂ)))
      ((state.val.1.1.val, state.val.1.2.val), state.val.2) := by
  let point : (ℂ × ℂ) × ℂ := ((state.val.1.1.val, state.val.1.2.val), state.val.2)
  have left : AnalyticAt ℂ (fun value : (ℂ × ℂ) × ℂ => value.1.1) point := by fun_prop
  have right : AnalyticAt ℂ (fun value : (ℂ × ℂ) × ℂ => value.1.2) point := by fun_prop
  have top : AnalyticAt ℂ (fun value : (ℂ × ℂ) × ℂ => value.2) point := by fun_prop
  have exponent : AnalyticAt ℂ (fun value : (ℂ × ℂ) × ℂ =>
      (value.2 - Complex.log value.1.1 - Complex.log value.1.2) / (degree : ℂ)) point :=
    ((top.sub (left.clog (lower_roots_slit state).1)).sub
      (right.clog (lower_roots_slit state).2)).div_const
  exact exponent.cexp'

end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation

open unitInterval

variable (degree : ℕ) [NeZero degree]

/-- Every native return has a finite root observation; the witness is used only in proofs. -/
theorem controlRoot_is_root (state : Memory) :
    ∃ index : Fin degree, controlRoot degree state = (Radix.omega degree index : ℂ) := by
  obtain ⟨⟨⟨left, right⟩, control⟩, rfl⟩ := prepare_surjective state
  let index : Fin degree := ⟨(control % (degree : ℤ)).toNat, by
    have positive : 0 < (degree : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne degree)
    have lower := Int.emod_nonneg control positive.ne'
    have upper := Int.emod_lt_of_pos control positive
    omega⟩
  have cast : (index.val : ℤ) = control % (degree : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg control (by exact_mod_cast NeZero.ne degree))
  have decomposition : (degree : ℤ) * (control / (degree : ℤ)) + index.val = control := by
    rw [cast]
    exact Int.mul_ediv_add_emod control (degree : ℤ)
  have read := Radix.readRoot_digit degree (control / (degree : ℤ)) index
  rw [decomposition] at read
  exact ⟨index, (controlRoot_prepare degree left right control).trans
    (congrArg (fun value : Circle => (value : ℂ)) read)⟩

/-- Fixed normalized power-cover kernels route an entire base path, not its endpoint. -/
def routeValue {basepoint : Punctured} (paths : Fin degree → Path basepoint basepoint)
    (state : Memory) (t : I) : ℂ :=
  Choice.dispatch (fun value : ℂ => value ^ degree)
    (fun index => (Radix.omega degree index : ℂ))
    (fun index => (paths index t).val) (controlRoot degree state)

theorem routeValue_eq {basepoint : Punctured} (paths : Fin degree → Path basepoint basepoint)
    (state : Memory) (index : Fin degree)
    (observed : controlRoot degree state = (Radix.omega degree index : ℂ)) (t : I) :
    routeValue degree paths state t = (paths index t).val := by
  unfold routeValue
  rw [observed]
  exact Choice.dispatch_root
    (fun first second same => Radix.omega_injective degree (Subtype.ext same))
    (fun first second => (Radix.omega_complex_pow degree first).trans
      (Radix.omega_complex_pow degree second).symm)
    (Radix.omega_regular degree) index

omit [NeZero degree] in
theorem continuous_routeValue {basepoint : Punctured} (paths : Fin degree → Path basepoint basepoint)
    (state : Memory) : Continuous (routeValue degree paths state) := by
  unfold routeValue Choice.dispatch
  exact continuous_finsetSum Finset.univ (fun index _ =>
    continuous_const.mul (continuous_subtype_val.comp (paths index).continuous))

theorem routeValue_ne_zero {basepoint : Punctured} (paths : Fin degree → Path basepoint basepoint)
    (state : Memory) (t : I) : routeValue degree paths state t ≠ 0 := by
  obtain ⟨index, observed⟩ := controlRoot_is_root degree state
  rw [routeValue_eq degree paths state index observed t]
  exact (paths index t).property

/-- The runtime base path is the finite analytic kernel sum over prescribed paths. -/
def routePath {basepoint : Punctured} (paths : Fin degree → Path basepoint basepoint)
    (state : Memory) : Path basepoint basepoint where
  toFun t := ⟨routeValue degree paths state t, routeValue_ne_zero degree paths state t⟩
  continuous_toFun := (continuous_routeValue degree paths state).subtype_mk _
  source' := by
    obtain ⟨index, observed⟩ := controlRoot_is_root degree state
    apply Subtype.ext
    exact (routeValue_eq degree paths state index observed 0).trans
      (congrArg Subtype.val (paths index).source)
  target' := by
    obtain ⟨index, observed⟩ := controlRoot_is_root degree state
    apply Subtype.ext
    exact (routeValue_eq degree paths state index observed 1).trans
      (congrArg Subtype.val (paths index).target)

theorem routePath_eq {basepoint : Punctured} (paths : Fin degree → Path basepoint basepoint)
    (state : Memory) (index : Fin degree)
    (observed : controlRoot degree state = (Radix.omega degree index : ℂ)) :
    routePath degree paths state = paths index := by
  apply Path.ext
  funext t
  apply Subtype.ext
  exact routeValue_eq degree paths state index observed t

/-- One fixed finite table supplies all three coordinate paths; state supplies only its root. -/
def routeDriver (table : Fin degree → Driver) (state : Memory) : Driver where
  left := routePath degree (fun index => (table index).left) state
  right := routePath degree (fun index => (table index).right) state
  control := routePath degree (fun index => (table index).control) state
  left_avoids := by
    intro t
    obtain ⟨index, observed⟩ := controlRoot_is_root degree state
    rw [routePath_eq degree (fun index => (table index).left) state index observed]
    exact (table index).left_avoids t
  right_avoids := by
    intro t
    obtain ⟨index, observed⟩ := controlRoot_is_root degree state
    rw [routePath_eq degree (fun index => (table index).right) state index observed]
    exact (table index).right_avoids t

private theorem Driver.eq_of_paths (first second : Driver)
    (left : first.left = second.left) (right : first.right = second.right)
    (control : first.control = second.control) : first = second := by
  cases first
  cases second
  cases left
  cases right
  cases control
  rfl

theorem routeDriver_eq (table : Fin degree → Driver) (state : Memory) (index : Fin degree)
    (observed : controlRoot degree state = (Radix.omega degree index : ℂ)) :
    routeDriver degree table state = table index := by
  apply Driver.eq_of_paths
  · exact routePath_eq degree (fun index => (table index).left) state index observed
  · exact routePath_eq degree (fun index => (table index).right) state index observed
  · exact routePath_eq degree (fun index => (table index).control) state index observed

/-- Actual continuation executes the internally routed finite table. -/
def executeRouted (table : Fin degree → Driver) (state : Memory) : Memory :=
  execute (routeDriver degree table state) state

theorem executeRouted_eq (table : Fin degree → Driver) (state : Memory) (index : Fin degree)
    (observed : controlRoot degree state = (Radix.omega degree index : ℂ)) :
    executeRouted degree table state = execute (table index) state := by
  unfold executeRouted
  rw [routeDriver_eq degree table state index observed]

/-- Arbitrary integer controls are routed by their finite residue, without decoding it at runtime. -/
theorem executeRouted_prepare (table : Fin degree → Driver) (left right quotient : ℤ)
    (index : Fin degree) :
    executeRouted degree table (prepare left right ((degree : ℤ) * quotient + index.val)) =
      execute (table index) (prepare left right ((degree : ℤ) * quotient + index.val)) := by
  apply executeRouted_eq
  rw [controlRoot_prepare]
  exact congrArg (fun value : Circle => (value : ℂ)) (Radix.readRoot_digit degree quotient index)

end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation

open unitInterval

/-- The fixed base point belongs to the twice-punctured base of each lower cover. -/
def restrictedBaseRoot : NestedRestricted.baseSet :=
  ⟨NestedContinuation.base.val, NestedContinuation.base.property, by
    intro equal
    exact base_ne_one (Subtype.ext equal)⟩

def restrictedBase : CoupledPullback.Base := ((restrictedBaseRoot, restrictedBaseRoot), one)

def Driver.restrictedPath (driver : Driver) : Path restrictedBase restrictedBase :=
  ((NestedRestricted.basePath driver.left (fun t equal => driver.left_avoids t (Subtype.ext equal))).prod
    (NestedRestricted.basePath driver.right (fun t equal => driver.right_avoids t (Subtype.ext equal)))).prod
      driver.control

/-- Restriction changes the geometric domain, preserving all base coordinates. -/
def forgetBase (point : CoupledPullback.Base) : Base :=
  ((⟨point.1.1.val, point.1.1.property.1⟩, ⟨point.1.2.val, point.1.2.property.1⟩), point.2)

theorem restrictedPath_forget (driver : Driver) :
    forgetBase ∘ driver.restrictedPath = driver.path := rfl

theorem lower_mem (path : Path NestedContinuation.base NestedContinuation.base)
    (avoids : ∀ t, path t ≠ one)
    (root : Transport.Fiber NestedContinuation.expCover NestedContinuation.base) (t : I) :
    lower path root t ∈ NestedRestricted.firstSet := by
  change Complex.exp (lower path root t) ≠ 0 ∧ Complex.exp (lower path root t) ≠ 1
  refine ⟨Complex.exp_ne_zero _, ?_⟩
  intro equal
  apply avoids t
  apply Subtype.ext
  exact (congrArg Subtype.val (congrFun (lower_projects path root) t)).symm.trans equal

theorem lower_state_mem (root : Transport.Fiber NestedContinuation.expCover NestedContinuation.base) :
    root.val ∈ NestedRestricted.firstSet := by
  change Complex.exp root.val ≠ 0 ∧ Complex.exp root.val ≠ 1
  refine ⟨Complex.exp_ne_zero _, ?_⟩
  intro equal
  apply base_ne_one
  apply Subtype.ext
  exact (congrArg Subtype.val root.property).symm.trans equal

/-- The same retained root triple, carrying only proofs of its covering domains. -/
def restrictedState (state : Memory) : CoupledPullback.Point :=
  ((⟨state.val.1.1.val, lower_state_mem (lowerLeft state)⟩,
    ⟨state.val.1.2.val, lower_state_mem (lowerRight state)⟩), state.val.2)

def forgetPoint (point : CoupledPullback.Point) : Point :=
  ((⟨point.1.1.val, CoupledPullback.root_ne_zero point.1.1⟩,
    ⟨point.1.2.val, CoupledPullback.root_ne_zero point.1.2⟩), point.2)

theorem restrictedState_forget (state : Memory) : forgetPoint (restrictedState state) = state.val := rfl

/-- The actual lower lifts and fixed third base coordinate form the intermediate curve. -/
def intermediateCurve (driver : Driver) (state : Memory) : C(I, CoupledPullback.Lower) where
  toFun t := ((⟨lower driver.left (lowerLeft state) t,
      lower_mem driver.left driver.left_avoids (lowerLeft state) t⟩,
    ⟨lower driver.right (lowerRight state) t,
      lower_mem driver.right driver.right_avoids (lowerRight state) t⟩), driver.control t)
  continuous_toFun := (((lower driver.left (lowerLeft state)).continuous.subtype_mk _).prodMk
    ((lower driver.right (lowerRight state)).continuous.subtype_mk _)).prodMk driver.control.continuous

/-- No curve is prescribed: this wraps the already constructed actual upper lift. -/
def restrictedTrajectory (driver : Driver) (state : Memory) : C(I, CoupledPullback.Point) where
  toFun t := ((⟨lower driver.left (lowerLeft state) t,
      lower_mem driver.left driver.left_avoids (lowerLeft state) t⟩,
    ⟨lower driver.right (lowerRight state) t,
      lower_mem driver.right driver.right_avoids (lowerRight state) t⟩), upper driver state t)
  continuous_toFun := (((lower driver.left (lowerLeft state)).continuous.subtype_mk _).prodMk
    ((lower driver.right (lowerRight state)).continuous.subtype_mk _)).prodMk
      (upper driver state).continuous

theorem restrictedTrajectory_forget (driver : Driver) (state : Memory) :
    forgetPoint ∘ restrictedTrajectory driver state = trajectory driver state := rfl

theorem restrictedTrajectory_start (driver : Driver) (state : Memory) :
    restrictedTrajectory driver state 0 = restrictedState state := by
  apply Prod.ext
  · apply Prod.ext <;> apply Subtype.ext
    · exact lower_start driver.left (lowerLeft state)
    · exact lower_start driver.right (lowerRight state)
  · exact upper_start driver state

theorem restrictedTrajectory_end (driver : Driver) (state : Memory) :
    restrictedTrajectory driver state 1 = restrictedState (execute driver state) := rfl

/-- The first geometric arrow projects the actual lifted upper trajectory. -/
theorem restricted_upper_projection (driver : Driver) (state : Memory) (t : I) :
    CoupledPullback.upperProjection (restrictedTrajectory driver state t) = intermediateCurve driver state t := by
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    change Complex.exp (upper driver state t) /
      (lower driver.left (lowerLeft state) t * lower driver.right (lowerRight state) t) =
      (driver.control t).val
    rw [upper_projects]
    exact mul_div_cancel_right₀ _
      (mul_ne_zero (lower_ne_zero driver.left driver.left_avoids (lowerLeft state) t)
        (lower_ne_zero driver.right driver.right_avoids (lowerRight state) t))

/-- The second geometric arrow projects the actual intermediate curve to the fixed driver. -/
theorem restricted_lower_projection (driver : Driver) (state : Memory) (t : I) :
    CoupledPullback.lowerProjection (intermediateCurve driver state t) = driver.restrictedPath t := by
  apply Prod.ext
  · apply Prod.ext <;> apply Subtype.ext
    · exact congrArg (fun value : Punctured => (value : ℂ))
        (congrFun (lower_projects driver.left (lowerLeft state)) t)
    · exact congrArg (fun value : Punctured => (value : ℂ))
        (congrFun (lower_projects driver.right (lowerRight state)) t)
  · rfl

theorem restrictedState_over_base (state : Memory) :
    CoupledPullback.lowerProjection (CoupledPullback.upperProjection (restrictedState state)) = restrictedBase := by
  let driver : Driver := controlTurn
  have first := congrArg CoupledPullback.lowerProjection (restricted_upper_projection driver state 0)
  rw [restrictedTrajectory_start] at first
  exact first.trans ((restricted_lower_projection driver state 0).trans driver.restrictedPath.source)

/-- Both covering projections commute throughout the complete runtime trajectory. -/
theorem restricted_runtime_diagram (driver : Driver) (state : Memory) (t : I) :
    CoupledPullback.upperProjection (restrictedTrajectory driver state t) = intermediateCurve driver state t ∧
      CoupledPullback.lowerProjection (intermediateCurve driver state t) = driver.restrictedPath t :=
  ⟨restricted_upper_projection driver state t, restricted_lower_projection driver state t⟩


/-- The intermediate path is the actual generated curve, with its actual endpoints. -/
def intermediatePath (driver : Driver) (state : Memory) :
    Path (CoupledPullback.upperProjection (restrictedState state)) (intermediateCurve driver state 1) where
  toFun := intermediateCurve driver state
  continuous_toFun := (intermediateCurve driver state).continuous
  source' := by
    have first := restricted_upper_projection driver state 0
    rw [restrictedTrajectory_start] at first
    exact first.symm
  target' := rfl

/-- The runtime intermediate curve is the unique actual lift for the matching lower cover. -/
theorem intermediateCurve_actual_lift (driver : Driver) (state : Memory) :
    intermediateCurve driver state =
      CoupledPullback.lowerCovering.liftPath driver.restrictedPath
        (CoupledPullback.upperProjection (restrictedState state))
        (driver.restrictedPath.source.trans (restrictedState_over_base state).symm) := by
  apply (CoupledPullback.lowerCovering.eq_liftPath_iff'
    (driver.restrictedPath.source.trans (restrictedState_over_base state).symm)).mpr
  constructor
  · funext t
    exact restricted_lower_projection driver state t
  · have first := restricted_upper_projection driver state 0
    rw [restrictedTrajectory_start] at first
    exact first.symm

/-- The runtime upper trajectory is the unique actual lift for the matching upper cover. -/
theorem restrictedTrajectory_actual_lift (driver : Driver) (state : Memory) :
    restrictedTrajectory driver state =
      CoupledPullback.upperCovering.liftPath (intermediatePath driver state) (restrictedState state)
        (intermediatePath driver state).source := by
  apply (CoupledPullback.upperCovering.eq_liftPath_iff'
    (intermediatePath driver state).source).mpr
  constructor
  · funext t
    exact restricted_upper_projection driver state t
  · exact restrictedTrajectory_start driver state

end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation

open unitInterval

theorem projection_period_shift (amount : ℤ) (point : Point) :
    projection (point.1, point.2 + NestedContinuation.period amount) = projection point := by
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    change Complex.exp (point.2 + NestedContinuation.period amount) /
      (point.1.1.val * point.1.2.val) = Complex.exp point.2 / (point.1.1.val * point.1.2.val)
    rw [Complex.exp_add, NestedContinuation.exp_period, mul_one]

/-- The intrinsic upper deck action; `controlDeck_eq_control_word` gives its existing executable word. -/
def controlDeck (amount : ℤ) (state : Memory) : Memory :=
  ⟨(state.val.1, state.val.2 + NestedContinuation.period amount),
    (projection_period_shift amount state.val).trans state.property⟩

theorem controlDeck_values (amount : ℤ) (state : Memory) :
    (controlDeck amount state).val = (state.val.1, state.val.2 + NestedContinuation.period amount) := rfl

theorem controlDeck_prepare (amount left right control : ℤ) :
    controlDeck amount (prepare left right control) = prepare left right (control + amount) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change upperRoot left right control + NestedContinuation.period amount =
      upperRoot left right (control + amount)
    simp [upperRoot, NestedContinuation.period]
    ring

/-- Lift uniqueness makes every fixed driver equivariant under the upper deck action. -/
theorem execute_controlDeck (driver : Driver) (amount : ℤ) (state : Memory) :
    execute driver (controlDeck amount state) = controlDeck amount (execute driver state) := by
  let shifted : C(I, Point) :=
    ⟨fun time => ((trajectory driver state time).1,
      (trajectory driver state time).2 + NestedContinuation.period amount),
      (trajectory driver state).continuous.fst.prodMk
        ((trajectory driver state).continuous.snd.add continuous_const)⟩
  have projects : ∀ time, projection (shifted time) = driver.path time := by
    intro time
    exact (projection_period_shift amount (trajectory driver state time)).trans
      (trajectory_projects driver state time)
  have starts : trajectory driver (controlDeck amount state) 0 = shifted 0 := by
    change trajectory driver (controlDeck amount state) 0 =
      ((trajectory driver state 0).1, (trajectory driver state 0).2 + NestedContinuation.period amount)
    rw [trajectory_start, trajectory_start, controlDeck_values]
  have same : trajectory driver (controlDeck amount state) = shifted :=
    coupled_curve_unique _ _
      (fun time => (trajectory_projects driver (controlDeck amount state) time).trans (projects time).symm)
      starts
  apply Subtype.ext
  rw [controlDeck_values]
  exact congrArg (fun curve : C(I, Point) => curve 1) same

/-- A deck shift multiplies every return observation by the same finite-cover phase. -/
theorem controlRoot_controlDeck (degree : ℕ) (amount : ℤ) (state : Memory) :
    controlRoot degree (controlDeck amount state) =
      Complex.exp (NestedContinuation.period amount / (degree : ℂ)) * controlRoot degree state := by
  unfold controlRoot
  rw [controlDeck_values]
  rw [← Complex.exp_add]
  congr 1
  ring

section FiniteRouting

variable (degree : ℕ) [NeZero degree]

private theorem root_prepare (index : Fin degree) (left right : ℤ) :
    controlRoot degree (prepare left right index.val) = (Radix.omega degree index : ℂ) := by
  rw [controlRoot_prepare]
  have root := congrArg (fun value : Circle => (value : ℂ)) (Radix.readRoot_digit degree 0 index)
  simpa only [mul_zero, zero_add] using root

/-- Every selected path has a fixed target observation on its own source cell. -/
def SendsRootCells (table : Fin degree → Driver) (next : Fin degree → Fin degree) : Prop :=
  ∀ index state, controlRoot degree state = (Radix.omega degree index : ℂ) →
    controlRoot degree (execute (table index) state) = (Radix.omega degree (next index) : ℂ)

/-- Exact cell matching includes the preimage condition needed to reverse a routed path. -/
def MatchesRootCells (table : Fin degree → Driver) (next : Fin degree → Fin degree) : Prop :=
  ∀ index state,
    controlRoot degree (execute (table index) state) = (Radix.omega degree (next index) : ℂ) ↔
      controlRoot degree state = (Radix.omega degree index : ℂ)

/-- For these actual lifts, one-sided cell transport is exact by deck equivariance. -/
theorem matchesRootCells_of_sends (table : Fin degree → Driver) (next : Fin degree → Fin degree)
    (sends : SendsRootCells degree table next) : MatchesRootCells degree table next := by
  intro index state
  constructor
  · intro target
    obtain ⟨⟨⟨left, right⟩, control⟩, rfl⟩ := prepare_surjective state
    change controlRoot degree (execute (table index) (prepare left right control)) =
      (Radix.omega degree (next index) : ℂ) at target
    change controlRoot degree (prepare left right control) = (Radix.omega degree index : ℂ)
    let initial := prepare left right (index.val : ℤ)
    let amount : ℤ := control - index.val
    have initial_root : controlRoot degree initial = (Radix.omega degree index : ℂ) :=
      root_prepare degree index left right
    have initial_target := sends index initial initial_root
    have shifted : controlDeck amount initial = prepare left right control := by
      rw [controlDeck_prepare]
      congr 1
      dsimp [amount]
      omega
    have output_phase :
        controlRoot degree (execute (table index) (prepare left right control)) =
          Complex.exp (NestedContinuation.period amount / (degree : ℂ)) *
            controlRoot degree (execute (table index) initial) := by
      rw [← shifted, execute_controlDeck, controlRoot_controlDeck]
    have balance := output_phase.symm.trans target
    rw [initial_target] at balance
    have phase_one : Complex.exp (NestedContinuation.period amount / (degree : ℂ)) = 1 := by
      apply mul_right_cancel₀ (Radix.omega degree (next index)).coe_ne_zero
      simpa only [one_mul] using balance
    rw [← shifted, controlRoot_controlDeck, phase_one, one_mul]
    exact initial_root
  · exact sends index state

/-- Inversion uses the same paths in reverse, indexed by the inverse finite permutation. -/
def reindexedReverse (table : Fin degree → Driver) (permutation : Equiv.Perm (Fin degree)) :
    Fin degree → Driver := fun index => (table (permutation.symm index)).reverse

theorem permuted_routed_left_inverse (table : Fin degree → Driver)
    (permutation : Equiv.Perm (Fin degree))
    (cells : MatchesRootCells degree table permutation) :
    Function.LeftInverse (executeRouted degree (reindexedReverse degree table permutation))
      (executeRouted degree table) := by
  intro state
  obtain ⟨index, observed⟩ := controlRoot_is_root degree state
  have moved := (cells index state).mpr observed
  rw [executeRouted_eq degree table state index observed]
  rw [executeRouted_eq degree (reindexedReverse degree table permutation)
    (execute (table index) state) (permutation index) moved]
  simpa only [reindexedReverse, permutation.symm_apply_apply] using execute_driver_reverse (table index) state

theorem permuted_routed_right_inverse (table : Fin degree → Driver)
    (permutation : Equiv.Perm (Fin degree))
    (cells : MatchesRootCells degree table permutation) :
    Function.RightInverse (executeRouted degree (reindexedReverse degree table permutation))
      (executeRouted degree table) := by
  intro state
  obtain ⟨index, observed⟩ := controlRoot_is_root degree state
  have reversed : controlRoot degree (execute (table (permutation.symm index)).reverse state) =
      (Radix.omega degree (permutation.symm index) : ℂ) := by
    apply (cells (permutation.symm index) _).mp
    rw [execute_after_driver_reverse, permutation.apply_symm_apply]
    exact observed
  rw [executeRouted_eq degree (reindexedReverse degree table permutation) state index observed]
  change executeRouted degree table (execute (table (permutation.symm index)).reverse state) = state
  rw [executeRouted_eq degree table _ (permutation.symm index) reversed]
  exact execute_after_driver_reverse (table (permutation.symm index)) state

/-- A root-permuting table is globally reversible by the existing routed execution kernel. -/
def permutedRoutedEquiv (table : Fin degree → Driver) (permutation : Equiv.Perm (Fin degree))
    (sends : SendsRootCells degree table permutation) : Memory ≃ Memory where
  toFun := executeRouted degree table
  invFun := executeRouted degree (reindexedReverse degree table permutation)
  left_inv := permuted_routed_left_inverse degree table permutation
    (matchesRootCells_of_sends degree table permutation sends)
  right_inv := permuted_routed_right_inverse degree table permutation
    (matchesRootCells_of_sends degree table permutation sends)

theorem permutedRoutedEquiv_apply (table : Fin degree → Driver) (permutation : Equiv.Perm (Fin degree))
    (sends : SendsRootCells degree table permutation) (state : Memory) :
    permutedRoutedEquiv degree table permutation sends state = executeRouted degree table state := rfl

theorem permutedRoutedEquiv_inverse (table : Fin degree → Driver) (permutation : Equiv.Perm (Fin degree))
    (sends : SendsRootCells degree table permutation) (state : Memory) :
    (permutedRoutedEquiv degree table permutation sends).symm state =
      executeRouted degree (reindexedReverse degree table permutation) state := rfl

/-- A closed finite observation evolves by its specified transition on roots. -/
theorem routed_root (table : Fin degree → Driver) (next : Fin degree → Fin degree)
    (sends : SendsRootCells degree table next) (state : Memory) (index : Fin degree)
    (observed : controlRoot degree state = (Radix.omega degree index : ℂ)) :
    controlRoot degree (executeRouted degree table state) = (Radix.omega degree (next index) : ℂ) := by
  rw [executeRouted_eq degree table state index observed]
  exact sends index state observed

theorem finite_surjective_of_routed_surjective (table : Fin degree → Driver)
    (next : Fin degree → Fin degree) (sends : SendsRootCells degree table next)
    (onto : Function.Surjective (executeRouted degree table)) : Function.Surjective next := by
  intro target
  obtain ⟨state, reaches⟩ := onto (prepare 0 0 target.val)
  obtain ⟨index, observed⟩ := controlRoot_is_root degree state
  have roots := routed_root degree table next sends state index observed
  rw [reaches, root_prepare] at roots
  exact ⟨index, Radix.omega_injective degree (Subtype.ext roots.symm)⟩

/-- Within root-closed routing, global reversibility is exactly finite-root permutation. -/
theorem routed_bijective_iff (table : Fin degree → Driver) (next : Fin degree → Fin degree)
    (sends : SendsRootCells degree table next) :
    Function.Bijective (executeRouted degree table) ↔ Function.Bijective next := by
  constructor
  · intro reversible
    exact Finite.surjective_iff_bijective.mp
      (finite_surjective_of_routed_surjective degree table next sends reversible.surjective)
  · intro finite_reversible
    exact (permutedRoutedEquiv degree table (Equiv.ofBijective next finite_reversible) sends).bijective

end FiniteRouting

/-- Reversing an actual gate preserves every observation preserved by its forward execution. -/
theorem controlRoot_reverse (degree : ℕ) (driver : Driver)
    (preserves : ∀ state, controlRoot degree (execute driver state) = controlRoot degree state)
    (state : Memory) :
    controlRoot degree (execute driver.reverse state) = controlRoot degree state := by
  have forward := preserves (execute driver.reverse state)
  rw [execute_after_driver_reverse] at forward
  exact forward.symm

def reverseTable (degree : ℕ) (table : Fin degree → Driver) : Fin degree → Driver :=
  reindexedReverse degree table (Equiv.refl _)

/-- Identity root routing is the identity-permutation instance of reversible routing. -/
theorem routed_left_inverse (degree : ℕ) [NeZero degree] (table : Fin degree → Driver)
    (preserves : ∀ index state, controlRoot degree (execute (table index) state) = controlRoot degree state) :
    Function.LeftInverse (executeRouted degree (reverseTable degree table)) (executeRouted degree table) :=
  permuted_routed_left_inverse degree table (Equiv.refl _)
    (matchesRootCells_of_sends degree table (Equiv.refl _)
      (fun index state observed => (preserves index state).trans observed))

theorem routed_right_inverse (degree : ℕ) [NeZero degree] (table : Fin degree → Driver)
    (preserves : ∀ index state, controlRoot degree (execute (table index) state) = controlRoot degree state) :
    Function.RightInverse (executeRouted degree (reverseTable degree table)) (executeRouted degree table) :=
  permuted_routed_right_inverse degree table (Equiv.refl _)
    (matchesRootCells_of_sends degree table (Equiv.refl _)
      (fun index state observed => (preserves index state).trans observed))

def routedEquiv (degree : ℕ) [NeZero degree] (table : Fin degree → Driver)
    (preserves : ∀ index state, controlRoot degree (execute (table index) state) = controlRoot degree state) :
    Memory ≃ Memory :=
  permutedRoutedEquiv degree table (Equiv.refl _)
    (fun index state observed => (preserves index state).trans observed)

/-- Root-preserving routing is exactly the identity-permutation instance. -/
theorem permutedRoutedEquiv_refl (degree : ℕ) [NeZero degree] (table : Fin degree → Driver)
    (preserves : ∀ index state, controlRoot degree (execute (table index) state) = controlRoot degree state) :
    permutedRoutedEquiv degree table (Equiv.refl _)
      (fun index state observed => (preserves index state).trans observed) = routedEquiv degree table preserves := by
  apply Equiv.ext
  intro state
  rfl

def Driver.executionEquiv (driver : Driver) : Memory ≃ Memory where
  toFun := execute driver
  invFun := execute driver.reverse
  left_inv := execute_driver_reverse driver
  right_inv := execute_after_driver_reverse driver

/-- A reversible routed return followed by any fixed actual gate closes the feedback cycle. -/
def feedbackEquiv (degree : ℕ) [NeZero degree] (table : Fin degree → Driver)
    (preserves : ∀ index state, controlRoot degree (execute (table index) state) = controlRoot degree state)
    (gate : Driver) : Memory ≃ Memory :=
  (routedEquiv degree table preserves).trans gate.executionEquiv

theorem feedbackEquiv_apply (degree : ℕ) [NeZero degree] (table : Fin degree → Driver)
    (preserves : ∀ index state, controlRoot degree (execute (table index) state) = controlRoot degree state)
    (gate : Driver) (state : Memory) :
    feedbackEquiv degree table preserves gate state = execute gate (executeRouted degree table state) := rfl

theorem feedbackEquiv_inverse (degree : ℕ) [NeZero degree] (table : Fin degree → Driver)
    (preserves : ∀ index state, controlRoot degree (execute (table index) state) = controlRoot degree state)
    (gate : Driver) (state : Memory) :
    (feedbackEquiv degree table preserves gate).symm state =
      executeRouted degree (reverseTable degree table) (execute gate.reverse state) := rfl

theorem feedback_actual_driver (degree : ℕ) [NeZero degree] (table : Fin degree → Driver)
    (preserves : ∀ index state, controlRoot degree (execute (table index) state) = controlRoot degree state)
    (gate : Driver) (state : Memory) :
    feedbackEquiv degree table preserves gate state = execute ((routeDriver degree table state).concat gate) state :=
  (execute_driver_trans (routeDriver degree table state) gate state).symm

theorem controlRoot_A_left (degree : ℕ) [NeZero degree] (state : Memory) :
    controlRoot degree (execute A_left state) = controlRoot degree state := by
  obtain ⟨⟨⟨left, right⟩, control⟩, rfl⟩ := prepare_surjective state
  simp only [execute_A_left, controlRoot_prepare]

theorem controlRoot_A_right (degree : ℕ) [NeZero degree] (state : Memory) :
    controlRoot degree (execute A_right state) = controlRoot degree state := by
  obtain ⟨⟨⟨left, right⟩, control⟩, rfl⟩ := prepare_surjective state
  simp only [execute_A_right, controlRoot_prepare]

/-- A fixed two-entry table of genuine memory-shift paths. -/
def shiftTable : Fin 2 → Driver := Fin.cases A_left (fun _ => A_right)

@[simp] theorem shiftTable_zero : shiftTable 0 = A_left := rfl

@[simp] theorem shiftTable_one : shiftTable 1 = A_right := by
  change Fin.cases A_left (fun _ => A_right) (0 : Fin 1).succ = A_right
  exact Fin.cases_succ (0 : Fin 1)

theorem shiftTable_preserves : ∀ index state,
    controlRoot 2 (execute (shiftTable index) state) = controlRoot 2 state := by
  intro index state
  exact Fin.cases (controlRoot_A_left 2 state) (fun _ => controlRoot_A_right 2 state) index

def shiftFeedback : Memory ≃ Memory := feedbackEquiv 2 shiftTable shiftTable_preserves B_left

theorem shiftFeedback_first : shiftFeedback (prepare (-1) 0 0) = prepare 0 0 1 := by
  change execute B_left (executeRouted 2 shiftTable (prepare (-1) 0 0)) = prepare 0 0 1
  have route := executeRouted_prepare 2 shiftTable (-1) 0 0 (0 : Fin 2)
  have selected : executeRouted 2 shiftTable (prepare (-1) 0 0) = execute A_left (prepare (-1) 0 0) := by
    simpa using route
  rw [selected, execute_A_left, execute_B_left]
  norm_num

theorem shiftFeedback_second : shiftFeedback (prepare 0 0 1) = prepare 0 1 2 := by
  change execute B_left (executeRouted 2 shiftTable (prepare 0 0 1)) = prepare 0 1 2
  have route := executeRouted_prepare 2 shiftTable 0 0 0 (1 : Fin 2)
  have selected : executeRouted 2 shiftTable (prepare 0 0 1) = execute A_right (prepare 0 0 1) := by
    simpa using route
  rw [selected, execute_A_right, execute_B_left]
  norm_num

theorem shiftFeedback_two_steps :
    shiftFeedback (shiftFeedback (prepare (-1) 0 0)) = prepare 0 1 2 := by
  rw [shiftFeedback_first, shiftFeedback_second]

end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation

/-- Zero-branch transport changes the retained root, not merely its integer description. -/
theorem execute_B_left_zero_ne (state : Memory) (zero : state.val.1.1.val = 1) :
    execute B_left state ≠ state := by
  intro same
  have upper := congrArg (fun root : Memory => root.val.2) same
  rw [execute_B_left_zero state zero] at upper
  have vanished : NestedContinuation.period 1 = 0 :=
    add_left_cancel (upper.trans (add_zero state.val.2).symm)
  have impossible : (1 : ℤ) = 0 := NestedContinuation.period_injective (by
    simpa only [NestedContinuation.period, Int.cast_zero, zero_mul] using vanished)
  exact one_ne_zero impossible

end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation

open unitInterval

/-- The finite alphabet consists of the five existing geometric loops. -/
inductive Gate
  | left | right | zeroLeft | zeroRight | control

def Gate.driver : Gate → Driver
  | .left => A_left
  | .right => A_right
  | .zeroLeft => B_left
  | .zeroRight => B_right
  | .control => controlTurn

/-- A Boolean sign means reverse the same actual base path. -/
abbrev Word := List (Gate × Bool)

def idle : Driver where
  left := Path.refl NestedContinuation.base
  right := Path.refl NestedContinuation.base
  control := Path.refl one
  left_avoids := fun _ => base_ne_one
  right_avoids := fun _ => base_ne_one

theorem execute_idle (state : Memory) : execute idle state = state := by
  apply Subtype.ext
  let constant : C(I, Point) := ContinuousMap.const I state.val
  have same : trajectory idle state = constant :=
    coupled_curve_unique _ _
      (fun t => (trajectory_projects idle state t).trans state.property.symm)
      (trajectory_start idle state)
  exact congrArg (fun curve : C(I, Point) => curve 1) same

def Word.driver : Word → Driver
  | [] => idle
  | (gate, backward) :: rest =>
      (if backward then gate.driver.reverse else gate.driver).concat (Word.driver rest)

def Word.atom (gate : Gate) (backward : Bool := false) : Word := [(gate, backward)]

def Word.control : ℤ → Word
  | .ofNat count => List.replicate count (.control, false)
  | .negSucc count => List.replicate (count + 1) (.control, true)

theorem execute_word_nil (state : Memory) : execute (Word.driver []) state = state := execute_idle state

theorem execute_word_cons (gate : Gate) (backward : Bool) (rest : Word) (state : Memory) :
    execute (Word.driver ((gate, backward) :: rest)) state =
      execute (Word.driver rest) (execute (if backward then gate.driver.reverse else gate.driver) state) :=
  execute_driver_trans _ _ _

theorem execute_word_atom (gate : Gate) (backward : Bool) (state : Memory) :
    execute (Word.driver (Word.atom gate backward)) state =
      execute (if backward then gate.driver.reverse else gate.driver) state := by
  rw [Word.atom, execute_word_cons, execute_word_nil]

theorem execute_word_append (first second : Word) (state : Memory) :
    execute (Word.driver (first ++ second)) state =
      execute (Word.driver second) (execute (Word.driver first) state) := by
  induction first generalizing state with
  | nil => simp only [List.nil_append, execute_word_nil]
  | cons atom rest induction_hypothesis =>
      rcases atom with ⟨gate, backward⟩
      rw [List.cons_append, execute_word_cons, execute_word_cons, induction_hypothesis]

theorem execute_repeat_control (count : ℕ) (left right control : ℤ) :
    execute (Word.driver (List.replicate count (Gate.control, false))) (prepare left right control) =
      prepare left right (control + (count : ℤ)) := by
  induction count generalizing control with
  | zero => simp only [List.replicate_zero, execute_word_nil, Nat.cast_zero, add_zero]
  | succ count induction_hypothesis =>
      rw [List.replicate_succ, execute_word_cons]
      change execute (Word.driver (List.replicate count (Gate.control, false)))
        (execute controlTurn (prepare left right control)) = _
      rw [execute_control_prepare, induction_hypothesis]
      congr 1
      push_cast
      ring

theorem execute_repeat_control_reverse (count : ℕ) (left right control : ℤ) :
    execute (Word.driver (List.replicate count (Gate.control, true))) (prepare left right control) =
      prepare left right (control - (count : ℤ)) := by
  induction count generalizing control with
  | zero => simp only [List.replicate_zero, execute_word_nil, Nat.cast_zero, sub_zero]
  | succ count induction_hypothesis =>
      rw [List.replicate_succ, execute_word_cons]
      change execute (Word.driver (List.replicate count (Gate.control, true)))
        (execute controlTurn.reverse (prepare left right control)) = _
      rw [execute_control_reverse, induction_hypothesis]
      congr 1
      push_cast
      ring

theorem execute_control_word (amount left right control : ℤ) :
    execute (Word.driver (Word.control amount)) (prepare left right control) =
      prepare left right (control + amount) := by
  cases amount with
  | ofNat count => exact execute_repeat_control count left right control
  | negSucc count =>
      rw [Word.control, execute_repeat_control_reverse]
      congr 1

/-- The deck automorphism is exactly an already available control-loop word. -/
theorem controlDeck_eq_control_word (amount : ℤ) (state : Memory) :
    controlDeck amount state = execute (Word.driver (Word.control amount)) state := by
  obtain ⟨⟨⟨left, right⟩, control⟩, rfl⟩ := prepare_surjective state
  change controlDeck amount (prepare left right control) =
    execute (Word.driver (Word.control amount)) (prepare left right control)
  rw [controlDeck_prepare, execute_control_word]

theorem control_word_length (amount : ℤ) : (Word.control amount).length = amount.natAbs := by
  cases amount <;> simp [Word.control]

end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation

/-- A finite program consists only of geometric words and marked stopping roots. -/
structure Program (degree : ℕ) where
  table : Fin degree → Word
  stop : Fin degree → Bool

namespace Program

variable {degree : ℕ} [NeZero degree]

def advance (program : Program degree) (state : Memory) : Memory :=
  executeRouted degree (fun index => Word.driver (program.table index)) state

/-- Stopping reads the same finite cover root through fixed normalized kernels. -/
def haltSignal (program : Program degree) (state : Memory) : ℂ :=
  Choice.dispatch (fun value : ℂ => value ^ degree)
    (fun index => (Radix.omega degree index : ℂ))
    (fun index => if program.stop index then 1 else 0) (controlRoot degree state)

def step (program : Program degree) (state : Memory) : Option Memory :=
  if program.haltSignal state = 1 then none else some (program.advance state)

def eval (program : Program degree) : Memory → Part Memory :=
  StateTransition.eval program.step

theorem advance_prepare (program : Program degree) (left right quotient : ℤ) (index : Fin degree) :
    program.advance (prepare left right ((degree : ℤ) * quotient + index.val)) =
      execute (Word.driver (program.table index))
        (prepare left right ((degree : ℤ) * quotient + index.val)) :=
  executeRouted_prepare degree (fun index => Word.driver (program.table index)) left right quotient index

theorem haltSignal_prepare (program : Program degree) (left right quotient : ℤ) (index : Fin degree) :
    program.haltSignal (prepare left right ((degree : ℤ) * quotient + index.val)) =
      if program.stop index then 1 else 0 := by
  unfold haltSignal
  rw [controlRoot_prepare]
  have root := congrArg (fun value : Circle => (value : ℂ))
    (Radix.readRoot_digit degree quotient index)
  rw [root]
  exact Choice.dispatch_root
    (fun first second same => Radix.omega_injective degree (Subtype.ext same))
    (fun first second => (Radix.omega_complex_pow degree first).trans
      (Radix.omega_complex_pow degree second).symm)
    (Radix.omega_regular degree) index

theorem step_prepare (program : Program degree) (left right quotient : ℤ) (index : Fin degree) :
    program.step (prepare left right ((degree : ℤ) * quotient + index.val)) =
      if program.stop index then none else
        some (execute (Word.driver (program.table index))
          (prepare left right ((degree : ℤ) * quotient + index.val))) := by
  unfold step
  rw [haltSignal_prepare]
  cases program.stop index <;> simp [advance_prepare]

end Program

end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation

/-- An inverse program reverses the word and each oriented geometric loop. -/
def Word.inverse : Word → Word
  | [] => []
  | (gate, backward) :: rest => Word.inverse rest ++ Word.atom gate (!backward)

private theorem execute_opposite (gate : Gate) (backward : Bool) (state : Memory) :
    execute (if !backward then gate.driver.reverse else gate.driver)
      (execute (if backward then gate.driver.reverse else gate.driver) state) = state := by
  cases backward
  · exact execute_driver_reverse gate.driver state
  · exact execute_after_driver_reverse gate.driver state

theorem execute_word_inverse (word : Word) (state : Memory) :
    execute (Word.driver word.inverse) (execute (Word.driver word) state) = state := by
  induction word generalizing state with
  | nil => rw [Word.inverse, execute_word_nil, execute_word_nil]
  | cons atom rest inverse_rest =>
      rcases atom with ⟨gate, backward⟩
      rw [Word.inverse, execute_word_append, execute_word_cons, inverse_rest, execute_word_atom]
      exact execute_opposite gate backward state

theorem Word.inverse_inverse (word : Word) : word.inverse.inverse = word := by
  have append_inverse : ∀ first second : Word,
      (first ++ second).inverse = second.inverse ++ first.inverse := by
    intro first second
    induction first with
    | nil => simp [Word.inverse]
    | cons atom rest recursive =>
        rcases atom with ⟨gate, backward⟩
        simp [Word.inverse, recursive, List.append_assoc]
  induction word with
  | nil => rfl
  | cons atom rest recursive =>
      rcases atom with ⟨gate, backward⟩
      simp [Word.inverse, append_inverse, recursive, Word.atom]

theorem execute_after_word_inverse (word : Word) (state : Memory) :
    execute (Word.driver word) (execute (Word.driver word.inverse) state) = state := by
  have backwards := execute_word_inverse word.inverse state
  simpa only [Word.inverse_inverse] using backwards

end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation

theorem Word.inverse_length (word : Word) : word.inverse.length = word.length := by
  induction word with
  | nil => rfl
  | cons atom rest recursive =>
      rcases atom with ⟨gate, backward⟩
      simp [Word.inverse, Word.atom, recursive]

/-- The finite inverse program has exactly the transport of the actual reverse path. -/
theorem execute_inverse_word_eq (word : Word) (state : Memory) :
    execute (Word.driver word.inverse) state = execute (Word.driver word).reverse state := by
  have inverse := execute_word_inverse word (execute (Word.driver word).reverse state)
  rw [execute_after_driver_reverse] at inverse
  exact inverse

end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation

/-- An admissible based deformation preserves the complete native root state. -/
theorem execute_homotopic (first second : Driver)
    (deformation : first.restrictedPath.Homotopic second.restrictedPath) (state : Memory) :
    execute first state = execute second state := by
  have lower_deformation : (intermediateCurve first state).HomotopicRel
      (intermediateCurve second state) {0, 1} := by
    rw [intermediateCurve_actual_lift first state, intermediateCurve_actual_lift second state]
    exact CoupledPullback.lowerCovering.homotopicRel_liftPath deformation
      (CoupledPullback.upperProjection (restrictedState state))
      (first.restrictedPath.source.trans (restrictedState_over_base state).symm)
      (second.restrictedPath.source.trans (restrictedState_over_base state).symm)
  have upper_end := CoupledPullback.upperCovering.liftPath_apply_one_eq_of_homotopicRel
    lower_deformation (restrictedState state)
      (intermediatePath first state).source (intermediatePath second state).source
  have endpoints : restrictedTrajectory first state 1 = restrictedTrajectory second state 1 := by
    rw [restrictedTrajectory_actual_lift first state, restrictedTrajectory_actual_lift second state]
    exact upper_end
  apply Subtype.ext
  exact congrArg forgetPoint endpoints

end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation.Program

variable {degree : ℕ} [NeZero degree]

/-- A fixed-length advance prefix. Each next driver uses the preceding actual lift result.
The step/eval hypotheses below certify which prefixes respect native stopping. -/
def runDriver (program : Program degree) : ℕ → Memory → Driver
  | 0, _ => idle
  | count + 1, state =>
      (routeDriver degree (fun index => Word.driver (program.table index)) state).concat
        (runDriver program count (program.advance state))

/-- Arbitrary counts describe advance iteration, including counts beyond a stopping return. -/
theorem execute_runDriver (program : Program degree) (count : ℕ) (state : Memory) :
    execute (program.runDriver count state) state = (program.advance)^[count] state := by
  induction count generalizing state with
  | zero => exact execute_idle state
  | succ count induction_hypothesis =>
      rw [runDriver, execute_driver_trans]
      change execute (program.runDriver count (program.advance state)) (program.advance state) = _
      rw [induction_hypothesis, Function.iterate_succ_apply]

private theorem advance_of_step (program : Program degree) {first last : Memory}
    (transition : program.step first = some last) : program.advance first = last := by
  unfold step at transition
  split at transition
  · contradiction
  · exact Option.some.inj transition

/-- A finite native step run has the corresponding number of actual advances. -/
theorem reaches_iterate_advance (program : Program degree) {initial final : Memory}
    (run : StateTransition.Reaches program.step initial final) :
    ∃ count, (program.advance)^[count] initial = final := by
  induction run with
  | refl => exact ⟨0, rfl⟩
  | tail _ edge previous =>
      rcases previous with ⟨count, reached⟩
      refine ⟨count + 1, ?_⟩
      rw [Function.iterate_succ_apply', reached]
      exact advance_of_step program edge

/-- Stopping-respecting finite execution is realized by its causally generated base path. -/
theorem runDriver_of_reaches (program : Program degree) {initial final : Memory}
    (run : StateTransition.Reaches program.step initial final) :
    ∃ count, execute (program.runDriver count initial) initial = final := by
  obtain ⟨count, reached⟩ := reaches_iterate_advance program run
  exact ⟨count, (execute_runDriver program count initial).trans reached⟩

/-- Every complete partial result is obtained by the same actual path construction. -/
theorem runDriver_of_eval (program : Program degree) {initial final : Memory}
    (result : final ∈ program.eval initial) :
    ∃ count, execute (program.runDriver count initial) initial = final :=
  runDriver_of_reaches program (StateTransition.mem_eval.mp result).1

/-- The whole generated prefix is literally lifted through the two matching real covers. -/
theorem runDriver_actual_lifts (program : Program degree) (count : ℕ) (state : Memory) :
    let driver := program.runDriver count state
    intermediateCurve driver state =
      CoupledPullback.lowerCovering.liftPath driver.restrictedPath
        (CoupledPullback.upperProjection (restrictedState state))
        (driver.restrictedPath.source.trans (restrictedState_over_base state).symm) ∧
    restrictedTrajectory driver state =
      CoupledPullback.upperCovering.liftPath (intermediatePath driver state) (restrictedState state)
        (intermediatePath driver state).source ∧
    restrictedTrajectory driver state 1 = restrictedState ((program.advance)^[count] state) := by
  dsimp only
  refine ⟨intermediateCurve_actual_lift _ _, restrictedTrajectory_actual_lift _ _, ?_⟩
  rw [restrictedTrajectory_end, execute_runDriver]

/-- A native finite run ends at the actual endpoint of this generated upper lift. -/
theorem runDriver_endpoint_of_reaches (program : Program degree) {initial final : Memory}
    (run : StateTransition.Reaches program.step initial final) :
    ∃ count,
      restrictedTrajectory (program.runDriver count initial) initial 1 = restrictedState final := by
  obtain ⟨count, reached⟩ := runDriver_of_reaches program run
  refine ⟨count, ?_⟩
  rw [restrictedTrajectory_end, reached]

end Monodromy.CoupledContinuation.Program

/-!
## Reversible conditional control

A finite permutation of control cells is compiled into signed words of the
existing conditional loop. Its inverse is selected from the returned roots.
-/

namespace Monodromy.ReversibleControl

open CoupledContinuation

/-- A static signed word in the one existing zero-conditional loop. -/
def zeroWord : ℤ → Word
  | .ofNat count => List.replicate count (.zeroLeft, false)
  | .negSucc count => List.replicate (count + 1) (.zeroLeft, true)

private theorem execute_B_reverse (left right control : ℤ) :
    execute B_left.reverse (prepare left right control) =
      prepare left right (control - if left = 0 then 1 else 0) := by
  have inverse := execute_driver_reverse B_left
    (prepare left right (control - if left = 0 then 1 else 0))
  rw [execute_B_left] at inverse
  simpa only [sub_add_cancel] using inverse

private theorem repeat_forward (count : ℕ) (left right control : ℤ) :
    execute (Word.driver (List.replicate count (.zeroLeft, false))) (prepare left right control) =
      prepare left right (control + if left = 0 then (count : ℤ) else 0) := by
  induction count generalizing control with
  | zero => simp only [List.replicate_zero, execute_word_nil, Nat.cast_zero, ite_self, add_zero]
  | succ count induction_hypothesis =>
      rw [List.replicate_succ, execute_word_cons]
      change execute (Word.driver (List.replicate count (.zeroLeft, false)))
        (execute B_left (prepare left right control)) = _
      rw [execute_B_left, induction_hypothesis]
      congr 1
      split_ifs <;> push_cast <;> omega

private theorem repeat_backward (count : ℕ) (left right control : ℤ) :
    execute (Word.driver (List.replicate count (.zeroLeft, true))) (prepare left right control) =
      prepare left right (control - if left = 0 then (count : ℤ) else 0) := by
  induction count generalizing control with
  | zero => simp only [List.replicate_zero, execute_word_nil, Nat.cast_zero, ite_self, sub_zero]
  | succ count induction_hypothesis =>
      rw [List.replicate_succ, execute_word_cons]
      change execute (Word.driver (List.replicate count (.zeroLeft, true)))
        (execute B_left.reverse (prepare left right control)) = _
      rw [execute_B_reverse, induction_hypothesis]
      congr 1
      split_ifs <;> push_cast <;> omega

/-- The integer formula is proved from actual forward and reverse lifted loops. -/
theorem execute_zeroWord (amount left right control : ℤ) :
    execute (Word.driver (zeroWord amount)) (prepare left right control) =
      prepare left right (control + if left = 0 then amount else 0) := by
  cases amount with
  | ofNat count => exact repeat_forward count left right control
  | negSucc count =>
      rw [zeroWord, repeat_backward]
      congr 1
      split_ifs <;> omega

variable {degree : ℕ} [NeZero degree]

/-- A finite permutation is compiled into finite words, not a new geometric operation. -/
def table (permutation : Equiv.Perm (Fin degree)) (index : Fin degree) : Word :=
  zeroWord ((permutation index).val - (index.val : ℤ))

/-- The native interpreter and its actual finite-root routing are used unchanged. -/
def program (permutation : Equiv.Perm (Fin degree)) : Program degree :=
  ⟨table permutation, fun _ => false⟩

/-- Each return is an ordinary nonhalting native Word-table step. -/
theorem step_eq_some (permutation : Equiv.Perm (Fin degree)) (state : Memory) :
    (program permutation).step state = some ((program permutation).advance state) := by
  simp [Program.step, Program.haltSignal, program, Choice.dispatch]

/-- The statically compiled primitive count is the absolute PC displacement. -/
theorem word_length (amount : ℤ) : (zeroWord amount).length = amount.natAbs := by
  cases amount <;> simp [zeroWord]

/-- A zero memory permutes the PC residue and retains its whole integer quotient. -/
theorem advance_prepare (permutation : Equiv.Perm (Fin degree))
    (left right quotient : ℤ) (index : Fin degree) :
    (program permutation).advance (prepare left right ((degree : ℤ) * quotient + index.val)) =
      if left = 0 then
        prepare left right ((degree : ℤ) * quotient + (permutation index).val)
      else prepare left right ((degree : ℤ) * quotient + index.val) := by
  rw [Program.advance_prepare]
  change execute (Word.driver (zeroWord ((permutation index).val - (index.val : ℤ))))
    (prepare left right ((degree : ℤ) * quotient + index.val)) = _
  rw [execute_zeroWord]
  by_cases zero : left = 0
  · rw [ite_eq_left zero, ite_eq_left zero]
    congr 1
    omega
  · simp only [ite_eq_right zero, add_zero]

/-- The inverse is another finite word table, selected using the returned control root. -/
theorem inverse_prepare (permutation : Equiv.Perm (Fin degree))
    (left right quotient : ℤ) (index : Fin degree) :
    (program permutation.symm).advance
      ((program permutation).advance (prepare left right ((degree : ℤ) * quotient + index.val))) =
        prepare left right ((degree : ℤ) * quotient + index.val) := by
  rw [advance_prepare]
  by_cases zero : left = 0
  · rw [ite_eq_left zero, advance_prepare, ite_eq_left zero, permutation.symm_apply_apply]
  · rw [ite_eq_right zero, advance_prepare, ite_eq_right zero]

private theorem prepared_residue_induction {property : Memory → Prop}
    (holds : ∀ left right quotient (index : Fin degree),
      property (prepare left right ((degree : ℤ) * quotient + index.val))) (state : Memory) :
    property state := by
  obtain ⟨⟨⟨left, right⟩, control⟩, rfl⟩ := prepare_surjective state
  let index : Fin degree := ⟨(control % (degree : ℤ)).toNat, by
    apply (Int.toNat_lt_of_ne_zero (NeZero.ne degree)).mpr
    exact Int.emod_lt_of_pos _ (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne degree))⟩
  have remainder : (index.val : ℤ) = control % (degree : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast NeZero.ne degree))
  have decomposition : (degree : ℤ) * (control / (degree : ℤ)) + index.val = control := by
    rw [remainder]
    exact Int.mul_ediv_add_emod _ _
  have result := holds left right (control / (degree : ℤ)) index
  rwa [decomposition] at result

/-- The inverse reconstructs the entire raw geometric state, with no retained trace. -/
theorem inverse (permutation : Equiv.Perm (Fin degree)) (state : Memory) :
    (program permutation.symm).advance ((program permutation).advance state) = state :=
  prepared_residue_induction (degree := degree)
    (property := fun point =>
      (program permutation.symm).advance ((program permutation).advance point) = point)
    (inverse_prepare permutation) state

/-- Control permutations compose through the same actual conditional path execution. -/
theorem compose_prepare (first second : Equiv.Perm (Fin degree))
    (left right quotient : ℤ) (index : Fin degree) :
    (program second).advance
      ((program first).advance (prepare left right ((degree : ℤ) * quotient + index.val))) =
    (program (first.trans second)).advance
      (prepare left right ((degree : ℤ) * quotient + index.val)) := by
  rw [advance_prepare]
  by_cases zero : left = 0
  · rw [ite_eq_left zero, advance_prepare, ite_eq_left zero, advance_prepare, ite_eq_left zero]
    rfl
  · rw [ite_eq_right zero, advance_prepare, ite_eq_right zero, advance_prepare, ite_eq_right zero]

theorem compose (first second : Equiv.Perm (Fin degree)) (state : Memory) :
    (program second).advance ((program first).advance state) =
      (program (first.trans second)).advance state :=
  prepared_residue_induction (degree := degree)
    (property := fun point => (program second).advance ((program first).advance point) =
      (program (first.trans second)).advance point)
    (compose_prepare first second) state

/-- The identity permutation compiles to an identity native return. -/
theorem identity (state : Memory) :
    (program (Equiv.refl (Fin degree))).advance state = state := by
  apply prepared_residue_induction (degree := degree)
    (property := fun point => (program (Equiv.refl (Fin degree))).advance point = point)
    (state := state)
  intro left right quotient index
  rw [advance_prepare]
  split_ifs <;> rfl

def executionEquiv (permutation : Equiv.Perm (Fin degree)) : Memory ≃ Memory where
  toFun := (program permutation).advance
  invFun := (program permutation.symm).advance
  left_inv := inverse permutation
  right_inv := by
    intro state
    simpa only [Equiv.symm_symm] using inverse permutation.symm state

/-- The two-PC controlled exchange is a single nonhalting native finite word table. -/
def swap : Program 2 := program (Equiv.swap (0 : Fin 2) 1)

theorem swap_involutive : Function.Involutive swap.advance := by
  intro state
  have symmetry : (Equiv.swap (0 : Fin 2) 1).symm = Equiv.swap (0 : Fin 2) 1 := Equiv.symm_swap _ _
  simpa only [swap, symmetry] using inverse (Equiv.swap (0 : Fin 2) 1) state

end Monodromy.ReversibleControl
