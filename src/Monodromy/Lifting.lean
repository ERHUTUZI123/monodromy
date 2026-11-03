module

public import Monodromy.Programs
import Mathlib.Algebra.Ring.Int.Parity

/-!
# Exact path lifting

The executor follows integer turns of the two base circles. Their unique
continuous lifts are half turns of the phases in the actual quartic space.
-/

@[expose] public section

namespace Monodromy.Execution

private theorem exp_pi : Circle.exp Real.pi = -1 := by
  apply Circle.ext
  simp [Circle.coe_exp, Complex.exp_pi_mul_I]

private theorem exp_integer_pi (n : ℤ) :
    Circle.exp ((n : ℝ) * Real.pi) = if n % 2 = 0 then 1 else -1 := by
  rw [Circle.exp_intCast_mul, exp_pi, neg_one_zpow_eq_ite]
  simp only [Int.even_iff]

/-- A base loop with an exact integer winding number. -/
noncomputable def circlePath (n : ℤ) : Path (1 : Circle) 1 where
  toFun t := Circle.exp (2 * Real.pi * (n : ℝ) * (t : ℝ))
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by
    change Circle.exp (2 * Real.pi * (n : ℝ) * 1) = 1
    rw [mul_one, mul_comm]
    exact Circle.exp_int_mul_two_pi n

noncomputable def windingPath (w : ℤ × ℤ) : Path TorusCover.base TorusCover.base :=
  (circlePath w.1).prod (circlePath w.2)

/-- An analytic lift, before reducing its endpoint to a finite root label. -/
noncomputable def phases (root : Root) (w : ℤ × ℤ) (t : ℝ) : Circle × Circle :=
  (TorusCover.sign root.1 * Circle.exp (Real.pi * t * (w.1 : ℝ)),
   TorusCover.sign root.2 * Circle.exp (Real.pi * t * (w.2 : ℝ)))

noncomputable def lifted (root : Root) (w : ℤ × ℤ) : C(unitInterval, Quartic.Space) where
  toFun t := Quartic.homeomorph (phases root w (t : ℝ))
  continuous_toFun := by unfold phases; fun_prop

private theorem phase_endpoint (bit : Bool) (n : ℤ) :
    TorusCover.sign bit * Circle.exp (Real.pi * (n : ℝ)) =
      TorusCover.sign (if n % 2 == 0 then bit else !bit) := by
  rw [mul_comm Real.pi, exp_integer_pi]
  by_cases h : n % 2 = 0 <;> cases bit <;> simp [h, TorusCover.sign]

theorem lifted_start (root : Root) (w : ℤ × ℤ) :
    lifted root w 0 = (Quartic.bits.symm root).1 := by
  change Quartic.homeomorph (phases root w 0) =
    Quartic.homeomorph (TorusCover.stateOfBits root).1
  simp [phases, TorusCover.stateOfBits]

theorem lifted_endpoint (root : Root) (w : ℤ × ℤ) :
    lifted root w 1 = (Quartic.bits.symm (follow root w)).1 := by
  change Quartic.homeomorph (phases root w 1) =
    Quartic.homeomorph (TorusCover.stateOfBits (follow root w)).1
  apply congrArg Quartic.homeomorph
  simp only [phases, mul_one, phase_endpoint, TorusCover.stateOfBits, follow]

theorem lifted_projects (root : Root) (w : ℤ × ℤ) :
    Quartic.projection ∘ lifted root w = windingPath w := by
  funext t
  apply Prod.ext
  all_goals
    change (_ * Circle.exp _) ^ 2 = _
    rw [mul_pow, ← Circle.exp_natCast_mul]
    have sign_sq (bit : Bool) : TorusCover.sign bit ^ 2 = 1 := by
      cases bit <;> simp [TorusCover.sign]
    rw [sign_sq, one_mul]
    change Circle.exp _ = Circle.exp _
    congr 1
    ring

/-- The computable half-turn rule is the actual covering-space transport. -/
theorem follow_transport (root : Root) (w : ℤ × ℤ) :
    Transport.transport Quartic.isCoveringMap_projection (windingPath w)
      (Quartic.bits.symm root) = Quartic.bits.symm (follow root w) := by
  apply Subtype.ext
  exact (Transport.transport_eq_actual_lift Quartic.isCoveringMap_projection
    (windingPath w) (Quartic.bits.symm root) (lifted root w)
    (lifted_projects root w) (lifted_start root w)).trans (lifted_endpoint root w)

/-- The same analytic lift is the existing feedback motion, at every real time. -/
theorem phases_motion (instruction : Program.Instruction) (root : Root) (t : ℝ) :
    Quartic.homeomorph (phases root (winding instruction root) t) =
      Program.motion instruction (2 * Real.pi * t) (Quartic.bits.symm root).1 := by
  change Quartic.homeomorph (phases root (winding instruction root) t) =
    Program.motion instruction (2 * Real.pi * t)
      (Quartic.homeomorph (TorusCover.stateOfBits root).1)
  rcases root with ⟨a, b⟩
  cases instruction <;> cases a <;> cases b <;>
    simp [phases, winding, Program.motion,
      Quartic.flow, Quartic.gated, Quartic.gatedWrite,
      Torus.flow, Torus.gated, Torus.gatedWrite,
      TorusCover.stateOfBits, TorusCover.sign]
  all_goals ring_nf
  all_goals exact (Circle.exp_neg _).symm

theorem instruction_path (instruction : Program.Instruction) (root : Root) :
    windingPath (winding instruction root) =
      Program.operationPath instruction (Quartic.bits.symm root) := by
  apply Path.ext
  funext t
  calc
    windingPath (winding instruction root) t =
        Quartic.projection (lifted root (winding instruction root) t) :=
      (congrFun (lifted_projects root (winding instruction root)) t).symm
    _ = Program.operationPath instruction (Quartic.bits.symm root) t :=
      congrArg Quartic.projection (phases_motion instruction root (t : ℝ))

theorem circlePath_neg (n : ℤ) : circlePath (-n) = (circlePath n).symm := by
  apply Path.ext
  funext t
  change Circle.exp (2 * Real.pi * ((-n : ℤ) : ℝ) * (t : ℝ)) =
    Circle.exp (2 * Real.pi * (n : ℝ) * (1 - (t : ℝ)))
  apply Circle.exp_eq_exp.mpr
  refine ⟨-n, ?_⟩
  push_cast
  ring

theorem windingPath_neg (w : ℤ × ℤ) :
    windingPath (-w.1, -w.2) = (windingPath w).symm := by
  apply Path.ext
  funext t
  change (circlePath (-w.1) t, circlePath (-w.2) t) =
    ((circlePath w.1).symm t, (circlePath w.2).symm t)
  rw [circlePath_neg, circlePath_neg]

/-- Each inverse instruction traverses the original base segment backwards. -/
theorem inverse_segment (instruction : Program.Instruction) (root : Root) :
    windingPath (turns true instruction (step false instruction root)) =
      (windingPath (turns false instruction root)).symm := by
  have same : winding instruction (step false instruction root) = winding instruction root := by
    rcases root with ⟨a, b⟩
    cases instruction <;> cases a <;> cases b <;> decide
  simp only [turns, Bool.false_eq_true, ↓reduceIte, same]
  exact windingPath_neg _

theorem step_eq_operation (inverse : Bool) (instruction : Program.Instruction) (root : Root) :
    step inverse instruction root = Program.operation instruction root := by
  rcases root with ⟨a, b⟩
  cases inverse <;> cases instruction <;> cases a <;> cases b <;> decide

theorem run_eq_program (inverse : Bool) (program : List Program.Instruction) (root : Root) :
    run inverse program root = Program.run program root := by
  induction program generalizing root with
  | nil => rfl
  | cons instruction rest ih =>
      change run inverse rest (step inverse instruction root) = _
      rw [step_eq_operation, ih]
      rfl

noncomputable def path (inverse : Bool) :
    List Program.Instruction → Root → Path TorusCover.base TorusCover.base
  | [], _ => Path.refl TorusCover.base
  | instruction :: rest, root =>
      (windingPath (turns inverse instruction root)).trans
        (path inverse rest (step inverse instruction root))

/-- Every CLI computation has exactly the endpoint of its complete lifted path. -/
theorem path_correct (inverse : Bool) (program : List Program.Instruction) (root : Root) :
    Transport.transport Quartic.isCoveringMap_projection (path inverse program root)
      (Quartic.bits.symm root) = Quartic.bits.symm (run inverse program root) := by
  induction program generalizing root with
  | nil => exact Transport.transport_refl Quartic.isCoveringMap_projection _
  | cons instruction rest ih =>
      change Transport.transport Quartic.isCoveringMap_projection
        ((windingPath (turns inverse instruction root)).trans
          (path inverse rest (step inverse instruction root))) _ = _
      rw [Transport.transport_trans, follow_transport]
      exact ih (step inverse instruction root)

theorem run_inverse (inverse : Bool) (program : List Program.Instruction) (root : Root) :
    run (!inverse) program.reverse (run inverse program root) = root := by
  simp only [run_eq_program]
  exact Program.run_reverse program root

end Monodromy.Execution
