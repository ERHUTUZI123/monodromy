module

public import Monodromy.Logarithm

@[expose] public section

namespace Monodromy.Lattice

open unitInterval

variable {ι : Type*}

/-- A legal joint memory lies over the base point in every coordinate. -/
def Grid (point : ι → ℝ) : Prop := ∀ i, Circle.exp (point i) = 1

/-- Native endpoints determine a joint lift and hence their own projected paths. -/
noncomputable def segment (source target : ι → ℝ) : C(I, ι → ℝ) where
  toFun t i := source i + (t : ℝ) * (target i - source i)
  continuous_toFun := continuous_pi fun _ =>
    continuous_const.add (continuous_subtype_val.mul continuous_const)

theorem segment_start (source target : ι → ℝ) : segment source target 0 = source := by
  funext i
  simp [segment]

theorem segment_end (source target : ι → ℝ) : segment source target 1 = target := by
  funext i
  simp [segment]

noncomputable def segmentPath (source target : ι → ℝ)
    (source_grid : Grid source) (target_grid : Grid target) (i : ι) :
    Path (1 : Circle) 1 where
  toFun t := Circle.exp (segment source target t i)
  continuous_toFun := Circle.exp.continuous.comp
    ((continuous_apply i).comp (segment source target).continuous)
  source' := by rw [segment_start]; exact source_grid i
  target' := by rw [segment_end]; exact target_grid i

/-- The internally generated loop reaches the native target by actual path lifting. -/
theorem segment_transport (source target : ι → ℝ)
    (source_grid : Grid source) (target_grid : Grid target) (i : ι) :
    Transport.transport Circle.isCoveringMap_exp
      (segmentPath source target source_grid target_grid i)
      ⟨source i, source_grid i⟩ = ⟨target i, target_grid i⟩ := by
  apply Subtype.ext
  calc
    _ = segment source target 1 i := Transport.transport_eq_actual_lift
      Circle.isCoveringMap_exp (segmentPath source target source_grid target_grid i)
      ⟨source i, source_grid i⟩
      ⟨fun t => segment source target t i,
        (continuous_apply i).comp (segment source target).continuous⟩
      rfl (congrFun (segment_start source target) i)
    _ = target i := congrFun (segment_end source target) i

namespace Return

variable {Memory : Type*} (coordinates : Memory → ι → ℝ)
  (grid : ∀ memory, Grid (coordinates memory)) (next : Memory → Memory)

noncomputable def coordinate (memory : Memory) (i : ι) : Logarithm.Memory :=
  ⟨coordinates memory i, grid memory i⟩

noncomputable def stepPath (memory : Memory) (i : ι) : Path (1 : Circle) 1 :=
  segmentPath (coordinates memory) (coordinates (next memory)) (grid memory) (grid (next memory)) i

theorem step_transport (memory : Memory) (i : ι) :
    Transport.transport Circle.isCoveringMap_exp (stepPath coordinates grid next memory i)
      (coordinate coordinates grid memory i) = coordinate coordinates grid (next memory) i :=
  segment_transport _ _ _ _ i

/-- Each later path is generated from the succeeding retained state. -/
noncomputable def runPath : ℕ → Memory → ι → Path (1 : Circle) 1
  | 0, _, _ => Path.refl 1
  | rounds + 1, memory, i =>
      (stepPath coordinates grid next memory i).trans
        (runPath rounds (next memory) i)

/-- This realization law applies to every grid-preserving return system. -/
theorem run_transport (rounds : ℕ) (memory : Memory) (i : ι) :
    Transport.transport Circle.isCoveringMap_exp (runPath coordinates grid next rounds memory i)
      (coordinate coordinates grid memory i) =
      coordinate coordinates grid ((next^[rounds]) memory) i := by
  induction rounds generalizing memory with
  | zero => simp [runPath]
  | succ rounds ih =>
      change Transport.transport Circle.isCoveringMap_exp
        ((stepPath coordinates grid next memory i).trans
          (runPath coordinates grid next rounds (next memory) i)) _ = _
      rw [Transport.transport_trans, step_transport, ih, Function.iterate_succ_apply]

end Return

/-- The retained logarithmic branches, with one integer per register. -/
noncomputable def realize (state : ι → ℤ) : ι → ℝ :=
  fun i => (Logarithm.sheet (state i) : ℝ)

noncomputable def basePaths (winding : ι → ℤ) (i : ι) : Path (1 : Circle) 1 :=
  Logarithm.turn (winding i)

/-- Coordinatewise lifts form one continuous curve in the product topology. -/
noncomputable def lift (state winding : ι → ℤ) : C(I, ι → ℝ) where
  toFun t i := Logarithm.lift (state i) (winding i) t
  continuous_toFun := continuous_pi fun i =>
    (Logarithm.lift (state i) (winding i)).continuous

theorem lift_projects (state winding : ι → ℤ) (t : I) (i : ι) :
    Circle.exp (lift state winding t i) = basePaths winding i t := by
  simp [lift, basePaths, Logarithm.lift, Logarithm.turn, add_mul, Circle.exp_add]

theorem lift_start (state winding : ι → ℤ) : lift state winding 0 = realize state := by
  funext i
  simp [lift, realize, Logarithm.lift, Logarithm.sheet]

theorem lift_end (state winding : ι → ℤ) :
    lift state winding 1 = realize (state + winding) := by
  funext i
  simp [lift, realize, Logarithm.lift, Logarithm.sheet]

/-- Any joint continuous lift with these initial branches is this entire curve. -/
theorem lift_unique (state winding : ι → ℤ) (curve : C(I, ι → ℝ))
    (projects : ∀ (t : I) (i : ι), Circle.exp (curve t i) = basePaths winding i t)
    (starts : curve 0 = realize state) : curve = lift state winding := by
  apply ContinuousMap.ext
  intro t
  funext i
  have same : (fun t : I => curve t i) = fun t : I => lift state winding t i :=
    Circle.isCoveringMap_exp.eq_of_comp_eq
      ((continuous_apply i).comp curve.continuous)
      ((continuous_apply i).comp (lift state winding).continuous)
      (by
        funext t
        exact (projects t i).trans (lift_projects state winding t i).symm)
      0 ((congrFun starts i).trans (congrFun (lift_start state winding) i).symm)
  exact congrFun same t

/-- Each coordinate's actual covering transport is the endpoint of the joint curve. -/
theorem transport_endpoint (state winding : ι → ℤ) (i : ι) :
    (Transport.transport Circle.isCoveringMap_exp (basePaths winding i)
      (Logarithm.sheet (state i)) : ℝ) = lift state winding 1 i :=
  Transport.transport_eq_actual_lift Circle.isCoveringMap_exp
    (basePaths winding i) (Logarithm.sheet (state i))
    ⟨fun t => lift state winding t i,
      (continuous_apply i).comp (lift state winding).continuous⟩
    (funext fun t => lift_projects state winding t i)
    (congrFun (lift_start state winding) i)

end Monodromy.Lattice
