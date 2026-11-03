module

public import Monodromy.Covering
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Selection and covering symmetry

A selective loop fixes one branch and moves another. Transport naturality
gives a precise structural obstruction: transitive commuting symmetries.
-/

@[expose] public section

namespace Monodromy.Choice

universe u v

open scoped Topology Classical

def Selective {State : Type u} (operation : State → State) : Prop :=
  ∃ source target, operation source = source ∧ operation target ≠ target

theorem fixed_of_transitive_commutants {State : Type u} (operation : State → State)
    (transitive : ∀ source target : State, ∃ symmetry : State → State,
      Function.Commute symmetry operation ∧ symmetry source = target)
    {source : State} (fixed : operation source = source) :
    ∀ target, operation target = target := by
  intro target
  obtain ⟨symmetry, commutes, sends⟩ := transitive source target
  calc
    operation target = operation (symmetry source) := congrArg operation sends.symm
    _ = symmetry (operation source) := (commutes source).symm
    _ = symmetry source := congrArg symmetry fixed
    _ = target := sends

variable {E : Type u} {X : Type v} [TopologicalSpace E] [TopologicalSpace X]
variable {projection : E → X} {base : X}

theorem fixed_of_transitive_selfmaps (covering : IsCoveringMap projection)
    (transitive : ∀ source target : Transport.Fiber projection base,
      ∃ symmetry : C(E, E), ∃ square : projection ∘ symmetry = projection,
        Transport.mapFiber symmetry square source = target)
    (loop : Path base base) {source : Transport.Fiber projection base}
    (fixed : Transport.transport covering loop source = source) :
    ∀ target, Transport.transport covering loop target = target := by
  apply fixed_of_transitive_commutants (Transport.transport covering loop) ?_ fixed
  intro first second
  obtain ⟨symmetry, square, sends⟩ := transitive first second
  exact ⟨Transport.mapFiber symmetry square,
    Transport.loop_selfmap_commute covering symmetry square loop, sends⟩

theorem not_selective_of_transitive_selfmaps (covering : IsCoveringMap projection)
    (transitive : ∀ source target : Transport.Fiber projection base,
      ∃ symmetry : C(E, E), ∃ square : projection ∘ symmetry = projection,
        Transport.mapFiber symmetry square source = target)
    (loop : Path base base) : ¬ Selective (Transport.transport covering loop) := by
  rintro ⟨source, target, fixed, moved⟩
  exact moved (fixed_of_transitive_selfmaps covering transitive loop fixed target)

/-- The equation's removable divided difference, normalized at a marked regular root. -/
noncomputable def kernel (f : ℂ → ℂ) (r z : ℂ) : ℂ :=
  dslope f r z / deriv f r

theorem kernel_self {f : ℂ → ℂ} {r : ℂ} (regular : deriv f r ≠ 0) :
    kernel f r r = 1 := by
  simp [kernel, regular]

theorem kernel_other {f : ℂ → ℂ} {r z : ℂ}
    (other : z ≠ r) (same_fiber : f z = f r) : kernel f r z = 0 := by
  simp [kernel, dslope_of_ne f other, slope_def_field, same_fiber]

theorem analyticAt_dslope {f : ℂ → ℂ} (entire : ∀ z, AnalyticAt ℂ f z)
    (r z : ℂ) : AnalyticAt ℂ (dslope f r) z := by
  by_cases same : z = r
  · subst z
    obtain ⟨series, analytic⟩ := entire r
    exact ⟨series.fslope, analytic.has_fpower_series_dslope_fslope⟩
  · have analytic : AnalyticAt ℂ (fun w => (f w - f r) / (w - r)) z :=
      ((entire z).sub analyticAt_const).div
        (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr same)
    apply analytic.congr
    filter_upwards [isOpen_ne.mem_nhds same] with w other
    simp only [dslope_of_ne f other, slope_def_field]

theorem analyticAt_kernel {f : ℂ → ℂ} (entire : ∀ z, AnalyticAt ℂ f z)
    (r z : ℂ) : AnalyticAt ℂ (kernel f r) z :=
  (analyticAt_dslope entire r z).div_const

/-- On its whole fiber, the equation supplies an analytic indicator of the marked root. -/
theorem kernel_fiber {f : ℂ → ℂ} {r z : ℂ} (regular : deriv f r ≠ 0)
    (same_fiber : f z = f r) : kernel f r z = if z = r then 1 else 0 := by
  split_ifs with same
  · subst z
    exact kernel_self regular
  · exact kernel_other same same_fiber

/-- Standard finite cardinal interpolation from the equation's marked-root kernels. -/
noncomputable def dispatch {ι : Type*} [Fintype ι]
    (f : ℂ → ℂ) (roots values : ι → ℂ) (z : ℂ) : ℂ :=
  ∑ i, kernel f (roots i) z * values i

theorem dispatch_root {ι : Type*} [Fintype ι]
    {f : ℂ → ℂ} {roots values : ι → ℂ}
    (distinct : Function.Injective roots)
    (same_fiber : ∀ i j, f (roots i) = f (roots j))
    (regular : ∀ i, deriv f (roots i) ≠ 0) (j : ι) :
    dispatch f roots values (roots j) = values j := by
  classical
  unfold dispatch
  rw [Finset.sum_eq_single j]
  · rw [kernel_self (regular j), one_mul]
  · intro i _ different
    rw [kernel_other (fun h => different (distinct h).symm) (same_fiber j i), zero_mul]
  · simp

theorem analyticAt_dispatch {ι : Type*} [Fintype ι]
    {f : ℂ → ℂ} (entire : ∀ z, AnalyticAt ℂ f z)
    (roots values : ι → ℂ) (z : ℂ) :
    AnalyticAt ℂ (dispatch f roots values) z := by
  unfold dispatch
  exact Finset.analyticAt_fun_sum Finset.univ
    (fun i _ => (analyticAt_kernel entire (roots i) z).mul analyticAt_const)

end Monodromy.Choice
