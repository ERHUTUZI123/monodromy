module

public import Monodromy.Covering
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
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

namespace Monodromy.Choice

/-- Exact arbitrary-table readout by these kernels characterizes distinct regular roots. -/
theorem dispatch_exact_iff {ι : Type*} [Fintype ι]
    {f : ℂ → ℂ} {roots : ι → ℂ}
    (same_fiber : ∀ i j, f (roots i) = f (roots j)) :
    (∀ values : ι → ℂ, ∀ i, dispatch f roots values (roots i) = values i) ↔
      Function.Injective roots ∧ ∀ i, deriv f (roots i) ≠ 0 := by
  classical
  constructor
  · intro reads
    constructor
    · intro first second same
      by_contra different
      have one := reads (fun i => if i = first then 1 else 0) first
      have zero := reads (fun i => if i = first then 1 else 0) second
      rw [same] at one
      have impossible := one.symm.trans zero
      simp [Ne.symm different] at impossible
    · intro i critical
      have self : kernel f (roots i) (roots i) = 1 := by
        simpa [dispatch] using reads (fun j => if j = i then 1 else 0) i
      simp [kernel, critical] at self
  · rintro ⟨distinct, regular⟩ values i
    exact dispatch_root distinct same_fiber regular i

end Monodromy.Choice

namespace Monodromy.Choice

theorem dslope_comp {f g : ℂ → ℂ} {r : ℂ}
    (outer : DifferentiableAt ℂ f (g r)) (inner : DifferentiableAt ℂ g r) (w : ℂ) :
    dslope (f ∘ g) r w = dslope f (g r) (g w) * dslope g r w := by
  by_cases same : w = r
  · subst w
    simpa only [dslope_same] using deriv_comp r outer inner
  · have inner_difference : (w - r) * dslope g r w = g w - g r := by
      simpa only [smul_eq_mul] using sub_smul_dslope g r w
    have outer_difference :
        (g w - g r) * dslope f (g r) (g w) = f (g w) - f (g r) := by
      simpa only [smul_eq_mul] using sub_smul_dslope f (g r) (g w)
    apply mul_left_cancel₀ (sub_ne_zero.mpr same)
    calc
      (w - r) * dslope (f ∘ g) r w = f (g w) - f (g r) := by
        simpa only [smul_eq_mul, Function.comp_apply] using sub_smul_dslope (f ∘ g) r w
      _ = (g w - g r) * dslope f (g r) (g w) := outer_difference.symm
      _ = (w - r) * (dslope f (g r) (g w) * dslope g r w) := by
        rw [← inner_difference]
        ring

/-- Outer and inner branch selectors multiply along a composite defining equation. -/
theorem kernel_comp {f g : ℂ → ℂ} {r : ℂ}
    (outer : DifferentiableAt ℂ f (g r)) (inner : DifferentiableAt ℂ g r) (w : ℂ) :
    kernel (f ∘ g) r w = kernel f (g r) (g w) * kernel g r w := by
  unfold kernel
  rw [dslope_comp outer inner, deriv_comp r outer inner]
  exact (div_mul_div_comm _ _ _ _).symm

theorem dslope_affine (a b r w : ℂ) :
    dslope (fun z : ℂ => a * z + b) r w = a := by
  by_cases same : w = r
  · subst w
    simpa only [dslope_same, mul_one, id_eq] using
      (((hasDerivAt_id r).const_mul a).add_const b).deriv
  · rw [dslope_of_ne _ same, slope_def_field]
    field_simp [sub_ne_zero.mpr same]
    ring

theorem kernel_affine {a : ℂ} (nonzero : a ≠ 0) (b r w : ℂ) :
    kernel (fun z : ℂ => a * z + b) r w = 1 := by
  unfold kernel
  rw [dslope_affine]
  have derivative : deriv (fun z : ℂ => a * z + b) r = a := by
    simpa only [mul_one, id_eq] using (((hasDerivAt_id r).const_mul a).add_const b).deriv
  rw [derivative, div_self nonzero]

/-- Affine changes of input preserve the normalized selector in the transformed coordinates. -/
theorem kernel_comp_affine {f : ℂ → ℂ} {a r : ℂ}
    (nonzero : a ≠ 0) (b : ℂ) (outer : DifferentiableAt ℂ f (a * r + b)) (w : ℂ) :
    kernel (f ∘ (fun z : ℂ => a * z + b)) r w =
      kernel f (a * r + b) (a * w + b) := by
  rw [kernel_comp (g := fun z : ℂ => a * z + b) outer
      (((hasDerivAt_id r).const_mul a).add_const b).differentiableAt,
    kernel_affine nonzero, mul_one]

/-- Affine changes of output preserve the selector itself. -/
theorem kernel_affine_comp {f : ℂ → ℂ} {a r : ℂ}
    (nonzero : a ≠ 0) (b : ℂ) (inner : DifferentiableAt ℂ f r) (w : ℂ) :
    kernel ((fun z : ℂ => a * z + b) ∘ f) r w = kernel f r w := by
  rw [kernel_comp (f := fun z : ℂ => a * z + b) (g := f)
      (((hasDerivAt_id (f r)).const_mul a).add_const b).differentiableAt inner,
    kernel_affine nonzero, one_mul]

/-- A flat composite-fiber readout is exactly an outer readout of inner readouts. -/
theorem dispatch_comp {ι κ : Type*} [Fintype ι] [Fintype κ]
    {f g : ℂ → ℂ} (outerRoots : ι → ℂ) (children values : ι → κ → ℂ)
    (projects : ∀ i j, g (children i j) = outerRoots i)
    (outer : ∀ i, DifferentiableAt ℂ f (outerRoots i))
    (inner : ∀ i j, DifferentiableAt ℂ g (children i j)) (w : ℂ) :
    dispatch (f ∘ g) (fun index : ι × κ => children index.1 index.2)
      (fun index : ι × κ => values index.1 index.2) w =
      ∑ i, kernel f (outerRoots i) (g w) * dispatch g (children i) (values i) w := by
  classical
  unfold dispatch
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have differentiable : DifferentiableAt ℂ f (g (children i j)) := by
    rw [projects]
    exact outer i
  rw [kernel_comp differentiable (inner i j), projects]
  ring

end Monodromy.Choice

namespace Monodromy.Choice

/-- Refinement preserves the parent selector exactly when every inner branch is represented. -/
theorem kernel_refinement_iff {κ : Type*} [Fintype κ]
    {f g : ℂ → ℂ} {parent : ℂ} (children : κ → ℂ)
    (distinct : Function.Injective children)
    (projects : ∀ child, g (children child) = parent)
    (regular : deriv f parent ≠ 0)
    (children_regular : ∀ child, deriv (f ∘ g) (children child) ≠ 0) :
    (∀ z, f (g z) = f parent →
      kernel f parent (g z) = ∑ child, kernel (f ∘ g) (children child) z) ↔
      ∀ z, g z = parent → ∃ child, children child = z := by
  classical
  constructor
  · intro refines z same
    by_contra missing
    have zero (child : κ) : kernel (f ∘ g) (children child) z = 0 := by
      apply kernel_other
      · intro equal
        exact missing ⟨child, equal.symm⟩
      · change f (g z) = f (g (children child))
        rw [same, projects child]
    have impossible := refines z (congrArg f same)
    rw [same, kernel_self regular] at impossible
    have total_zero : (∑ child, kernel (f ∘ g) (children child) z) = 0 :=
      Finset.sum_eq_zero (fun child _ => zero child)
    rw [total_zero] at impossible
    exact one_ne_zero impossible
  · intro complete z same_fiber
    by_cases same : g z = parent
    · obtain ⟨child, rfl⟩ := complete z same
      rw [projects child, kernel_self regular]
      have read := dispatch_root (values := fun _ : κ => (1 : ℂ)) distinct
        (fun first second => by simp only [Function.comp_apply, projects]) children_regular child
      simpa only [dispatch, mul_one] using read.symm
    · rw [kernel_other same same_fiber]
      symm
      apply Finset.sum_eq_zero
      intro child _
      apply kernel_other
      · intro equal
        exact same ((congrArg g equal).trans (projects child))
      · change f (g z) = f (g (children child))
        simpa only [projects] using same_fiber

end Monodromy.Choice

namespace Monodromy.Choice

/-- Equivariant maps for a transitive commuting family commute with one another. -/
theorem commute_of_transitive_commuting {H S : Type*} (action : H → S → S)
    (transitive : ∀ first second, ∃ symmetry, action symmetry first = second)
    (commuting : ∀ first second, Function.Commute (action first) (action second))
    (f g : S → S) (f_equivariant : ∀ symmetry, Function.Commute f (action symmetry))
    (g_equivariant : ∀ symmetry, Function.Commute g (action symmetry)) : Function.Commute f g := by
  intro state
  obtain ⟨first, sends_first⟩ := transitive state (f state)
  obtain ⟨second, sends_second⟩ := transitive state (g state)
  calc
    f (g state) = f (action second state) := congrArg f sends_second.symm
    _ = action second (f state) := f_equivariant second state
    _ = action second (action first state) := congrArg (action second) sends_first.symm
    _ = action first (action second state) := commuting second first state
    _ = action first (g state) := congrArg (action first) sends_second
    _ = g (action first state) := (g_equivariant first state).symm
    _ = g (f state) := congrArg g sends_first

end Monodromy.Choice
