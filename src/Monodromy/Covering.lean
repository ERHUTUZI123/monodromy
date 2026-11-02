module

public import Monodromy.Algebra
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Logic.Function.Conjugate
public import Mathlib.Analysis.Convex.Contractible

@[expose] public section

/-!
# Transport from actual continuous covering-space lifts

The state is a point of an actual fiber of `p : E → X`. Transport is the
endpoint of mathlib's continuous path lift, not an independently axiomatized
endpoint function. Composition and homotopy invariance consequently depend on
the covering-space lifting theorems imported above.

The hypothesis `IsCoveringMap p` is explicit. This file does not establish that
a particular polynomial family is a covering, that its fibers are finite, or
that a numerical continuation algorithm computes these ideal lifts.
-/


namespace Monodromy.Transport

open unitInterval

universe u v w

variable {E : Type u} {X : Type v}
variable [TopologicalSpace E] [TopologicalSpace X]
variable {p : E → X}

/-- A persistent state over a specified control point. -/
abbrev Fiber (p : E → X) (x : X) := p ⁻¹' {x}

/-- The endpoint of the actual continuous lift of a based or open path. -/
noncomputable def transport (cov : IsCoveringMap p) {x y : X}
    (γ : Path x y) : Fiber p x → Fiber p y :=
  cov.monodromy (Path.Homotopic.Quotient.mk γ)

/-- Transport is realized by a continuous path with the specified initial state. -/
theorem continuous_lift_exists (cov : IsCoveringMap p) {x y : X}
    (γ : Path x y) (e : Fiber p x) :
    ∃ Γ : C(I, E), p ∘ Γ = γ ∧ Γ 0 = (e : E) ∧
      Γ 1 = (transport cov γ e : E) := by
  let start : γ 0 = p (e : E) := γ.source.trans e.2.symm
  refine ⟨cov.liftPath γ e start, cov.liftPath_lifts γ e start,
    cov.liftPath_zero γ e start, ?_⟩
  exact (cov.coe_monodromy_mk γ e).symm

/-- Any continuous lift from this state is the same lifted path. -/
theorem continuous_lift_unique (cov : IsCoveringMap p) {x y : X}
    (γ : Path x y) (e : Fiber p x) (Γ : C(I, E))
    (projects : p ∘ Γ = γ) (starts : Γ 0 = (e : E)) :
    Γ = cov.liftPath γ e (γ.source.trans e.2.symm) := by
  exact (cov.eq_liftPath_iff' (γ.source.trans e.2.symm)).mpr ⟨projects, starts⟩

/-- A supplied actual continuous lift has exactly the declared transport endpoint. -/
theorem transport_eq_actual_lift (cov : IsCoveringMap p) {x y : X}
    (γ : Path x y) (e : Fiber p x) (Γ : C(I, E))
    (projects : p ∘ Γ = γ) (starts : Γ 0 = (e : E)) :
    (transport cov γ e : E) = Γ 1 := by
  exact cov.monodromy_eq_apply_one projects starts

/-- Serial path execution: the first path acts first, then the second path. -/
theorem transport_trans (cov : IsCoveringMap p) {x y z : X}
    (γ : Path x y) (δ : Path y z) (e : Fiber p x) :
    transport cov (γ.trans δ) e = transport cov δ (transport cov γ e) := by
  exact cov.monodromy_trans_apply (Path.Homotopic.Quotient.mk γ)
    (Path.Homotopic.Quotient.mk δ) e

/-- Endpoint-fixed path homotopy preserves the transported state. -/
theorem transport_homotopic (cov : IsCoveringMap p) {x y : X}
    {γ δ : Path x y} (homotopy : γ.Homotopic δ) (e : Fiber p x) :
    transport cov γ e = transport cov δ e := by
  exact congrArg (fun q : Path.Homotopic.Quotient x y => cov.monodromy q e)
    (Quotient.sound homotopy)

/-- The constant path retains the actual state. -/
@[simp] theorem transport_refl (cov : IsCoveringMap p) {x : X} (e : Fiber p x) :
    transport cov (Path.refl x) e = e := by
  change cov.monodromy (Path.Homotopic.Quotient.refl x) e = e
  exact congrFun (cov.monodromy_refl (x := x)) e

/-- Executing a path and then its reverse restores the ideal carried state. -/
@[simp] theorem transport_reverse (cov : IsCoveringMap p) {x y : X}
    (γ : Path x y) (e : Fiber p x) :
    transport cov γ.symm (transport cov γ e) = e := by
  calc
    transport cov γ.symm (transport cov γ e) =
        transport cov (γ.trans γ.symm) e := (transport_trans cov γ γ.symm e).symm
    _ = transport cov (Path.refl x) e :=
      transport_homotopic cov (Path.Homotopic.trans_symm γ) e
    _ = e := transport_refl cov e

/-- Reverse execution followed by forward execution also restores the state. -/
@[simp] theorem reverse_transport (cov : IsCoveringMap p) {x y : X}
    (γ : Path x y) (e : Fiber p y) :
    transport cov γ (transport cov γ.symm e) = e := by
  calc
    transport cov γ (transport cov γ.symm e) =
        transport cov (γ.symm.trans γ) e := (transport_trans cov γ.symm γ e).symm
    _ = transport cov (Path.refl y) e :=
      transport_homotopic cov (Path.Homotopic.symm_trans γ) e
    _ = e := transport_refl cov e

/-- Open-path transport is a fiber equivalence; loops specialize to permutations. -/
noncomputable def transportEquiv (cov : IsCoveringMap p) {x y : X}
    (γ : Path x y) : Fiber p x ≃ Fiber p y where
  toFun := transport cov γ
  invFun := transport cov γ.symm
  left_inv := transport_reverse cov γ
  right_inv := reverse_transport cov γ

section Naturality

variable {E' : Type w} [TopologicalSpace E'] {q : E' → X}

/-- A commuting map of total spaces restricts to a map of each actual fiber. -/
def mapFiber (h : E → E') (square : q ∘ h = p) {x : X} :
    Fiber p x → Fiber q x :=
  fun e => ⟨h e, (congrFun square e).trans e.2⟩

/-- A continuous commuting map sends an actual lift to the corresponding lift.
The proof constructs the continuous path `h ∘ Γ` and uses lift uniqueness. -/
theorem transport_naturality (cov : IsCoveringMap p) (cov' : IsCoveringMap q)
    (h : C(E, E')) (square : q ∘ h = p) {x y : X}
    (γ : Path x y) (e : Fiber p x) :
    transport cov' γ (mapFiber h square e) =
      mapFiber h square (transport cov γ e) := by
  obtain ⟨Γ, projects, starts, endpoint⟩ := continuous_lift_exists cov γ e
  let Γ' : C(I, E') := h.comp Γ
  have projects' : q ∘ Γ' = γ := by
    funext t
    change q (h (Γ t)) = γ t
    exact (congrFun square (Γ t)).trans (congrFun projects t)
  have starts' : Γ' 0 = (mapFiber h square e : E') := by
    change h (Γ 0) = h e
    rw [starts]
  apply Subtype.ext
  calc
    (transport cov' γ (mapFiber h square e) : E') = Γ' 1 :=
      transport_eq_actual_lift cov' γ (mapFiber h square e) Γ' projects' starts'
    _ = h (transport cov γ e) := by
      change h (Γ 1) = h (transport cov γ e)
      rw [endpoint]
    _ = (mapFiber h square (transport cov γ e) : E') := rfl

/-- A covering-space self-map commutes with transport along any open path. -/
theorem selfmap_commutes (cov : IsCoveringMap p) (h : C(E, E))
    (square : p ∘ h = p) {x y : X} (γ : Path x y) (e : Fiber p x) :
    mapFiber h square (transport cov γ e) =
      transport cov γ (mapFiber h square e) :=
  (transport_naturality cov cov h square γ e).symm

/-- For loops, the commuting relation is an equality of fiber endomorphisms. -/
theorem loop_selfmap_commute (cov : IsCoveringMap p) (h : C(E, E))
    (square : p ∘ h = p) {x : X} (γ : Path x x) :
    Function.Commute (mapFiber h square : Fiber p x → Fiber p x) (transport cov γ) := by
  intro e
  exact selfmap_commutes cov h square γ e

/-- An actual covering isomorphism gives a specified identification of fibers. -/
def fiberEquiv (h : E ≃ₜ E') (square : q ∘ h = p) (x : X) :
    Fiber p x ≃ Fiber q x where
  toFun := mapFiber h square
  invFun e := ⟨h.symm e, by
    calc
      p (h.symm e) = q (h (h.symm e)) := (congrFun square (h.symm e)).symm
      _ = q e := congrArg q (h.apply_symm_apply e)
      _ = x := e.2⟩
  left_inv e := Subtype.ext (h.symm_apply_apply e)
  right_inv e := Subtype.ext (h.apply_symm_apply e)

/-- Transport intertwines the actual fiber identification of a covering isomorphism.
Together with `fiberEquiv` this is the fiberwise conjugacy statement. -/
theorem fiberEquiv_transport (cov : IsCoveringMap p) (cov' : IsCoveringMap q)
    (h : E ≃ₜ E') (square : q ∘ h = p) {x y : X}
    (γ : Path x y) (e : Fiber p x) :
    fiberEquiv h square y (transport cov γ e) =
      transport cov' γ (fiberEquiv h square x e) := by
  exact (transport_naturality cov cov' (h : C(E, E')) square γ e).symm

end Naturality

end Monodromy.Transport

/-!
# Protection from a continuous rectangle

A rectangle in the actual covering base identifies its two boundary programs.
When its horizontal edges are the same migration path, this yields protection
of the old loop under the actual fiber transport. The rectangle is data; an
independent intertwining assertion is not assumed.
-/


namespace Monodromy.Protection

open unitInterval

universe u v

variable {X : Type u} [TopologicalSpace X]

/-- Traverse the parameter coordinate at fixed path time. -/
def horizontal (t : I) : Path ((0 : I), t) (1, t) where
  toFun s := (s, t)
  continuous_toFun := continuous_id.prodMk continuous_const
  source' := rfl
  target' := rfl

/-- Traverse the path coordinate at a fixed parameter. -/
def vertical (s : I) : Path (s, (0 : I)) (s, 1) where
  toFun t := (s, t)
  continuous_toFun := continuous_const.prodMk continuous_id
  source' := rfl
  target' := rfl

/-- The actual continuous rectangle fills the two boundary routes. -/
theorem rectangle_homotopic
    {x₀₀ x₀₁ x₁₀ x₁₁ : X}
    (old : Path x₀₀ x₀₁) (new : Path x₁₀ x₁₁)
    (start : Path x₀₀ x₁₀) (finish : Path x₀₁ x₁₁)
    (H : C(I × I, X))
    (left : ∀ t, H (0, t) = old t)
    (right : ∀ t, H (1, t) = new t)
    (bottom : ∀ s, H (s, 0) = start s)
    (top : ∀ s, H (s, 1) = finish s) :
    (old.trans finish).Homotopic (start.trans new) := by
  let : ContractibleSpace I :=
    (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by simp⟩
  obtain ⟨rectangle⟩ := SimplyConnectedSpace.paths_homotopic
    ((vertical 0).trans (horizontal 1))
    ((horizontal 0).trans (vertical 1))
  have first : (((vertical 0).trans (horizontal 1)).map H.continuous).toContinuousMap =
      (old.trans finish).toContinuousMap := by
    ext t
    change H (((vertical 0).trans (horizontal 1)) t) = (old.trans finish) t
    rw [Path.trans_apply, Path.trans_apply]
    split_ifs
    · exact left _
    · exact top _
  have second : (((horizontal 0).trans (vertical 1)).map H.continuous).toContinuousMap =
      (start.trans new).toContinuousMap := by
    ext t
    change H (((horizontal 0).trans (vertical 1)) t) = (start.trans new) t
    rw [Path.trans_apply, Path.trans_apply]
    split_ifs
    · exact bottom _
    · exact right _
  exact ⟨ContinuousMap.HomotopyRel.cast (rectangle.map H) first second⟩

/-- The filled rectangle equates the endpoints of the two actual lifted routes. -/
theorem rectangle_transport
    {E : Type v} [TopologicalSpace E] {p : E → X} (cov : IsCoveringMap p)
    {x₀₀ x₀₁ x₁₀ x₁₁ : X}
    (old : Path x₀₀ x₀₁) (new : Path x₁₀ x₁₁)
    (start : Path x₀₀ x₁₀) (finish : Path x₀₁ x₁₁)
    (H : C(I × I, X))
    (left : ∀ t, H (0, t) = old t)
    (right : ∀ t, H (1, t) = new t)
    (bottom : ∀ s, H (s, 0) = start s)
    (top : ∀ s, H (s, 1) = finish s)
    (state : Transport.Fiber p x₀₀) :
    Transport.transport cov new (Transport.transport cov start state) =
      Transport.transport cov finish (Transport.transport cov old state) := by
  rw [← Transport.transport_trans, ← Transport.transport_trans]
  exact Transport.transport_homotopic cov
    (rectangle_homotopic old new start finish H left right bottom top).symm state

/-- A continuous family of loops protects the old action through actual migration. -/
theorem loop_family_intertwines
    {E : Type v} [TopologicalSpace E] {p : E → X} (cov : IsCoveringMap p)
    {x y : X} (old : Path x x) (new : Path y y) (migration : Path x y)
    (H : C(I × I, X))
    (left : ∀ t, H (0, t) = old t)
    (right : ∀ t, H (1, t) = new t)
    (bottom : ∀ s, H (s, 0) = migration s)
    (top : ∀ s, H (s, 1) = migration s) :
    Algebra.Intertwines (Transport.transportEquiv cov migration)
      (Transport.transportEquiv cov old) (Transport.transportEquiv cov new) := by
  intro state
  exact rectangle_transport cov old new migration migration H left right bottom top state

end Monodromy.Protection
