module

public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Logic.Function.Conjugate
import Mathlib.Tactic.FunProp

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

/-! Coverings are preserved by continuous pullback and finite product. -/

namespace Monodromy.CoverPullback

variable {E X B : Type*} [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace B]

abbrev Space (p : E → X) (g : B → X) := {pair : B × E // p pair.2 = g pair.1}

def projection (p : E → X) (g : B → X) (state : Space p g) : B := state.val.1

set_option backward.isDefEq.respectTransparency false in
theorem covering {p : E → X} (cover : IsCoveringMap p) {g : B → X}
    (continuous_g : Continuous g) : IsCoveringMap (projection p g) := by
  intro point
  let I := p ⁻¹' {g point}
  obtain ⟨discrete, V, in_V, open_V, _, H, over⟩ := cover (g point)
  let U : Set B := g ⁻¹' V
  let forward : (projection p g) ⁻¹' U → U × I := fun state =>
    (⟨state.val.val.1, state.property⟩,
     (H ⟨state.val.val.2, by
       change p state.val.val.2 ∈ V
       rw [state.val.property]
       exact state.property⟩).2)
  let backward : U × I → (projection p g) ⁻¹' U := fun coordinates =>
    let old := H.symm (⟨g coordinates.1.val, coordinates.1.property⟩, coordinates.2)
    ⟨⟨(coordinates.1.val, old.val),
      (over old).symm.trans (by simp [old])⟩, coordinates.1.property⟩
  have left_inverse : Function.LeftInverse backward forward := by
    intro state
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · let old : p ⁻¹' V := ⟨state.val.val.2, by
        change p state.val.val.2 ∈ V
        rw [state.val.property]
        exact state.property⟩
      have same : (⟨g state.val.val.1, state.property⟩, (H old).2) = H old := by
        apply Prod.ext
        · apply Subtype.ext
          exact state.val.property.symm.trans (over old).symm
        · rfl
      change (H.symm (⟨g state.val.val.1, state.property⟩, (H old).2)).val = state.val.val.2
      rw [same, H.symm_apply_apply]
  have right_inverse : Function.RightInverse backward forward := by
    intro coordinates
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · change (H (H.symm (⟨g coordinates.1.val, coordinates.1.property⟩, coordinates.2))).2 = coordinates.2
      rw [H.apply_symm_apply]
  let localHomeomorph : (projection p g) ⁻¹' U ≃ₜ U × I :=
    { toFun := forward
      invFun := backward
      left_inv := left_inverse
      right_inv := right_inverse
      continuous_toFun := by dsimp [forward]; fun_prop
      continuous_invFun := by dsimp [backward]; fun_prop }
  apply IsEvenlyCovered.to_isEvenlyCovered_preimage (I := I)
  refine ⟨discrete, U, in_V, open_V.preimage continuous_g, ?_, localHomeomorph, ?_⟩
  · exact (open_V.preimage continuous_g).preimage (continuous_fst.comp continuous_subtype_val)
  · intro state
    rfl

end Monodromy.CoverPullback

namespace Monodromy.CoverPullback

variable {E X F Y : Type*}
  [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace F] [TopologicalSpace Y]

set_option backward.isDefEq.respectTransparency false in
theorem prodMap {f : E → X} {g : F → Y} (first : IsCoveringMap f) (second : IsCoveringMap g) :
    IsCoveringMap (Prod.map f g) := by
  intro point
  obtain ⟨first_discrete, U, in_U, open_U, _, H, over_H⟩ := first point.1
  obtain ⟨second_discrete, V, in_V, open_V, _, K, over_K⟩ := second point.2
  let I := f ⁻¹' {point.1}
  let J := g ⁻¹' {point.2}
  let : DiscreteTopology I := first_discrete
  let : DiscreteTopology J := second_discrete
  have source_eq : (Prod.map f g) ⁻¹' (U ×ˢ V) = (f ⁻¹' U) ×ˢ (g ⁻¹' V) := rfl
  let localHomeomorph : (Prod.map f g) ⁻¹' (U ×ˢ V) ≃ₜ (U ×ˢ V) × (I × J) :=
    (Homeomorph.setCongr source_eq).trans ((Homeomorph.Set.prod (f ⁻¹' U) (g ⁻¹' V)).trans
      ((H.prodCongr K).trans ((Homeomorph.prodProdProdComm U I V J).trans
        ((Homeomorph.Set.prod U V).symm.prodCongr (Homeomorph.refl (I × J))))))
  apply IsEvenlyCovered.to_isEvenlyCovered_preimage (I := I × J)
  refine ⟨inferInstance, U ×ˢ V, ⟨in_U, in_V⟩, open_U.prod open_V,
    (open_U.prod open_V).preimage (first.continuous.prodMap second.continuous), localHomeomorph, ?_⟩
  intro state
  exact Prod.ext (over_H _) (over_K _)

end Monodromy.CoverPullback

namespace Monodromy.CoverPullback

variable {X : Type*} [TopologicalSpace X]

theorem identity : IsCoveringMap (id : X → X) := by
  intro point
  let U : Set X := Set.univ
  let H : U ≃ₜ U × Unit :=
    { toFun := fun value => (value, ())
      invFun := Prod.fst
      left_inv := fun _ => rfl
      right_inv := fun _ => Prod.ext rfl (Subsingleton.elim _ _)
      continuous_toFun := by fun_prop
      continuous_invFun := continuous_fst }
  apply IsEvenlyCovered.to_isEvenlyCovered_preimage (I := Unit)
  exact ⟨inferInstance, Set.univ, trivial, isOpen_univ, by simp, H, fun _ => rfl⟩

end Monodromy.CoverPullback
