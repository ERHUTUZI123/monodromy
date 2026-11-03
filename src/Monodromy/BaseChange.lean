module

public import Monodromy.Covering

/-!
# Changing coordinates on a cover

Compatible changes of base and total-space coordinates identify the actual
fibers and carry lifted paths to lifted paths.
-/

@[expose] public section

namespace Monodromy.BaseChange

universe u v w

variable {E E' : Type u} {X : Type v} {Y : Type w}
  [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace X] [TopologicalSpace Y]
  {p : E → X} {q : E' → Y}

/-- A commuting change of coordinates identifies fibers over corresponding base points. -/
def fiberEquiv (h : E ≃ₜ E') (b : X ≃ₜ Y) (square : q ∘ h = b ∘ p) (x : X) :
    Transport.Fiber p x ≃ Transport.Fiber q (b x) where
  toFun state := ⟨h state, (congrFun square state).trans (congrArg b state.property)⟩
  invFun state := ⟨h.symm state, by
    apply b.injective
    calc
      b (p (h.symm state)) = q (h (h.symm state)) := (congrFun square (h.symm state)).symm
      _ = q state := congrArg q (h.apply_symm_apply state)
      _ = b x := state.property⟩
  left_inv state := Subtype.ext (h.symm_apply_apply state)
  right_inv state := Subtype.ext (h.apply_symm_apply state)

/-- The coordinate changes intertwine actual transport along the mapped base path. -/
theorem transport (covering : IsCoveringMap p) (covering' : IsCoveringMap q)
    (h : E ≃ₜ E') (b : X ≃ₜ Y) (square : q ∘ h = b ∘ p) {x y : X}
    (path : Path x y) (state : Transport.Fiber p x) :
    fiberEquiv h b square y (Transport.transport covering path state) =
      Transport.transport covering' (path.map b.continuous) (fiberEquiv h b square x state) := by
  obtain ⟨lift, projects, starts, endpoint⟩ := Transport.continuous_lift_exists covering path state
  let mapped : C(unitInterval, E') := (h : C(E, E')).comp lift
  have projects' : q ∘ mapped = path.map b.continuous := by
    funext t
    exact (congrFun square (lift t)).trans (congrArg b (congrFun projects t))
  have starts' : mapped 0 = (fiberEquiv h b square x state : E') :=
    congrArg h starts
  apply Subtype.ext
  exact (congrArg h endpoint).symm.trans
    (Transport.transport_eq_actual_lift covering' (path.map b.continuous)
      (fiberEquiv h b square x state) mapped projects' starts').symm

end Monodromy.BaseChange
