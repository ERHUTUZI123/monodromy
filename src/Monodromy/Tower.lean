module

public import Monodromy.Radix
public import Mathlib.Analysis.Complex.CoveringMap

/-!
# Continuation through the covering tower

The finite root observation is carried by the same path as logarithmic memory.
Thus it records a lower level of the covering tower throughout execution.
-/

@[expose] public section

namespace Monodromy.Radix.Tower

open unitInterval

abbrev Punctured := {z : ℂ // z ≠ 0}

noncomputable def project (x : ℝ) : Punctured :=
  ⟨(Circle.exp x : ℂ), (Circle.exp x).coe_ne_zero⟩

def power (B : ℕ) (z : Punctured) : Punctured :=
  ⟨z.val ^ B, pow_ne_zero B z.property⟩

theorem covering (B : ℕ) [NeZero B] : IsCoveringMap (power B) :=
  isCoveringMap_npow B (by exact_mod_cast NeZero.ne B)

noncomputable def observe (B : ℕ) (x : ℝ) : Punctured := project (x / B)

theorem square (B : ℕ) [NeZero B] (x : ℝ) : power B (observe B x) = project x := by
  apply Subtype.ext
  exact congrArg (fun z : Circle => (z : ℂ)) (readRoot_pow B x)

noncomputable def basePath (curve : C(I, ℝ)) : Path (project (curve 0)) (project (curve 1)) where
  toFun t := project (curve t)
  continuous_toFun := by unfold project; fun_prop
  source' := rfl
  target' := rfl

noncomputable def rootLift (B : ℕ) (curve : C(I, ℝ)) : C(I, Punctured) where
  toFun t := observe B (curve t)
  continuous_toFun := by unfold observe project; fun_prop

/-- Actual finite-cover transport carries the observation of the logarithmic branch. -/
theorem transport_observe (B : ℕ) [NeZero B] (curve : C(I, ℝ)) :
    Transport.transport (covering B) (basePath curve)
      ⟨observe B (curve 0), square B (curve 0)⟩ =
      ⟨observe B (curve 1), square B (curve 1)⟩ := by
  apply Subtype.ext
  exact Transport.transport_eq_actual_lift (covering B) (basePath curve)
    ⟨observe B (curve 0), square B (curve 0)⟩ (rootLift B curve)
    (funext fun t => square B (curve t)) rfl

end Monodromy.Radix.Tower

namespace Monodromy.Radix.Tower

def one : Punctured := ⟨1, one_ne_zero⟩

abbrev Roots (B : ℕ) := Transport.Fiber (power B) one

theorem root_power {B : ℕ} (root : Roots B) : root.val.val ^ B = 1 :=
  congrArg Subtype.val root.property

/-- Multiplication by a root of unity is a continuous symmetry of the power cover. -/
def deck {B : ℕ} (root : Roots B) : C(Punctured, Punctured) where
  toFun point := ⟨root.val.val * point.val, mul_ne_zero root.val.property point.property⟩
  continuous_toFun := by fun_prop

theorem deck_square {B : ℕ} (root : Roots B) : power B ∘ deck root = power B := by
  funext point
  apply Subtype.ext
  change (root.val.val * point.val) ^ B = point.val ^ B
  rw [mul_pow, root_power, one_mul]

def deckAction {B : ℕ} (root : Roots B) : Roots B → Roots B :=
  Transport.mapFiber (deck root) (deck_square root)

theorem deckAction_commute {B : ℕ} (first second : Roots B) :
    Function.Commute (deckAction first) (deckAction second) := by
  intro state
  apply Subtype.ext
  apply Subtype.ext
  change first.val.val * (second.val.val * state.val.val) =
    second.val.val * (first.val.val * state.val.val)
  ring

/-- Root multiplication reaches every branch from every other branch. -/
theorem deckAction_transitive (B : ℕ) (first second : Roots B) :
    ∃ root : Roots B, deckAction root first = second := by
  let ratio : Punctured := ⟨second.val.val / first.val.val,
    div_ne_zero second.val.property first.val.property⟩
  have ratio_root : power B ratio = one := by
    apply Subtype.ext
    change (second.val.val / first.val.val) ^ B = 1
    rw [div_pow, root_power, root_power, div_self one_ne_zero]
  refine ⟨⟨ratio, ratio_root⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change (second.val.val / first.val.val) * first.val.val = second.val.val
  exact div_mul_cancel₀ _ first.val.property

/-- All fixed based-loop transports in a power cover commute. -/
theorem loop_transport_commute (B : ℕ) [NeZero B] (first second : Path one one) :
    Function.Commute (Transport.transport (covering B) first)
      (Transport.transport (covering B) second) := by
  apply Choice.commute_of_transitive_commuting (@deckAction B)
    (deckAction_transitive B) deckAction_commute
  · intro root
    exact (Transport.loop_selfmap_commute (covering B) (deck root) (deck_square root) first).symm
  · intro root
    exact (Transport.loop_selfmap_commute (covering B) (deck root) (deck_square root) second).symm

end Monodromy.Radix.Tower
