module

public import Mathlib.Computability.StateTransition
public import Mathlib.Data.Set.Finite.Basic

/-!
# Closed observations

An observation that evolves on its own carries the complete stopping semantics.
A finite such quotient bounds the information available to internal control.
-/

@[expose] public section

namespace Monodromy.Observation

universe u

def stopped {S : Type*} (next : S → S) (halt : S → Bool) (state : S) : Option S :=
  if halt state then none else some (next state)

/-- An observation closed under evolution preserves the entire partial execution. -/
theorem observed_eval {S F : Type u} (observe : S → F) (next : S → S)
    (advance : F → F) (halt : F → Bool)
    (closed : ∀ state, observe (next state) = advance (observe state)) (state : S) :
    StateTransition.eval (stopped advance halt) (observe state) =
      observe <$> StateTransition.eval (stopped next (fun s => halt (observe s))) state := by
  apply StateTransition.tr_eval' _ _ observe
  apply StateTransition.fun_respects.mpr
  intro source
  by_cases done : halt (observe source) = true
  · simp [stopped, done, StateTransition.FRespects]
  · simp only [stopped, done, StateTransition.FRespects]
    apply Relation.TransGen.single
    simp [stopped, done, closed source]

theorem observed_dom {S F : Type u} (observe : S → F) (next : S → S)
    (advance : F → F) (halt : F → Bool)
    (closed : ∀ state, observe (next state) = advance (observe state)) (state : S) :
    (StateTransition.eval (stopped next (fun s => halt (observe s))) state).Dom ↔
      (StateTransition.eval (stopped advance halt) (observe state)).Dom := by
  rw [observed_eval observe next advance halt closed state]
  rfl

/-- With a finite closed observation, halting depends on a finite set of classes. -/
theorem finite_halting_partition {S F : Type u} [Finite F]
    (observe : S → F) (next : S → S) (advance : F → F) (halt : F → Bool)
    (closed : ∀ state, observe (next state) = advance (observe state)) :
    ∃ accepts : Set F, accepts.Finite ∧ ∀ state,
      (StateTransition.eval (stopped next (fun s => halt (observe s))) state).Dom ↔
        observe state ∈ accepts := by
  refine ⟨{q | (StateTransition.eval (stopped advance halt) q).Dom}, Set.toFinite _, ?_⟩
  intro state
  exact observed_dom observe next advance halt closed state

end Monodromy.Observation
