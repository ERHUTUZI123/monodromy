module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Computability.StateTransition
public import Mathlib.Data.Set.Finite.Basic
import Lean.Elab.Tactic.Omega

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

namespace Monodromy.Observation

variable {S : Type*}

/-- Termination is exactly a visit to a stopping state under the total return map. -/
theorem stopped_dom_iff (next : S → S) (halt : S → Bool) (state : S) :
    (StateTransition.eval (stopped next halt) state).Dom ↔
      ∃ rounds : ℕ, halt ((next^[rounds]) state) = true := by
  constructor
  · intro terminates
    obtain ⟨target, finished⟩ := Part.dom_iff_mem.mp terminates
    exact StateTransition.evalInduction finished fun current _ successors => by
      cases done : halt current with
      | true => exact ⟨0, done⟩
      | false =>
          obtain ⟨rounds, stops⟩ := successors (next current) (by simp [stopped, done])
          exact ⟨rounds + 1, by simpa only [Function.iterate_succ_apply] using stops⟩
  · rintro ⟨rounds, stops⟩
    induction rounds generalizing state with
    | zero =>
        exact Part.dom_iff_mem.mpr ⟨state,
          StateTransition.mem_eval.mpr ⟨Relation.ReflTransGen.refl, by simpa [stopped] using stops⟩⟩
    | succ rounds previous =>
        cases done : halt state with
        | true =>
            exact Part.dom_iff_mem.mpr ⟨state,
              StateTransition.mem_eval.mpr ⟨Relation.ReflTransGen.refl, by simp [stopped, done]⟩⟩
        | false =>
            have reaches : StateTransition.Reaches (stopped next halt) state (next state) :=
              Relation.ReflTransGen.single (by simp [stopped, done])
            rw [StateTransition.reaches_eval reaches]
            exact previous (next state) (by simpa only [Function.iterate_succ_apply] using stops)

/-- A first visit in a finite orbit occurs before the number of available states. -/
theorem exists_bounded_visit [Fintype S] (next : S → S) (visit : S → Bool) (state : S)
    (eventually : ∃ rounds : ℕ, visit ((next^[rounds]) state) = true) :
    ∃ rounds < Fintype.card S, visit ((next^[rounds]) state) = true := by
  classical
  let first := Nat.find eventually
  have visits : visit ((next^[first]) state) = true := Nat.find_spec eventually
  have no_repeat (left right : Fin (first + 1)) (ordered : left.val < right.val)
      (same : (next^[left.val]) state = (next^[right.val]) state) : False := by
    have repeated := congrArg (next^[first - right.val]) same
    rw [← Function.iterate_add_apply, ← Function.iterate_add_apply] at repeated
    have end_index : first - right.val + right.val = first := by omega
    rw [end_index] at repeated
    have earlier : first - right.val + left.val < first := by omega
    exact Nat.find_min eventually earlier (by rw [repeated]; exact visits)
  have fresh : Function.Injective (fun index : Fin (first + 1) => (next^[index.val]) state) := by
    intro left right same
    apply Fin.ext
    by_contra different
    rcases lt_or_gt_of_ne different with ordered | ordered
    · exact no_repeat left right ordered same
    · exact no_repeat right left ordered same.symm
  have bound : first + 1 ≤ Fintype.card S := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective _ fresh
  exact ⟨first, by omega, visits⟩

/-- Finite autonomous stopping has a complete cardinality-bounded search. -/
theorem finite_stopped_dom_iff [Fintype S] (next : S → S) (halt : S → Bool) (state : S) :
    (StateTransition.eval (stopped next halt) state).Dom ↔
      ∃ rounds < Fintype.card S, halt ((next^[rounds]) state) = true := by
  rw [stopped_dom_iff]
  exact ⟨exists_bounded_visit next halt state, fun ⟨rounds, _, stops⟩ => ⟨rounds, stops⟩⟩

/-- Evaluate at most the finite number of available observation states. -/
def finiteHalts [Fintype S] (next : S → S) (halt : S → Bool) (state : S) : Bool :=
  (List.range (Fintype.card S)).any (fun rounds => halt ((next^[rounds]) state))

theorem finiteHalts_eq_true [Fintype S] (next : S → S) (halt : S → Bool) (state : S) :
    finiteHalts next halt state = true ↔
      (StateTransition.eval (stopped next halt) state).Dom := by
  rw [finite_stopped_dom_iff]
  simp [finiteHalts]

end Monodromy.Observation
