module

public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.Group.Subgroup.Defs

@[expose] public section

/-!
# Transport and protected finite actions

These are native algebraic objects and proofs.  A geometric model must separately
construct its fiber equivalence and prove `Intertwines`; this file does not assume
that a proposed path or parameter update satisfies a covering-space contract.

Permutation multiplication is function composition: `a * b` executes `b` first.
-/


namespace Monodromy.Algebra

universe u v

variable {S : Type u} {T : Type v}

/-- One common fiber identification intertwines an old and a new action. -/
def Intertwines (transport : S ≃ T) (old : Equiv.Perm S)
    (new : Equiv.Perm T) : Prop :=
  ∀ state, new (transport state) = transport (old state)

/-- Intertwining determines the new action by conjugating through the transport. -/
theorem intertwines_conjugation
    (transport : S ≃ T) (old : Equiv.Perm S) (new : Equiv.Perm T)
    (preserves : Intertwines transport old new) :
    new = (transport.symm.trans old).trans transport := by
  apply Equiv.ext
  intro state
  simpa only [Equiv.trans_apply, Equiv.apply_symm_apply] using
    preserves (transport.symm state)

/-- The same fiber transport preserves compositions of protected actions. -/
theorem intertwines_mul
    (transport : S ≃ T) (a b : Equiv.Perm S) (a' b' : Equiv.Perm T)
    (ha : Intertwines transport a a') (hb : Intertwines transport b b') :
    Intertwines transport (a * b) (a' * b') := by
  intro state
  change a' (b' (transport state)) = transport (a (b state))
  rw [hb state, ha (b state)]

/-- If a closed parameter transport returns the same action, they commute. -/
theorem closed_intertwining_commutes
    (transport old : Equiv.Perm S)
    (preserves : Intertwines transport old old) :
    Commute old transport := by
  change old * transport = transport * old
  apply Equiv.ext
  intro state
  exact preserves state

/-- Protecting each declared action makes a closed transport centralize the library. -/
theorem closed_intertwining_centralizes
    {Action : Type v} (transport : Equiv.Perm S)
    (library : Action → Equiv.Perm S)
    (preserves : ∀ action, Intertwines transport (library action) (library action)) :
    ∀ action, Commute (library action) transport := by
  intro action
  exact closed_intertwining_commutes transport (library action) (preserves action)

private theorem exists_outside_pair
    [Fintype S] [DecidableEq S] (atLeastThree : 3 ≤ Fintype.card S)
    (a b : S) : ∃ state : S, state ≠ a ∧ state ≠ b := by
  classical
  by_contra absent
  have covered : ∀ state : S, state = a ∨ state = b := by
    intro state
    by_cases ha : state = a
    · exact Or.inl ha
    · right
      by_contra hb
      exact absent ⟨state, ha, hb⟩
  have subset : (Finset.univ : Finset S) ⊆ {a, b} := by
    intro state _
    simpa only [Finset.mem_insert, Finset.mem_singleton] using covered state
  have pairCard : ({a, b} : Finset S).card ≤ 2 := by
    exact Finset.card_le_two
  have tooSmall : Fintype.card S ≤ 2 := by
    simpa only [Finset.card_univ] using (Finset.card_le_card subset).trans pairCard
  exact (by decide : ¬ (3 ≤ 2)) (atLeastThree.trans tooSmall)

/-- A permutation commuting with every permutation is trivial on at least three states. -/
theorem eq_one_of_commutes_all
    [Fintype S] [DecidableEq S] (atLeastThree : 3 ≤ Fintype.card S)
    (transport : Equiv.Perm S)
    (centralizes : ∀ action : Equiv.Perm S, Commute transport action) :
    transport = 1 := by
  classical
  apply Equiv.ext
  intro state
  change transport state = state
  by_contra moved
  obtain ⟨third, third_ne_state, third_ne_image⟩ :=
    exists_outside_pair atLeastThree state (transport state)
  have fixed : Equiv.swap (transport state) third state = state := by
    simp [Equiv.swap_apply_def, Ne.symm moved, Ne.symm third_ne_state]
  have equality :
      transport * Equiv.swap (transport state) third =
        Equiv.swap (transport state) third * transport :=
    centralizes (Equiv.swap (transport state) third)
  have evaluated := congrArg (fun action : Equiv.Perm S => action state) equality
  have image_eq_third : transport state = third := by
    simpa only [Equiv.Perm.mul_apply, fixed, Equiv.swap_apply_left] using evaluated
  exact third_ne_image image_eq_third.symm

/-- Full action protection leaves no nontrivial closed transport on three or more states. -/
theorem eq_one_of_intertwines_all
    [Fintype S] [DecidableEq S] (atLeastThree : 3 ≤ Fintype.card S)
    (transport : Equiv.Perm S)
    (preserves : ∀ action : Equiv.Perm S, Intertwines transport action action) :
    transport = 1 := by
  apply eq_one_of_commutes_all atLeastThree transport
  intro action
  exact (closed_intertwining_commutes transport action (preserves action)).symm

/-- The old control action in the nested-quartic example, defined algebraically. -/
def A : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 2 3

/-- The parameter-loop action in the nested-quartic example, defined algebraically. -/
def tau : Equiv.Perm (Fin 4) := Equiv.swap 0 2 * Equiv.swap 1 3

theorem A_zero : A 0 = 1 := by decide
theorem A_one : A 1 = 0 := by decide
theorem A_two : A 2 = 3 := by decide
theorem A_three : A 3 = 2 := by decide

theorem tau_zero : tau 0 = 2 := by decide
theorem tau_one : tau 1 = 3 := by decide
theorem tau_two : tau 2 = 0 := by decide
theorem tau_three : tau 3 = 1 := by decide

theorem A_mul_A : A * A = 1 := by decide
theorem tau_mul_tau : tau * tau = 1 := by decide
theorem A_inv : A⁻¹ = A := by decide
theorem A_ne_one : A ≠ 1 := by decide
theorem tau_ne_one : tau ≠ 1 := by decide
theorem tau_ne_A : tau ≠ A := by decide
theorem A_commutes_tau : Commute A tau := by
  change A * tau = tau * A
  decide

/-- These four joint programs reach every state from every initial state. -/
theorem joint_action_transitive : ∀ start target : Fin 4,
    start = target ∨ A start = target ∨ tau start = target ∨
      (A * tau) start = target := by decide

/-- The old library's whole subgroup, explicitly closed under multiplication/inverse. -/
def oldSubgroup : Subgroup (Equiv.Perm (Fin 4)) where
  carrier := {action | action = 1 ∨ action = A}
  one_mem' := Or.inl rfl
  mul_mem' := by
    intro a b ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
      simp [A_mul_A]
  inv_mem' := by
    intro action h
    rcases h with rfl | rfl <;> simp [A_inv]

/-- Partial protection permits a commuting action outside the entire old subgroup. -/
theorem tau_not_mem_oldSubgroup : tau ∉ oldSubgroup := by
  intro member
  rcases member with trivial | old
  · exact tau_ne_one trivial
  · exact tau_ne_A old

/-- The same nontrivial transport preserves every action in the old library. -/
theorem tau_preserves_oldSubgroup {action : Equiv.Perm (Fin 4)}
    (old : action ∈ oldSubgroup) : Intertwines tau action action := by
  rcases old with rfl | rfl
  · intro state
    rfl
  · intro state
    have equality : A * tau = tau * A := A_commutes_tau
    exact congrArg (fun operation : Equiv.Perm (Fin 4) => operation state) equality

end Monodromy.Algebra

/-!
# The discrete contract of protected growth

Geometry must establish the hypotheses below.  This file proves their consequences
for finite executable words and task interfaces; it does not formalize a Rouché
certificate or assert that an arbitrary structural edit satisfies the contract.
-/


namespace Monodromy.Growth

universe u v w x y

variable {Action : Type u} {Old : Type v} {New : Type w}

/-- Execute actions in list order: the head acts first. -/
def run {State : Type v} (step : Action → State → State) : List Action → State → State
  | [], state => state
  | action :: word, state => run step word (step action state)

/-- Every old generator agrees with its grown realization under one state map. -/
def Intertwines (embed : Old → New)
    (oldStep : Action → Old → Old) (newStep : Action → New → New) : Prop :=
  ∀ action state, newStep action (embed state) = embed (oldStep action state)

/-- Generator preservation implies preservation of every finite old program. -/
theorem run_intertwines
    {embed : Old → New} {oldStep : Action → Old → Old}
    {newStep : Action → New → New}
    (preserves : Intertwines embed oldStep newStep)
    (word : List Action) (state : Old) :
    run newStep word (embed state) = embed (run oldStep word state) := by
  induction word generalizing state with
  | nil => rfl
  | cons action word ih =>
      change run newStep word (newStep action (embed state)) =
        embed (run oldStep word (oldStep action state))
      rw [preserves action state]
      exact ih (oldStep action state)

/-- A new operation reaching a fresh state cannot equal any old executable word. -/
theorem fresh_action_not_old_word
    {embed : Old → New} {oldStep : Action → Old → Old}
    {newStep : Action → New → New}
    (preserves : Intertwines embed oldStep newStep)
    (newAction : New → New) (state : Old) (fresh : New)
    (outside : ∀ old, embed old ≠ fresh)
    (reaches : newAction (embed state) = fresh)
    (word : List Action) :
    run newStep word (embed state) ≠ newAction (embed state) := by
  intro equal
  apply outside (run oldStep word state)
  calc
    embed (run oldStep word state) = run newStep word (embed state) :=
      (run_intertwines preserves word state).symm
    _ = newAction (embed state) := equal
    _ = fresh := reaches

/-- A relation closed under old token transitions is closed under their words. -/
theorem run_relation
    {oldStep : Action → Old → Old} {newStep : Action → New → New}
    (relation : Old → New → Prop)
    (closed : ∀ action old new, relation old new →
      relation (oldStep action old) (newStep action new)) :
    ∀ word old new, relation old new →
      relation (run oldStep word old) (run newStep word new) := by
  intro word
  induction word with
  | nil =>
      intro old new related
      exact related
  | cons action word ih =>
      intro old new related
      exact ih (oldStep action old) (newStep action new)
        (closed action old new related)

/-- Task retention additionally needs related encodings and agreeing readouts. -/
theorem task_retention
    {Input : Type x} {Output : Type y}
    {oldStep : Action → Old → Old} {newStep : Action → New → New}
    (relation : Old → New → Prop)
    (closed : ∀ action old new, relation old new →
      relation (oldStep action old) (newStep action new))
    (oldEncode : Input → Old) (newEncode : Input → New)
    (oldRead : Old → Output) (newRead : New → Output)
    (encodings : ∀ input, relation (oldEncode input) (newEncode input))
    (readouts : ∀ old new, relation old new → newRead new = oldRead old)
    (word : List Action) (input : Input) :
    newRead (run newStep word (newEncode input)) =
      oldRead (run oldStep word (oldEncode input)) := by
  exact readouts _ _
    (run_relation relation closed word _ _ (encodings input))

end Monodromy.Growth
