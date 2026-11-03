module

public import Monodromy.Algebra
public import Mathlib.Computability.DFA
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Set.Finite.Range
import Mathlib.GroupTheory.OrderOfElement

/-!
# Finite persistent memory

At returning instruction boundaries, a fixed finite fiber is a finite
state space. This includes feedback paths selected by the current state.
The external instruction word is input, rather than additional memory.
-/

@[expose] public section

namespace Monodromy.Finite

variable {Action State : Type}

/-- Observe a computation by a set of accepting memory states. -/
def automaton (step : Action → State → State) (initial : State) (accept : Set State) :
    DFA Action State where
  step state action := step action state
  start := initial
  accept := accept

theorem eval_eq_run (step : Action → State → State) (initial : State) (accept : Set State)
    (program : List Action) (state : State) :
    (automaton step initial accept).evalFrom state program = Growth.run step program state := by
  induction program generalizing state with
  | nil => rfl
  | cons action rest ih => exact ih (step action state)

/-- Finite persistent memory recognizes a regular language of instruction words. -/
theorem language_regular [Fintype State] (step : Action → State → State)
    (initial : State) (accept : Set State) :
    Language.IsRegular {program | Growth.run step program initial ∈ accept} := by
  refine ⟨State, inferInstance, automaton step initial accept, ?_⟩
  ext program
  exact iff_of_eq (congrArg (fun state => state ∈ accept)
    (eval_eq_run step initial accept program initial))

/-- Every program acts through one of finitely many state transformations. -/
theorem finite_semantics [Finite State] (execute : List Action → State → State) :
    (Set.range execute).Finite := Set.toFinite _

/-- Faithful encodings of infinitely many configurations need infinite retained state. -/
theorem no_faithful_encoding {Configuration : Type} [Finite State] [Infinite Configuration]
    (encode : Configuration → State) : ¬ Function.Injective encode :=
  not_injective_infinite_finite encode

/-- The readout depends only on retained state, rather than an external transcript. -/
theorem no_exact_readout [Finite State] (encode : ℕ → State) (read : State → ℕ) :
    ¬ ∀ n, read (encode n) = n := by
  intro h
  exact no_faithful_encoding encode (Function.LeftInverse.injective h)

theorem no_exact_counter [Finite State] (step : State → State) (start : State)
    (read : State → ℕ) : ¬ ∀ n, read ((step^[n]) start) = n :=
  no_exact_readout (fun n => (step^[n]) start) read

/-- A fixed reversible action has a positive period common to every retained state. -/
theorem reversible_period [Finite State] (step : Equiv.Perm State) :
    ∃ period : ℕ, 0 < period ∧ ∀ (n : ℕ) (state : State),
      (step ^ (n + period)) state = (step ^ n) state := by
  obtain ⟨period, positive, returns⟩ := (isOfFinOrder_of_finite step).exists_pow_eq_one
  refine ⟨period, positive, ?_⟩
  intro n state
  rw [pow_add, returns, mul_one]

end Monodromy.Finite
