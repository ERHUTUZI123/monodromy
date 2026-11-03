module

public import Monodromy.Machine
public import Mathlib.Data.Fintype.EquivFin

/-!
# Every finite Turing table

Pointed finite enumeration preserves the blank and initial label. Renaming
therefore connects arbitrary finite alphabet and control types to the native
radix machine, with complete configuration and partial-execution semantics.
-/

@[expose] public section

namespace Monodromy.FiniteRenaming

open Turing

section Enumeration

variable (α : Type*) [Fintype α] [Inhabited α]

/-- Enumerate any finite pointed type with its distinguished element at zero. -/
noncomputable def enumeration : α ≃ Fin (Fintype.card α) :=
  (Fintype.equivFin α).trans (Equiv.swap ((Fintype.equivFin α) default) 0)

@[simp] theorem enumeration_default : enumeration α default = 0 := by
  simp [enumeration]

noncomputable def toFin : PointedMap α (Fin (Fintype.card α)) :=
  ⟨enumeration α, enumeration_default α⟩

noncomputable def fromFin : PointedMap (Fin (Fintype.card α)) α :=
  ⟨(enumeration α).symm, by
    apply (enumeration α).injective
    simp⟩

@[simp] theorem from_toFin (value : α) : fromFin α (toFin α value) = value :=
  (enumeration α).symm_apply_apply value

@[simp] theorem to_fromFin (value : Fin (Fintype.card α)) :
    toFin α (fromFin α value) = value :=
  (enumeration α).apply_symm_apply value

end Enumeration

section Machine

variable {Γ Q : Type} [Fintype Γ] [Inhabited Γ] [Fintype Q] [Inhabited Q]

/-- Renaming preserves both the blank symbol and initial control state. -/
noncomputable def machine (source : TM0.Machine Γ Q) :
    TM0.Machine (Fin (Fintype.card Γ)) (Fin (Fintype.card Q)) :=
  source.map (toFin Γ) (fromFin Γ) (toFin Q) (fromFin Q)

noncomputable def configuration (source : TM0.Cfg Γ Q) :
    TM0.Cfg (Fin (Fintype.card Γ)) (Fin (Fintype.card Q)) :=
  source.map (toFin Γ) (toFin Q)

/-- The entire state and tape commute with one exact transition, including halt. -/
theorem step_configuration (source : TM0.Machine Γ Q) (state : TM0.Cfg Γ Q) :
    (TM0.step source state).map configuration =
      TM0.step (machine source) (configuration state) :=
  source.map_step (toFin Γ) (fromFin Γ) (toFin Q) (fromFin Q)
    (S := Set.univ) (from_toFin Γ) (fun state _ => from_toFin Q state) state (Set.mem_univ _)

theorem configuration_init (input : List Γ) :
    configuration (TM0.init input : TM0.Cfg Γ Q) = TM0.init (input.map (toFin Γ)) :=
  TM0.map_init (toFin Γ) (toFin Q) input

theorem respects (source : TM0.Machine Γ Q) :
    StateTransition.Respects (TM0.step source) (TM0.step (machine source))
      (fun first second => configuration first = second) := by
  simpa only [machine, configuration, Set.mem_univ, true_and] using
    source.map_respects (toFin Γ) (fromFin Γ) (toFin Q) (fromFin Q)
      (S := Set.univ) (TM0.univ_supports source) (from_toFin Γ)
      (fun state _ => from_toFin Q state)

theorem eval_configuration (source : TM0.Machine Γ Q) (state : TM0.Cfg Γ Q) :
    StateTransition.eval (TM0.step (machine source)) (configuration state) =
      (configuration (Γ := Γ) (Q := Q)) <$> StateTransition.eval (TM0.step source) state :=
  StateTransition.tr_eval' (TM0.step source) (TM0.step (machine source)) (configuration (Γ := Γ) (Q := Q))
    (respects source) state

end Machine

open Turing

variable {Γ Q : Type} [Fintype Γ] [Inhabited Γ] [Fintype Q] [Inhabited Q]

theorem configuration_injective : Function.Injective (configuration (Γ := Γ) (Q := Q)) := by
  have roundtrip (word : ListBlank Γ) : (word.map (toFin Γ)).map (fromFin Γ) = word := by
    apply ListBlank.ext
    intro index
    simp
  have inverse : Function.LeftInverse
      (TM0.Cfg.map (fromFin Γ) (fromFin Q)) (configuration (Γ := Γ) (Q := Q)) := by
    rintro ⟨label, symbol, left, right⟩
    simp [configuration, TM0.Cfg.map, Tape.map, roundtrip]
  exact inverse.injective

end Monodromy.FiniteRenaming

namespace Monodromy.Universality

open Turing

variable {Γ Q : Type} [Fintype Γ] [Inhabited Γ] [Fintype Q] [Inhabited Q]

def Represents (source : TM0.Cfg Γ Q)
    (memory : Machine.Memory (Fintype.card Γ) (Fintype.card Q)) : Prop :=
  Machine.Represents (FiniteRenaming.configuration source) memory

theorem source_covered (source : TM0.Cfg Γ Q) :
    ∃ memory, Represents source memory :=
  Machine.source_covered (FiniteRenaming.configuration source)

/-- A native finite analytic table simulates every finite-alphabet, finite-control TM0. -/
theorem simulatesTM0 (source : TM0.Machine Γ Q) :
    StateTransition.Respects (TM0.step source)
      (Machine.step (FiniteRenaming.machine source)) Represents := by
  intro state memory related
  have native := Machine.simulatesTM0 (FiniteRenaming.machine source)
    (show Machine.Represents (FiniteRenaming.configuration state) memory from related)
  rw [← FiniteRenaming.step_configuration source state] at native
  cases result : TM0.step source state <;> simpa [result, Represents] using native

/-- Halting and divergence are preserved for arbitrary finite alphabet and control types. -/
theorem halting_iff (source : TM0.Machine Γ Q)
    {state : TM0.Cfg Γ Q}
    {memory : Machine.Memory (Fintype.card Γ) (Fintype.card Q)}
    (related : Represents state memory) :
    (Machine.eval (FiniteRenaming.machine source) memory).Dom ↔
      (StateTransition.eval (TM0.step source) state).Dom := by
  refine (Machine.halting_iff (FiniteRenaming.machine source) related).trans ?_
  rw [FiniteRenaming.eval_configuration]
  rfl

/-- The native result represents the entire original final configuration, including its tape. -/
theorem eval_represents (source : TM0.Machine Γ Q)
    {state : TM0.Cfg Γ Q}
    {memory result : Machine.Memory (Fintype.card Γ) (Fintype.card Q)}
    (related : Represents state memory)
    (finished : result ∈ Machine.eval (FiniteRenaming.machine source) memory) :
    ∃ target, Represents target result ∧ target ∈ StateTransition.eval (TM0.step source) state := by
  obtain ⟨renamed, represented, completed⟩ :=
    Machine.eval_represents (FiniteRenaming.machine source) related finished
  rw [FiniteRenaming.eval_configuration] at completed
  obtain ⟨target, completed, same⟩ := (Part.mem_map_iff _).mp completed
  refine ⟨target, ?_, completed⟩
  change Machine.Represents (FiniteRenaming.configuration target) result
  rw [same]
  exact represented

/-- A halted configuration remains stationary when counting complete returns. -/
def tick (machine : TM0.Machine Γ Q) (state : TM0.Cfg Γ Q) : TM0.Cfg Γ Q :=
  (TM0.step machine state).getD state

theorem advance_represents (machine : TM0.Machine Γ Q)
    {state : TM0.Cfg Γ Q}
    {memory : Machine.Memory (Fintype.card Γ) (Fintype.card Q)}
    (related : Represents state memory) :
    Represents (tick machine state) (Machine.advance (FiniteRenaming.machine machine) memory) := by
  have native := Machine.advance_represents (FiniteRenaming.machine machine) related
  change Machine.Represents (FiniteRenaming.configuration (tick machine state)) _
  rw [← FiniteRenaming.step_configuration] at native
  cases result : TM0.step machine state <;> simpa [tick, result] using native

/-- One native return corresponds to one complete source transition. -/
theorem iterate_represents (machine : TM0.Machine Γ Q) (rounds : ℕ)
    {state : TM0.Cfg Γ Q}
    {memory : Machine.Memory (Fintype.card Γ) (Fintype.card Q)}
    (related : Represents state memory) :
    Represents (((tick machine)^[rounds]) state)
      (((Machine.advance (FiniteRenaming.machine machine))^[rounds]) memory) := by
  induction rounds with
  | zero => exact related
  | succ rounds previous =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact advance_represents machine previous

theorem represents_unique {first second : TM0.Cfg Γ Q}
    {memory : Machine.Memory (Fintype.card Γ) (Fintype.card Q)}
    (one : Represents first memory) (two : Represents second memory) : first = second :=
  FiniteRenaming.configuration_injective (Machine.represents_unique one two)

/-- The partial results of the source and native systems agree in both directions. -/
theorem result_iff (machine : TM0.Machine Γ Q)
    {state target : TM0.Cfg Γ Q}
    {memory : Machine.Memory (Fintype.card Γ) (Fintype.card Q)}
    (related : Represents state memory) :
    target ∈ StateTransition.eval (TM0.step machine) state ↔
      ∃ result, result ∈ Machine.eval (FiniteRenaming.machine machine) memory ∧
        Represents target result := by
  constructor
  · intro finished
    obtain ⟨result, represented, completed⟩ :=
      StateTransition.tr_eval (simulatesTM0 machine) related finished
    exact ⟨result, completed, represented⟩
  · rintro ⟨result, finished, represented⟩
    obtain ⟨other, other_representation, completed⟩ := eval_represents machine related finished
    exact represents_unique other_representation represented ▸ completed

/-- One native memory follows the entire source computation by actual continuation. -/
structure FaithfulRun (source : TM0.Machine Γ Q) (state : TM0.Cfg Γ Q)
    (memory : Machine.Memory (Fintype.card Γ) (Fintype.card Q)) : Prop where
  initial : Represents state memory
  iterations : ∀ rounds,
    Represents (((tick source)^[rounds]) state)
      (((Machine.advance (FiniteRenaming.machine source))^[rounds]) memory)
  transport : ∀ rounds i,
    Transport.transport Circle.isCoveringMap_exp
      (Machine.runPath (FiniteRenaming.machine source) rounds memory i)
      (Machine.coordinate memory i) =
      Machine.coordinate (((Machine.advance (FiniteRenaming.machine source))^[rounds]) memory) i
  halting : (Machine.eval (FiniteRenaming.machine source) memory).Dom ↔
    (StateTransition.eval (TM0.step source) state).Dom
  source_result : ∀ target, target ∈ StateTransition.eval (TM0.step source) state →
    ∃ result, Represents target result ∧
      result ∈ Machine.eval (FiniteRenaming.machine source) memory
  native_result : ∀ result, result ∈ Machine.eval (FiniteRenaming.machine source) memory →
    ∃ target, Represents target result ∧ target ∈ StateTransition.eval (TM0.step source) state
  analytic : ∀ point, AnalyticAt ℝ (Machine.next (FiniteRenaming.machine source)) point

/-- Every represented initial state has the complete simulation certificate. -/
theorem faithful_of_represents (source : TM0.Machine Γ Q)
    {state : TM0.Cfg Γ Q}
    {memory : Machine.Memory (Fintype.card Γ) (Fintype.card Q)}
    (related : Represents state memory) : FaithfulRun source state memory := by
  exact {
    initial := related
    iterations := fun rounds => iterate_represents source rounds related
    transport := fun rounds i => Machine.run_transport (FiniteRenaming.machine source) rounds memory i
    halting := halting_iff source related
    source_result := fun _ completed => StateTransition.tr_eval (simulatesTM0 source) related completed
    native_result := fun _ completed => eval_represents source related completed
    analytic := Machine.analyticAt_next (FiniteRenaming.machine source)
  }

/-- Every finite Turing machine has a full native, analytic continuation simulation. -/
theorem every_finite_machine (source : TM0.Machine Γ Q) (state : TM0.Cfg Γ Q) :
    ∃ memory, FaithfulRun source state memory := by
  obtain ⟨memory, related⟩ := source_covered state
  exact ⟨memory, faithful_of_represents source related⟩

theorem FaithfulRun.divergence {source : TM0.Machine Γ Q} {state : TM0.Cfg Γ Q}
    {memory : Machine.Memory (Fintype.card Γ) (Fintype.card Q)}
    (certificate : FaithfulRun source state memory) :
    ¬ (Machine.eval (FiniteRenaming.machine source) memory).Dom ↔
      ¬ (StateTransition.eval (TM0.step source) state).Dom :=
  not_congr certificate.halting

/-- The finite input is placed directly in native word memory. -/
noncomputable def native_input (input : List Γ) :
    Machine.Memory (Fintype.card Γ) (Fintype.card Q) :=
  Machine.init (TwoStacks.init (input.map (FiniteRenaming.toFin Γ)) :
    TwoStacks.Configuration (Fin (Fintype.card Γ)) (Fin (Fintype.card Q)))

theorem input_represents (input : List Γ) :
    Represents (TM0.init input : TM0.Cfg Γ Q) (native_input (Q := Q) input) := by
  refine ⟨TwoStacks.init (input.map (FiniteRenaming.toFin Γ)), ?_, rfl⟩
  rw [TwoStacks.decode_init, FiniteRenaming.configuration_init]

/-- Every finite input has an explicit native initialization and faithful complete execution. -/
theorem every_finite_input (source : TM0.Machine Γ Q) (input : List Γ) :
    FaithfulRun source (TM0.init input) (native_input (Q := Q) input) :=
  faithful_of_represents source (input_represents input)

end Monodromy.Universality
