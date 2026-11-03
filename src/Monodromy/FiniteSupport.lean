module

public import Mathlib.Computability.TuringMachine.PostTuringMachine
public import Mathlib.Data.Fintype.Sets

/-!
# Finite control from a supported transition table

A finite support includes the initial label and every reachable transition
target. Restricting to that pointed finite carrier preserves the entire
configuration and execution, while leaving the tape alphabet unchanged.
-/

@[expose] public section

namespace Monodromy.FiniteSupport

open Turing

variable {Γ Q : Type*} [Inhabited Γ] [Inhabited Q]

/-- A finite, transition-closed collection of control labels. -/
structure Support (source : TM0.Machine Γ Q) where
  labels : Finset Q
  closed : TM0.Supports source (labels : Set Q)

namespace Support

variable {source : TM0.Machine Γ Q} (support : Support source)

/-- The finite control retains the source's distinguished initial label. -/
def Control : Type _ := {label : Q // label ∈ support.labels}

instance : Fintype support.Control := by unfold Control; infer_instance

instance : Inhabited support.Control := ⟨⟨default, support.closed.1⟩⟩

/-- Each transition target is already certified to belong to the finite control. -/
def restrict : TM0.Machine Γ support.Control := fun label symbol =>
  match transition : source label.val symbol with
  | none => none
  | some (target, instruction) =>
      some (⟨target, support.closed.2 transition label.property⟩, instruction)

/-- Forget only the finite-support certificate; the complete tape is retained. -/
def embed (configuration : TM0.Cfg Γ support.Control) : TM0.Cfg Γ Q :=
  ⟨configuration.q.val, configuration.Tape⟩

theorem embed_injective : Function.Injective support.embed := by
  intro first second same
  have labels : first.q = second.q := Subtype.ext (congrArg (fun c : TM0.Cfg Γ Q => c.q) same)
  have tapes : first.Tape = second.Tape := congrArg (fun c : TM0.Cfg Γ Q => c.Tape) same
  cases first
  cases second
  cases labels
  cases tapes
  rfl

omit [Inhabited Γ] in
/-- Forgetting the target certificate recovers the original fixed table entry. -/
theorem restrict_value (label : support.Control) (symbol : Γ) :
    (support.restrict label symbol).map (fun entry => (entry.1.val, entry.2)) = source label.val symbol := by
  unfold restrict
  split <;> simp_all

/-- Restriction preserves one complete transition, including halt. -/
theorem step_embed (configuration : TM0.Cfg Γ support.Control) :
    (TM0.step support.restrict configuration).map support.embed =
      TM0.step source (support.embed configuration) := by
  rcases configuration with ⟨label, tape⟩
  change ((support.restrict label tape.head).map _).map support.embed =
    (source label.val tape.head).map _
  rw [← support.restrict_value label tape.head, Option.map_map, Option.map_map]
  rfl

/-- Embedding is a refinement on all finite-control configurations. -/
theorem respects : StateTransition.Respects (TM0.step support.restrict) (TM0.step source)
    (fun first second => support.embed first = second) := by
  apply StateTransition.fun_respects.mpr
  intro configuration
  cases result : TM0.step support.restrict configuration with
  | none =>
      change TM0.step source (support.embed configuration) = none
      simp [← support.step_embed, result]
  | some successor =>
      apply Relation.TransGen.single
      simp [← support.step_embed, result]

/-- Restriction preserves the entire partial execution and final configuration. -/
theorem eval_embed (configuration : TM0.Cfg Γ support.Control) :
    StateTransition.eval (TM0.step source) (support.embed configuration) =
      support.embed <$> StateTransition.eval (TM0.step support.restrict) configuration :=
  StateTransition.tr_eval' (TM0.step support.restrict) (TM0.step source) support.embed
    support.respects configuration

theorem halting_iff (configuration : TM0.Cfg Γ support.Control) :
    (StateTransition.eval (TM0.step support.restrict) configuration).Dom ↔
      (StateTransition.eval (TM0.step source) (support.embed configuration)).Dom := by
  rw [support.eval_embed]
  rfl

theorem divergence_iff (configuration : TM0.Cfg Γ support.Control) :
    ¬ (StateTransition.eval (TM0.step support.restrict) configuration).Dom ↔
      ¬ (StateTransition.eval (TM0.step source) (support.embed configuration)).Dom :=
  not_congr (support.halting_iff configuration)

/-- Input initialization uses the same blank, label, and full tape. -/
theorem embed_init (input : List Γ) :
    support.embed (TM0.init input) = TM0.init input := rfl

/-- The standard TM0 output partial function is unchanged on every input. -/
theorem eval_input (input : List Γ) : TM0.eval support.restrict input = TM0.eval source input := by
  unfold TM0.eval
  rw [← support.embed_init input, support.eval_embed]
  rfl

end Support

end Monodromy.FiniteSupport
