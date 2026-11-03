module

public import Mathlib.Computability.TuringMachine.PostTuringMachine

/-!
# A finite-word presentation of a Turing tape

This is a reference semantics. Finite control and alphabet instances are
represented geometrically by logarithmic word memory and analytic readouts.
-/

@[expose] public section

namespace Monodromy.TwoStacks

open Turing

variable {Γ Q : Type*} [Inhabited Γ]

/-- The closest symbols are at the heads of the two finite lists. -/
structure Configuration (Γ Q : Type*) where
  q : Q
  left : List Γ
  head : Γ
  right : List Γ

def tape (configuration : Configuration Γ Q) : Tape Γ :=
  ⟨configuration.head, ListBlank.mk configuration.left, ListBlank.mk configuration.right⟩

def decode (configuration : Configuration Γ Q) : TM0.Cfg Γ Q :=
  ⟨configuration.q, tape configuration⟩

def move : Dir → Configuration Γ Q → Configuration Γ Q
  | .left, configuration =>
      ⟨configuration.q, configuration.left.tail, configuration.left.headI,
        configuration.head :: configuration.right⟩
  | .right, configuration =>
      ⟨configuration.q, configuration.head :: configuration.left,
        configuration.right.headI, configuration.right.tail⟩

def write (symbol : Γ) (configuration : Configuration Γ Q) : Configuration Γ Q :=
  { configuration with head := symbol }

theorem tape_move (direction : Dir) (configuration : Configuration Γ Q) :
    tape (move direction configuration) = (tape configuration).move direction := by
  cases direction <;> rfl

theorem tape_write (symbol : Γ) (configuration : Configuration Γ Q) :
    tape (write symbol configuration) = (tape configuration).write symbol := rfl

/-- Trailing blank conventions do not restrict the TM0 configurations represented. -/
theorem decode_surjective : Function.Surjective (decode : Configuration Γ Q → TM0.Cfg Γ Q) := by
  rintro ⟨label, symbol, left, right⟩
  refine ListBlank.induction_on left (fun left => ?_)
  refine ListBlank.induction_on right (fun right => ?_)
  exact ⟨⟨label, left, symbol, right⟩, rfl⟩


variable [Inhabited Q]

def step (machine : TM0.Machine Γ Q) (configuration : Configuration Γ Q) :
    Option (Configuration Γ Q) :=
  (machine configuration.q configuration.head).map fun (label, instruction) =>
    let current := { configuration with q := label }
    match instruction with
    | .move direction => move direction current
    | .write symbol => write symbol current

/-- Exact one-step simulation of the full TM0 state and tape, including halting. -/
theorem decode_step (machine : TM0.Machine Γ Q) (configuration : Configuration Γ Q) :
    (step machine configuration).map decode = TM0.step machine (decode configuration) := by
  unfold step TM0.step decode tape
  dsimp only
  cases transition : machine configuration.q configuration.head with
  | none => rfl
  | some instruction =>
      rcases instruction with ⟨label, instruction⟩
      cases instruction with
      | move direction => cases direction <;> rfl
      | write symbol => rfl

def init (input : List Γ) : Configuration Γ Q :=
  ⟨default, [], input.headI, input.tail⟩

theorem decode_init (input : List Γ) : decode (init input : Configuration Γ Q) = TM0.init input := rfl


/-- Every stack transition and its halt state are respected at the full TM0 configuration level. -/
theorem decode_respects (machine : TM0.Machine Γ Q) :
    StateTransition.Respects (step machine) (TM0.step machine)
      (fun source target => decode source = target) := by
  apply StateTransition.fun_respects.mpr
  intro source
  cases result : step machine source with
  | none =>
      change TM0.step machine (decode source) = none
      rw [← decode_step, result]
      rfl
  | some target =>
      apply Relation.TransGen.single
      simp [← decode_step machine source, result]

/-- Partial execution, including divergence, agrees on the entire final state and tape. -/
theorem eval_decode (machine : TM0.Machine Γ Q) (configuration : Configuration Γ Q) :
    StateTransition.eval (TM0.step machine) (decode configuration) =
      decode <$> StateTransition.eval (step machine) configuration :=
  StateTransition.tr_eval' (step machine) (TM0.step machine) decode
    (decode_respects machine) configuration

end Monodromy.TwoStacks
