module

public import Mathlib.Computability.StateTransition

/-! Standard counter-machine semantics used as a refinement target. -/

@[expose] public section

namespace Monodromy.Counter

inductive Instruction (n m : ℕ)
  | inc (reg : Fin n) (next : Fin m)
  | dec (reg : Fin n) (zero nonzero : Fin m)
  | halt

structure Configuration (n m : ℕ) where
  pc : Fin m
  counters : Fin n → ℕ

abbrev Program (n m : ℕ) := Fin m → Instruction n m

def step {n m : ℕ} (program : Program n m)
    (state : Configuration n m) : Option (Configuration n m) :=
  match program state.pc with
  | .inc reg next =>
      some ⟨next, Function.update state.counters reg (state.counters reg + 1)⟩
  | .dec reg zero nonzero =>
      match state.counters reg with
      | 0 => some ⟨zero, state.counters⟩
      | value + 1 => some ⟨nonzero, Function.update state.counters reg value⟩
  | .halt => none

variable {n m : ℕ} (program : Program n m) (state : Configuration n m)

theorem step_inc {reg : Fin n} {next : Fin m}
    (instruction : program state.pc = .inc reg next) :
    step program state =
      some ⟨next, Function.update state.counters reg (state.counters reg + 1)⟩ := by
  simp [step, instruction]

theorem step_dec_zero {reg : Fin n} {zero nonzero : Fin m}
    (instruction : program state.pc = .dec reg zero nonzero)
    (value : state.counters reg = 0) :
    step program state = some ⟨zero, state.counters⟩ := by
  simp [step, instruction, value]

theorem step_dec_succ {reg : Fin n} {zero nonzero : Fin m} {value : ℕ}
    (instruction : program state.pc = .dec reg zero nonzero)
    (counter : state.counters reg = value + 1) :
    step program state = some ⟨nonzero, Function.update state.counters reg value⟩ := by
  simp [step, instruction, counter]

theorem step_halt (instruction : program state.pc = .halt) :
    step program state = none := by
  simp [step, instruction]

/-- Partial evaluation retains the last state when its instruction halts. -/
def eval {n m : ℕ} (program : Program n m) : Configuration n m → Part (Configuration n m) :=
  StateTransition.eval (step program)

/-- The total return map keeps a halted configuration in place. -/
def tick {n m : ℕ} (program : Program n m) (state : Configuration n m) : Configuration n m :=
  (step program state).getD state



variable {k : ℕ}

/-- Rename every program address while retaining the registers. -/
def mapInstruction (address : Fin m → Fin k) : Instruction n m → Instruction n k
  | .inc register target => .inc register (address target)
  | .dec register zero nonzero => .dec register (address zero) (address nonzero)
  | .halt => .halt

def mapConfiguration (address : Fin m → Fin k) (state : Configuration n m) :
    Configuration n k := ⟨address state.pc, state.counters⟩

theorem mapConfiguration_injective (address : Fin m → Fin k)
    (faithful : Function.Injective address) :
    Function.Injective (mapConfiguration (n := n) address) := by
  intro first second same
  cases first
  cases second
  congr 1
  · exact faithful (congrArg Configuration.pc same)
  · exact congrArg Configuration.counters same

theorem step_map (address : Fin m → Fin k)
    (oldProgram : Program n m) (newProgram : Program n k)
    (agrees : ∀ label, newProgram (address label) = mapInstruction address (oldProgram label))
    (state : Configuration n m) :
    step newProgram (mapConfiguration address state) =
      (step oldProgram state).map (mapConfiguration address) := by
  unfold step
  simp only [mapConfiguration, agrees]
  cases instruction : oldProgram state.pc with
  | inc => rfl
  | dec register =>
      cases value : state.counters register <;> simp [mapInstruction, mapConfiguration, value]
  | halt => rfl

/-- Relocation preserves the full partial result, including divergence. -/
theorem eval_map (address : Fin m → Fin k)
    (oldProgram : Program n m) (newProgram : Program n k)
    (agrees : ∀ label, newProgram (address label) = mapInstruction address (oldProgram label))
    (state : Configuration n m) :
    eval newProgram (mapConfiguration address state) =
      mapConfiguration address <$> eval oldProgram state := by
  apply StateTransition.tr_eval' (step oldProgram) (step newProgram) (mapConfiguration address)
  intro first second same
  subst second
  cases source : step oldProgram first with
  | none => simpa [source] using step_map address oldProgram newProgram agrees first
  | some successor =>
      refine ⟨mapConfiguration address successor, rfl, Relation.TransGen.single ?_⟩
      simp [step_map address oldProgram newProgram agrees first, source]

end Monodromy.Counter
