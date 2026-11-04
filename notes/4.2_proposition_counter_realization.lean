module

public import Mathlib.Computability.StateTransition
public import Monodromy.Continuation
public import Monodromy.Tape
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Logic.Function.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Tactic.FinCases

/-!
# Counter machines and native continuation

The standard finite counter semantics is retained. A three-phase finite
compiler realizes each two-counter step by two actual geometric returns;
the faithful configuration encoding preserves complete partial execution.

Classical finite counter macros and prime coding compile an entire finite
Turing table through three source registers to the same two-counter target.
Every arithmetic loop has a separate finite control region, with marked
source entries and no intermediate return boundary.
-/

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

noncomputable section

namespace Monodromy.CounterContinuation

open CoupledContinuation

/-- Three finite program phases share the existing upper control coordinate. -/
def label {m : ℕ} (position : Fin m) (phase : Fin 3) : ℤ :=
  (finProdFinEquiv (position, phase)).val

theorem label_eq {m : ℕ} (position : Fin m) (phase : Fin 3) :
    label position phase = (phase.val : ℤ) + 3 * (position.val : ℤ) := by
  simp [label, finProdFinEquiv]

def memoryGate (register : Fin 2) : Gate := if register = 0 then .left else .right

def zeroGate (register : Fin 2) : Gate := if register = 0 then .zeroLeft else .zeroRight

def instructionWord {m : ℕ} (program : Counter.Program 2 m) (position : Fin m) (phase : Fin 3) : Word :=
  match program position with
  | .halt => []
  | .inc register target =>
      if phase = 0 then Word.control 1
      else if phase = 1 then
        Word.atom (memoryGate register) ++ Word.control (label target 0 - label position 1)
      else []
  | .dec register zero nonzero =>
      if phase = 0 then Word.control 1 ++ Word.atom (zeroGate register)
      else if phase = 1 then
        Word.atom (memoryGate register) true ++ Word.control (label nonzero 0 - label position 1)
      else Word.control (label zero 0 - label position 2)

def instructionStop {m : ℕ} (instruction : Counter.Instruction 2 m) : Bool :=
  match instruction with | .halt => true | _ => false

def stopping {m : ℕ} (program : Counter.Program 2 m) (position : Fin m) (phase : Fin 3) : Bool :=
  if phase = 0 then instructionStop (program position) else false

def wordTable {m : ℕ} (program : Counter.Program 2 m) (index : Fin (m * 3)) : Word :=
  let address := finProdFinEquiv.symm index
  instructionWord program address.1 address.2

def stopTable {m : ℕ} (program : Counter.Program 2 m) (index : Fin (m * 3)) : Bool :=
  let address := finProdFinEquiv.symm index
  stopping program address.1 address.2

def compile {m : ℕ} (program : Counter.Program 2 m) : CoupledContinuation.Program (m * 3) :=
  ⟨wordTable program, stopTable program⟩

def encode {m : ℕ} (state : Counter.Configuration 2 m) : Memory :=
  prepare (state.counters 0 : ℤ) (state.counters 1 : ℤ) (label state.pc 0)

theorem compile_table_address {m : ℕ} (program : Counter.Program 2 m)
    (position : Fin m) (phase : Fin 3) :
    (compile program).table (finProdFinEquiv (position, phase)) = instructionWord program position phase := by
  simp [compile, wordTable]

theorem compile_stop_address {m : ℕ} (program : Counter.Program 2 m)
    (position : Fin m) (phase : Fin 3) :
    (compile program).stop (finProdFinEquiv (position, phase)) = stopping program position phase := by
  simp [compile, stopTable]

variable {m : ℕ} [NeZero m]

theorem advance_at (program : Counter.Program 2 m) (left right : ℤ)
    (position : Fin m) (phase : Fin 3) :
    (compile program).advance (prepare left right (label position phase)) =
      execute (Word.driver (instructionWord program position phase))
        (prepare left right (label position phase)) := by
  have run := CoupledContinuation.Program.advance_prepare (compile program) left right 0
    (finProdFinEquiv (position, phase))
  simpa only [mul_zero, zero_add, compile_table_address, label] using run

theorem step_at (program : Counter.Program 2 m) (left right : ℤ)
    (position : Fin m) (phase : Fin 3) :
    (compile program).step (prepare left right (label position phase)) =
      if stopping program position phase then none else
        some (execute (Word.driver (instructionWord program position phase))
          (prepare left right (label position phase))) := by
  have run := CoupledContinuation.Program.step_prepare (compile program) left right 0
    (finProdFinEquiv (position, phase))
  simpa only [mul_zero, zero_add, compile_table_address, compile_stop_address, label] using run

end Monodromy.CounterContinuation

namespace Monodromy.CounterContinuation

open CoupledContinuation

variable {m : ℕ} [NeZero m]

theorem advance_inc_first (program : Counter.Program 2 m) (position target : Fin m)
    (register : Fin 2) (instruction : program position = .inc register target) (left right : ℤ) :
    (compile program).advance (prepare left right (label position 0)) =
      prepare left right (label position 1) := by
  rw [advance_at]
  simp [instructionWord, instruction]
  rw [execute_control_word]
  congr 1
  simp [label_eq]
  omega

theorem advance_inc_second (program : Counter.Program 2 m) (position target : Fin m)
    (register : Fin 2) (instruction : program position = .inc register target) (left right : ℤ) :
    (compile program).advance (prepare left right (label position 1)) =
      prepare (left + if register = 0 then 1 else 0) (right + if register = 1 then 1 else 0)
        (label target 0) := by
  rw [advance_at]
  simp [instructionWord, instruction]
  rw [execute_word_append, execute_word_atom]
  fin_cases register
  · change execute (Word.driver (Word.control _)) (execute A_left _) = _
    rw [execute_A_left, execute_control_word]
    congr 1 <;> simp
  · change execute (Word.driver (Word.control _)) (execute A_right _) = _
    rw [execute_A_right, execute_control_word]
    congr 1 <;> simp

theorem advance_dec_first (program : Counter.Program 2 m) (position zero nonzero : Fin m)
    (register : Fin 2) (instruction : program position = .dec register zero nonzero) (left right : ℤ) :
    (compile program).advance (prepare left right (label position 0)) =
      prepare left right (label position 1 + if (![left, right] register) = 0 then 1 else 0) := by
  rw [advance_at]
  simp [instructionWord, instruction]
  rw [execute_word_append, execute_control_word, execute_word_atom]
  fin_cases register
  · change execute B_left _ = _
    rw [execute_B_left]
    congr 1
    simp [label_eq]
    omega
  · change execute B_right _ = _
    rw [execute_B_right]
    congr 1
    simp [label_eq]
    omega

theorem advance_dec_positive (program : Counter.Program 2 m) (position zero nonzero : Fin m)
    (register : Fin 2) (instruction : program position = .dec register zero nonzero) (left right : ℤ) :
    (compile program).advance (prepare left right (label position 1)) =
      prepare (left - if register = 0 then 1 else 0) (right - if register = 1 then 1 else 0)
        (label nonzero 0) := by
  rw [advance_at]
  simp [instructionWord, instruction]
  rw [execute_word_append, execute_word_atom]
  fin_cases register
  · change execute (Word.driver (Word.control _)) (execute A_left.reverse _) = _
    rw [execute_A_left_reverse, execute_control_word]
    congr 1 <;> simp
  · change execute (Word.driver (Word.control _)) (execute A_right.reverse _) = _
    rw [execute_A_right_reverse, execute_control_word]
    congr 1 <;> simp

theorem advance_dec_zero (program : Counter.Program 2 m) (position zero nonzero : Fin m)
    (register : Fin 2) (instruction : program position = .dec register zero nonzero) (left right : ℤ) :
    (compile program).advance (prepare left right (label position 2)) =
      prepare left right (label zero 0) := by
  rw [advance_at]
  simp [instructionWord, instruction]
  rw [execute_control_word]
  congr 1
  omega

theorem step_running_at (program : Counter.Program 2 m) (position : Fin m) (phase : Fin 3)
    (running : stopping program position phase = false) (left right : ℤ) :
    (compile program).step (prepare left right (label position phase)) =
      some ((compile program).advance (prepare left right (label position phase))) := by
  rw [step_at, running]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [advance_at]

theorem step_phase_one (program : Counter.Program 2 m) (position : Fin m) (left right : ℤ) :
    (compile program).step (prepare left right (label position 1)) =
      some ((compile program).advance (prepare left right (label position 1))) := by
  apply step_running_at
  simp [stopping]

theorem step_phase_two (program : Counter.Program 2 m) (position : Fin m) (left right : ℤ) :
    (compile program).step (prepare left right (label position 2)) =
      some ((compile program).advance (prepare left right (label position 2))) := by
  apply step_running_at
  simp [stopping]

end Monodromy.CounterContinuation

namespace Monodromy.CounterContinuation

open CoupledContinuation

variable {m : ℕ}

/-- The three retained roots preserve the whole finite-control, two-counter configuration. -/
theorem encode_injective : Function.Injective (@encode m) := by
  intro first second same
  have labels : (((first.counters 0 : ℤ), (first.counters 1 : ℤ)), label first.pc 0) =
      (((second.counters 0 : ℤ), (second.counters 1 : ℤ)), label second.pc 0) :=
    CoupledContinuation.prepare_injective same
  have positions : first.pc = second.pc := by
    apply Fin.ext
    have control := congrArg Prod.snd labels
    simp only [label_eq, Fin.val_zero, Nat.cast_zero, zero_add] at control
    exact_mod_cast (show (first.pc.val : ℤ) = (second.pc.val : ℤ) by omega)
  have lefts : first.counters 0 = second.counters 0 := by
    have casted : (first.counters 0 : ℤ) = (second.counters 0 : ℤ) :=
      congrArg (fun value : (ℤ × ℤ) × ℤ => value.1.1) labels
    exact_mod_cast casted
  have rights : first.counters 1 = second.counters 1 := by
    have casted : (first.counters 1 : ℤ) = (second.counters 1 : ℤ) :=
      congrArg (fun value : (ℤ × ℤ) × ℤ => value.1.2) labels
    exact_mod_cast casted
  have registers : first.counters = second.counters := by
    funext register
    fin_cases register <;> assumption
  cases first
  cases second
  cases positions
  cases registers
  rfl

variable [NeZero m]

/-- A source halt is read by the native finite-root stopping signal. -/
theorem step_halt (program : Counter.Program 2 m) (state : Counter.Configuration 2 m)
    (instruction : program state.pc = .halt) : (compile program).step (encode state) = none := by
  unfold encode
  rw [step_at]
  simp [stopping, instructionStop, instruction]

/-- Every live source step is realized by exactly two nonempty native returns. -/
theorem two_returns (program : Counter.Program 2 m)
    (state result : Counter.Configuration 2 m) (source_step : Counter.step program state = some result) :
    ∃ middle : Memory,
      (compile program).step (encode state) = some middle ∧
      (compile program).step middle = some (encode result) := by
  cases instruction : program state.pc with
  | halt => simp [Counter.step, instruction] at source_step
  | inc register target =>
      have result_eq : result =
          ⟨target, Function.update state.counters register (state.counters register + 1)⟩ := by
        simpa [Counter.step, instruction] using source_step.symm
      subst result
      have running : stopping program state.pc 0 = false := by
        simp [stopping, instructionStop, instruction]
      refine ⟨prepare (state.counters 0 : ℤ) (state.counters 1 : ℤ) (label state.pc 1), ?_, ?_⟩
      · change (compile program).step
          (prepare (state.counters 0 : ℤ) (state.counters 1 : ℤ) (label state.pc 0)) = _
        rw [step_running_at program state.pc 0 running,
          advance_inc_first program state.pc target register instruction]
      · rw [step_phase_one, advance_inc_second program state.pc target register instruction]
        apply congrArg some
        unfold encode
        fin_cases register <;> simp [Function.update]
  | dec register zero nonzero =>
      have running : stopping program state.pc 0 = false := by
        simp [stopping, instructionStop, instruction]
      cases counter : state.counters register with
      | zero =>
          have result_eq : result = ⟨zero, state.counters⟩ := by
            simpa [Counter.step, instruction, counter] using source_step.symm
          subst result
          have zero_value : (![((state.counters 0 : ℤ)), ((state.counters 1 : ℤ))] register) = 0 := by
            have casted := congrArg (fun value : ℕ => (value : ℤ)) counter
            fin_cases register <;> simpa using casted
          have first_return :
              (compile program).advance
                (prepare (state.counters 0 : ℤ) (state.counters 1 : ℤ) (label state.pc 0)) =
              prepare (state.counters 0 : ℤ) (state.counters 1 : ℤ) (label state.pc 2) := by
            rw [advance_dec_first program state.pc zero nonzero register instruction, zero_value]
            simp only [ite_true]
            congr 1
            simp [label_eq]
            omega
          refine ⟨prepare (state.counters 0 : ℤ) (state.counters 1 : ℤ) (label state.pc 2), ?_, ?_⟩
          · change (compile program).step
              (prepare (state.counters 0 : ℤ) (state.counters 1 : ℤ) (label state.pc 0)) = _
            rw [step_running_at program state.pc 0 running, first_return]
          · rw [step_phase_two, advance_dec_zero program state.pc zero nonzero register instruction]
            rfl
      | succ value =>
          have result_eq : result = ⟨nonzero, Function.update state.counters register value⟩ := by
            simpa [Counter.step, instruction, counter] using source_step.symm
          subst result
          have nonzero_value : (![((state.counters 0 : ℤ)), ((state.counters 1 : ℤ))] register) ≠ 0 := by
            have casted := congrArg (fun value : ℕ => (value : ℤ)) counter
            have positive : (![((state.counters 0 : ℤ)), ((state.counters 1 : ℤ))] register) = (value : ℤ) + 1 := by
              fin_cases register <;> simpa using casted
            omega
          have first_return :
              (compile program).advance
                (prepare (state.counters 0 : ℤ) (state.counters 1 : ℤ) (label state.pc 0)) =
              prepare (state.counters 0 : ℤ) (state.counters 1 : ℤ) (label state.pc 1) := by
            simpa only [ite_eq_right nonzero_value, add_zero] using
              advance_dec_first program state.pc zero nonzero register instruction
                (state.counters 0 : ℤ) (state.counters 1 : ℤ)
          refine ⟨prepare (state.counters 0 : ℤ) (state.counters 1 : ℤ) (label state.pc 1), ?_, ?_⟩
          · change (compile program).step
              (prepare (state.counters 0 : ℤ) (state.counters 1 : ℤ) (label state.pc 0)) = _
            rw [step_running_at program state.pc 0 running, first_return]
          · rw [step_phase_one, advance_dec_positive program state.pc zero nonzero register instruction]
            apply congrArg some
            unfold encode
            fin_cases register <;> simp_all [Function.update]

/-- The geometric program refines the standard two-counter transition system. -/
theorem simulates (program : Counter.Program 2 m) :
    StateTransition.Respects (Counter.step program) (compile program).step
      (fun first second => encode first = second) := by
  apply StateTransition.fun_respects.mpr
  intro state
  cases source_step : Counter.step program state with
  | none =>
      change (compile program).step (encode state) = none
      cases instruction : program state.pc with
      | halt => exact step_halt program state instruction
      | inc register target => simp [Counter.step, instruction] at source_step
      | dec register zero nonzero =>
          cases counter : state.counters register <;>
            simp [Counter.step, instruction, counter] at source_step
  | some result =>
      change StateTransition.Reaches₁ (compile program).step (encode state) (encode result)
      obtain ⟨middle, first_return, second_return⟩ := two_returns program state result source_step
      have first_reach : StateTransition.Reaches₁ (compile program).step (encode state) middle :=
        Relation.TransGen.single first_return
      exact first_reach.tail second_return

/-- Complete results, halting, and divergence agree through the faithful native encoding. -/
theorem eval_encode (program : Counter.Program 2 m) (state : Counter.Configuration 2 m) :
    (compile program).eval (encode state) = encode <$> Counter.eval program state :=
  StateTransition.tr_eval' (Counter.step program) (compile program).step encode (simulates program) state

theorem halting_iff (program : Counter.Program 2 m) (state : Counter.Configuration 2 m) :
    ((compile program).eval (encode state)).Dom ↔ (Counter.eval program state).Dom := by
  have same := congrArg Part.Dom (eval_encode program state)
  exact same.to_iff

theorem divergence_iff (program : Counter.Program 2 m) (state : Counter.Configuration 2 m) :
    ¬ ((compile program).eval (encode state)).Dom ↔ ¬ (Counter.eval program state).Dom :=
  not_congr (halting_iff program state)

end Monodromy.CounterContinuation


namespace Monodromy.CounterContinuation

variable {m : ℕ} [NeZero m]

/-- Two actual native returns commute with one complete source transition, including halt. -/
theorem step_bind_step_encode (program : Counter.Program 2 m) (state : Counter.Configuration 2 m) :
    ((compile program).step (encode state)).bind (compile program).step =
      (Counter.step program state).map encode := by
  cases source_step : Counter.step program state with
  | none =>
      have stopped := StateTransition.fun_respects.mp (simulates program) (a₁ := state)
      rw [source_step] at stopped
      change (compile program).step (encode state) = none at stopped
      rw [stopped]
      rfl
  | some result =>
      obtain ⟨middle, first_return, second_return⟩ := two_returns program state result source_step
      rw [first_return]
      exact second_return

end Monodromy.CounterContinuation

namespace Monodromy.CounterContinuation

open CoupledContinuation

/-- A source boundary is observed from the actual cubic control root alone. -/
def SourceBoundary (state : Memory) : Prop := controlRoot 3 state = 1

theorem controlRoot_label {m : ℕ} (position : Fin m) (phase : Fin 3) (left right : ℤ) :
    controlRoot 3 (prepare left right (label position phase)) = (Radix.omega 3 phase : ℂ) := by
  rw [controlRoot_prepare, label_eq]
  have reorder : (phase.val : ℤ) + 3 * (position.val : ℤ) =
      (3 : ℤ) * (position.val : ℤ) + phase.val := by omega
  rw [reorder]
  exact congrArg (fun root : Circle => (root : ℂ))
    (Radix.readRoot_digit 3 (position.val : ℤ) phase)

theorem sourceBoundary_label_iff {m : ℕ} (position : Fin m) (phase : Fin 3)
    (left right : ℤ) :
    SourceBoundary (prepare left right (label position phase)) ↔ phase = 0 := by
  have root_zero : (Radix.omega 3 (0 : Fin 3) : ℂ) = 1 := by simp [Radix.omega]
  constructor
  · intro boundary
    apply Radix.omega_injective 3
    apply Subtype.ext
    exact (controlRoot_label position phase left right).symm.trans (boundary.trans root_zero.symm)
  · rintro rfl
    exact (controlRoot_label position 0 left right).trans root_zero

@[simp] theorem sourceBoundary_encode {m : ℕ} (state : Counter.Configuration 2 m) :
    SourceBoundary (encode state) :=
  (sourceBoundary_label_iff state.pc 0 _ _).mpr rfl

variable {m : ℕ} [NeZero m]

/-- The first actual native return moves every live source state to phase one or two. -/
theorem advance_live_phase (program : Counter.Program 2 m) (state : Counter.Configuration 2 m)
    (live : program state.pc ≠ .halt) :
    (compile program).advance (encode state) =
      prepare (state.counters 0 : ℤ) (state.counters 1 : ℤ) (label state.pc 1) ∨
    (compile program).advance (encode state) =
      prepare (state.counters 0 : ℤ) (state.counters 1 : ℤ) (label state.pc 2) := by
  unfold encode
  cases instruction : program state.pc with
  | halt => exact False.elim (live instruction)
  | inc register target =>
      exact Or.inl (advance_inc_first program state.pc target register instruction _ _)
  | dec register zero nonzero =>
      rw [advance_dec_first program state.pc zero nonzero register instruction]
      by_cases zero_value : (![(state.counters 0 : ℤ), (state.counters 1 : ℤ)] register) = 0
      · right
        rw [ite_eq_left zero_value]
        congr 1
        simp only [label_eq]
        omega
      · left
        simp only [ite_eq_right zero_value, add_zero]

theorem advance_live_not_boundary (program : Counter.Program 2 m)
    (state : Counter.Configuration 2 m) (live : program state.pc ≠ .halt) :
    ¬ SourceBoundary ((compile program).advance (encode state)) := by
  rcases advance_live_phase program state live with first | second
  · rw [first, sourceBoundary_label_iff]
    decide
  · rw [second, sourceBoundary_label_iff]
    decide

/-- Exactly two actual native returns separate consecutive marked source states. -/
theorem two_returns_with_boundary (program : Counter.Program 2 m)
    (state result : Counter.Configuration 2 m) (source_step : Counter.step program state = some result) :
    ∃ middle : Memory,
      SourceBoundary (encode state) ∧
      (compile program).step (encode state) = some middle ∧
      ¬ SourceBoundary middle ∧
      (compile program).step middle = some (encode result) ∧
      SourceBoundary (encode result) := by
  obtain ⟨middle, first, second⟩ := two_returns program state result source_step
  have live : program state.pc ≠ .halt := by
    intro halted
    simp [Counter.step, halted] at source_step
  have running : stopping program state.pc 0 = false := by
    cases instruction : program state.pc <;> simp [stopping, instructionStop, instruction] at live ⊢
  have actual_first : (compile program).step (encode state) =
      some ((compile program).advance (encode state)) :=
    step_running_at program state.pc 0 running _ _
  have identifies : middle = (compile program).advance (encode state) :=
    Option.some.inj (first.symm.trans actual_first)
  refine ⟨middle, sourceBoundary_encode state, first, ?_, second, sourceBoundary_encode result⟩
  rw [identifies]
  exact advance_live_not_boundary program state live

end Monodromy.CounterContinuation

namespace Monodromy.PrimeCode

/-- A classical proof-side encoding of three source registers, using fixed distinct primes. -/
def prime (index : Fin 3) : ℕ := if index = 0 then 2 else if index = 1 then 3 else 5

def encode (registers : Fin 3 → ℕ) : ℕ :=
  2 ^ registers 0 * 3 ^ registers 1 * 5 ^ registers 2

theorem prime_prime (index : Fin 3) : (prime index).Prime := by
  fin_cases index <;> norm_num [prime] <;> decide

theorem encode_positive (registers : Fin 3 → ℕ) : 0 < encode registers := by
  unfold encode
  positivity

/-- Prime valuations recover each source register exactly. -/
theorem factorization_encode (registers : Fin 3 → ℕ) (index : Fin 3) :
    (encode registers).factorization (prime index) = registers index := by
  unfold encode
  rw [Nat.factorization_mul
      (mul_ne_zero (pow_ne_zero _ (by decide)) (pow_ne_zero _ (by decide)))
      (pow_ne_zero _ (by decide)),
    Nat.factorization_mul (pow_ne_zero _ (by decide)) (pow_ne_zero _ (by decide)),
    (show Nat.Prime 2 by decide).factorization_pow,
    (show Nat.Prime 3 by decide).factorization_pow,
    (show Nat.Prime 5 by decide).factorization_pow]
  fin_cases index <;> simp [prime]

def decode (code : ℕ) : Fin 3 → ℕ := fun index => code.factorization (prime index)

theorem decode_encode : Function.LeftInverse decode encode := by
  intro registers
  funext index
  exact factorization_encode registers index

theorem encode_injective : Function.Injective encode := decode_encode.injective

@[simp] theorem encode_zero : encode (fun _ => 0) = 1 := by simp [encode]

/-- Incrementing a source register multiplies the single code by its fixed prime. -/
theorem encode_increment (registers : Fin 3 → ℕ) (index : Fin 3) :
    encode (Function.update registers index (registers index + 1)) = prime index * encode registers := by
  fin_cases index <;> norm_num [encode, prime, Function.update_apply, pow_add] <;> ring

/-- Divisibility is precisely the nonzero test for the corresponding source register. -/
theorem prime_dvd_encode_iff (registers : Fin 3 → ℕ) (index : Fin 3) :
    prime index ∣ encode registers ↔ registers index ≠ 0 := by
  rw [(prime_prime index).dvd_iff_one_le_factorization (encode_positive registers).ne',
    factorization_encode]
  omega

theorem register_zero_iff (registers : Fin 3 → ℕ) (index : Fin 3) :
    registers index = 0 ↔ ¬ prime index ∣ encode registers := by
  rw [prime_dvd_encode_iff]
  omega

theorem remainder_zero_iff (registers : Fin 3 → ℕ) (index : Fin 3) :
    encode registers % prime index = 0 ↔ registers index ≠ 0 := by
  rw [← Nat.dvd_iff_mod_eq_zero, prime_dvd_encode_iff]

/-- A nonzero source decrement is exact division of the positive code. -/
theorem encode_decrement (registers : Fin 3 → ℕ) (index : Fin 3)
    (nonzero : registers index ≠ 0) :
    encode (Function.update registers index (registers index - 1)) = encode registers / prime index := by
  let previous := Function.update registers index (registers index - 1)
  have restores : Function.update previous index (previous index + 1) = registers := by
    funext other
    by_cases same : other = index
    · subst other
      simp only [previous, Function.update_self]
      omega
    · simp [previous, same]
  have restores_code := encode_increment previous index
  rw [restores] at restores_code
  change encode previous = encode registers / prime index
  rw [restores_code, Nat.mul_div_cancel_left _ (prime_prime index).pos]

end Monodromy.PrimeCode

namespace Monodromy.Counter.RegisterRelocation

variable {n k m : ℕ}

def instruction (register : Fin n → Fin k) : Instruction n m → Instruction k m
  | .inc source target => .inc (register source) target
  | .dec source zero nonzero => .dec (register source) zero nonzero
  | .halt => .halt

def program (register : Fin n → Fin k) (source : Program n m) : Program k m :=
  fun address => instruction register (source address)

/-- Registers outside the image retain their arbitrary fixed background values. -/
def embed (register : Fin n → Fin k) (background : Fin k → ℕ)
    (state : Configuration n m) : Configuration k m :=
  ⟨state.pc, Function.extend register state.counters background⟩

theorem embed_read (register : Fin n → Fin k) (faithful : Function.Injective register)
    (background : Fin k → ℕ) (state : Configuration n m) (index : Fin n) :
    (embed register background state).counters (register index) = state.counters index :=
  faithful.extend_apply _ _ _

theorem embed_outside (register : Fin n → Fin k) (background : Fin k → ℕ)
    (state : Configuration n m) (index : Fin k) (outside : ∀ source, register source ≠ index) :
    (embed register background state).counters index = background index :=
  Function.extend_apply' _ _ _ (by rintro ⟨source, same⟩; exact outside source same)

/-- A register injection preserves each complete step, including the zero and halt cases. -/
theorem step_embed (register : Fin n → Fin k) (faithful : Function.Injective register)
    (background : Fin k → ℕ) (source : Program n m) (state : Configuration n m) :
    step (program register source) (embed register background state) =
      (step source state).map (embed register background) := by
  cases operation : source state.pc with
  | inc index target =>
      simp [step, program, instruction, embed, operation, faithful.extend_apply, faithful.extend_update]
  | dec index zero nonzero =>
      cases value : state.counters index <;>
        simp [step, program, instruction, embed, operation, value,
          faithful.extend_apply, faithful.extend_update]
  | halt => simp [step, program, instruction, embed, operation]

/-- The same relocation transports any finite arithmetic macro run. -/
theorem reaches_embed (register : Fin n → Fin k) (faithful : Function.Injective register)
    (background : Fin k → ℕ) (source : Program n m) {first last : Configuration n m}
    (run : StateTransition.Reaches (step source) first last) :
    StateTransition.Reaches (step (program register source))
      (embed register background first) (embed register background last) := by
  induction run with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ edge previous =>
      apply previous.tail
      have actual : step source _ = some _ := edge
      rw [step_embed register faithful background source, actual]
      rfl

/-- Partial results, halting and divergence survive register relocation exactly. -/
theorem eval_embed (register : Fin n → Fin k) (faithful : Function.Injective register)
    (background : Fin k → ℕ) (source : Program n m) (state : Configuration n m) :
    eval (program register source) (embed register background state) =
      embed register background <$> eval source state := by
  apply StateTransition.tr_eval' (step source) (step (program register source)) (embed register background)
  apply StateTransition.fun_respects.mpr
  intro current
  cases result : step source current with
  | none =>
      change step (program register source) (embed register background current) = none
      simp [step_embed register faithful background source, result]
  | some next =>
      apply Relation.TransGen.single
      simp [step_embed register faithful background source, result]

/-- Either stack and the shared third scratch register can host the same two-register macro. -/
def pairIntoThree (active : Fin 2) (index : Fin 2) : Fin 3 :=
  if index = 0 then active.castSucc else 2

theorem pairIntoThree_injective (active : Fin 2) : Function.Injective (pairIntoThree active) := by
  intro first second same
  fin_cases active <;> fin_cases first <;> fin_cases second <;>
    first | rfl | norm_num [pairIntoThree] at same

end Monodromy.Counter.RegisterRelocation

namespace Monodromy.Counter

variable {n m k : ℕ}

/-- Finite prefixes may be linked into a new program by replacing only their halt exits. -/
theorem step_map_live (address : Fin m → Fin k)
    (oldProgram : Program n m) (newProgram : Program n k)
    (agrees : ∀ label, oldProgram label ≠ .halt →
      newProgram (address label) = mapInstruction address (oldProgram label))
    {state result : Configuration n m} (running : step oldProgram state = some result) :
    step newProgram (mapConfiguration address state) = some (mapConfiguration address result) := by
  have live : oldProgram state.pc ≠ .halt := by
    intro stopped
    simp [step, stopped] at running
  have same : step newProgram (mapConfiguration address state) =
      (step oldProgram state).map (mapConfiguration address) := by
    unfold step
    simp only [mapConfiguration, agrees state.pc live]
    cases instruction : oldProgram state.pc with
    | inc => rfl
    | dec register =>
        cases value : state.counters register <;> simp [mapInstruction, mapConfiguration, value]
    | halt => rfl
  rw [running] at same
  exact same

/-- Running-row agreement preserves every finite path while leaving exits free for continuation. -/
theorem reaches_map_live (address : Fin m → Fin k)
    (oldProgram : Program n m) (newProgram : Program n k)
    (agrees : ∀ label, oldProgram label ≠ .halt →
      newProgram (address label) = mapInstruction address (oldProgram label))
    {first last : Configuration n m} (execution : StateTransition.Reaches (step oldProgram) first last) :
    StateTransition.Reaches (step newProgram)
      (mapConfiguration address first) (mapConfiguration address last) := by
  induction execution with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ running reached =>
      exact reached.tail (step_map_live address oldProgram newProgram agrees running)

end Monodromy.Counter

namespace Monodromy.CounterMultiplication

/-- Countdown cells are only finite control addresses, never another register. -/
def phase (factor remaining : ℕ) : Fin (factor + 4) :=
  ⟨remaining % (factor + 4), Nat.mod_lt _ (by omega)⟩

def transfer (factor : ℕ) : Fin (factor + 4) := ⟨factor + 1, by omega⟩
def restore (factor : ℕ) : Fin (factor + 4) := ⟨factor + 2, by omega⟩
def finish (factor : ℕ) : Fin (factor + 4) := ⟨factor + 3, by omega⟩

def program (factor : ℕ) : Counter.Program 2 (factor + 4) := fun position =>
  if position.val = 0 then .dec 0 (transfer factor) (phase factor factor)
  else if position.val ≤ factor then .inc 1 (phase factor (position.val - 1))
  else if position.val = factor + 1 then .dec 1 (finish factor) (restore factor)
  else if position.val = factor + 2 then .inc 0 (transfer factor)
  else .halt

def configuration (factor : ℕ) (position : Fin (factor + 4)) (first second : ℕ) :
    Counter.Configuration 2 (factor + 4) := ⟨position, ![first, second]⟩

@[simp] theorem phase_zero (factor : ℕ) : phase factor 0 = 0 := by
  apply Fin.ext
  simp [phase]

theorem phase_val (factor remaining : ℕ) (bound : remaining ≤ factor) :
    (phase factor remaining).val = remaining :=
  Nat.mod_eq_of_lt (by omega)

theorem program_zero (factor : ℕ) :
    program factor 0 = .dec 0 (transfer factor) (phase factor factor) := by
  simp [program]

theorem program_phase (factor remaining : ℕ) (bound : remaining < factor) :
    program factor (phase factor (remaining + 1)) = .inc 1 (phase factor remaining) := by
  have current := phase_val factor (remaining + 1) (by omega)
  have inside : remaining + 1 ≤ factor := by omega
  simp [program, current, inside]

theorem program_transfer (factor : ℕ) :
    program factor (transfer factor) = .dec 1 (finish factor) (restore factor) := by
  simp [program, transfer]

theorem program_restore (factor : ℕ) :
    program factor (restore factor) = .inc 0 (transfer factor) := by
  have outside : ¬ factor + 2 ≤ factor := by omega
  simp [program, restore, outside]

theorem program_finish (factor : ℕ) : program factor (finish factor) = .halt := by
  have outside : ¬ factor + 3 ≤ factor := by omega
  simp [program, finish, outside]

theorem step_phase (factor remaining first second : ℕ) (bound : remaining < factor) :
    Counter.step (program factor) (configuration factor (phase factor (remaining + 1)) first second) =
      some (configuration factor (phase factor remaining) first (second + 1)) := by
  rw [Counter.step_inc (program factor) _ (program_phase factor remaining bound)]
  apply congrArg some
  congr 1
  funext register
  fin_cases register <;> simp [configuration, Function.update]

theorem step_consume (factor first second : ℕ) :
    Counter.step (program factor) (configuration factor 0 (first + 1) second) =
      some (configuration factor (phase factor factor) first second) := by
  rw [Counter.step_dec_succ (program factor) _ (program_zero factor) rfl]
  apply congrArg some
  congr 1
  funext register
  fin_cases register <;> simp [configuration, Function.update]

theorem step_begin_transfer (factor second : ℕ) :
    Counter.step (program factor) (configuration factor 0 0 second) =
      some (configuration factor (transfer factor) 0 second) :=
  Counter.step_dec_zero (program factor) _ (program_zero factor) rfl

theorem step_transfer (factor first second : ℕ) :
    Counter.step (program factor) (configuration factor (transfer factor) first (second + 1)) =
      some (configuration factor (restore factor) first second) := by
  rw [Counter.step_dec_succ (program factor) _ (program_transfer factor) rfl]
  apply congrArg some
  congr 1
  funext register
  fin_cases register <;> simp [configuration, Function.update]

theorem step_restore (factor first second : ℕ) :
    Counter.step (program factor) (configuration factor (restore factor) first second) =
      some (configuration factor (transfer factor) (first + 1) second) := by
  rw [Counter.step_inc (program factor) _ (program_restore factor)]
  apply congrArg some
  congr 1
  funext register
  fin_cases register <;> simp [configuration, Function.update]

theorem step_finish (factor first : ℕ) :
    Counter.step (program factor) (configuration factor (transfer factor) first 0) =
      some (configuration factor (finish factor) first 0) :=
  Counter.step_dec_zero (program factor) _ (program_transfer factor) rfl

theorem halted (factor first second : ℕ) :
    Counter.step (program factor) (configuration factor (finish factor) first second) = none :=
  Counter.step_halt (program factor) _ (program_finish factor)

/-- Every countdown pass has a fixed finite length and retains the first register. -/
theorem increments_reach (factor remaining first second : ℕ) (bound : remaining ≤ factor) :
    StateTransition.Reaches (Counter.step (program factor))
      (configuration factor (phase factor remaining) first second)
      (configuration factor 0 first (second + remaining)) := by
  induction remaining generalizing second with
  | zero =>
      simp only [phase_zero, Nat.add_zero]
      exact Relation.ReflTransGen.refl
  | succ remaining induction_hypothesis =>
      have first_step := step_phase factor remaining first second (by omega)
      have rest := induction_hypothesis (second := second + 1) (by omega)
      have arithmetic : second + 1 + remaining = second + (remaining + 1) := by omega
      rw [arithmetic] at rest
      exact Relation.ReflTransGen.head first_step rest

/-- Consuming the first register adds exactly factor times its original value to the second. -/
theorem consume_reach (factor first second : ℕ) :
    StateTransition.Reaches (Counter.step (program factor))
      (configuration factor 0 first second)
      (configuration factor 0 0 (second + factor * first)) := by
  induction first generalizing second with
  | zero =>
      simp only [Nat.mul_zero, Nat.add_zero]
      exact Relation.ReflTransGen.refl
  | succ first induction_hypothesis =>
      have pass : StateTransition.Reaches (Counter.step (program factor))
          (configuration factor 0 (first + 1) second)
          (configuration factor 0 first (second + factor)) :=
        Relation.ReflTransGen.head (step_consume factor first second)
          (increments_reach factor factor first second (by omega))
      have rest := induction_hypothesis (second := second + factor)
      have arithmetic : second + factor + factor * first = second + factor * (first + 1) := by ring
      rw [arithmetic] at rest
      exact pass.trans rest

/-- The final loop transfers the second register into the first, leaving zero behind. -/
theorem transfer_reach (factor first second : ℕ) :
    StateTransition.Reaches (Counter.step (program factor))
      (configuration factor (transfer factor) first second)
      (configuration factor (transfer factor) (first + second) 0) := by
  induction second generalizing first with
  | zero =>
      simp only [Nat.add_zero]
      exact Relation.ReflTransGen.refl
  | succ second induction_hypothesis =>
      have rest := induction_hypothesis (first := first + 1)
      have arithmetic : first + 1 + second = first + (second + 1) := by omega
      rw [arithmetic] at rest
      exact Relation.ReflTransGen.head (step_transfer factor first second)
        (Relation.ReflTransGen.head (step_restore factor first second) rest)

/-- Entry and exit are explicit cells of the same finite two-counter table. -/
theorem reaches_result (factor input : ℕ) :
    StateTransition.Reaches (Counter.step (program factor))
      (configuration factor 0 input 0)
      (configuration factor (finish factor) (factor * input) 0) := by
  have consumed := consume_reach factor input 0
  simp only [Nat.zero_add] at consumed
  have moved := transfer_reach factor 0 (factor * input)
  simp only [Nat.zero_add] at moved
  exact consumed.trans (Relation.ReflTransGen.head (step_begin_transfer factor (factor * input))
    (moved.tail (step_finish factor (factor * input))))

/-- Complete partial execution returns precisely the product, with the second counter cleared. -/
theorem eval_result (factor input : ℕ) :
    Counter.eval (program factor) (configuration factor 0 input 0) =
      Part.some (configuration factor (finish factor) (factor * input) 0) := by
  apply Part.eq_some_iff.mpr
  exact StateTransition.mem_eval.mpr ⟨reaches_result factor input, halted factor (factor * input) 0⟩

end Monodromy.CounterMultiplication

namespace Monodromy.Counter.DivMod

variable (p : ℕ) [NeZero p]

/-- Four bounded-remainder phases and one quotient-increment address. -/
def size : ℕ := 4 * p + 1

def consume (remainder : Fin p) : Fin (size p) := ⟨remainder.val, by dsimp [size]; omega⟩
def transfer (remainder : Fin p) : Fin (size p) := ⟨p + remainder.val, by dsimp [size]; omega⟩
def restore (remainder : Fin p) : Fin (size p) := ⟨2 * p + remainder.val, by dsimp [size]; omega⟩
def finish (remainder : Fin p) : Fin (size p) := ⟨3 * p + remainder.val, by dsimp [size]; omega⟩
def bump : Fin (size p) := ⟨4 * p, by dsimp [size]; omega⟩

def next (remainder : Fin p) : Fin (size p) :=
  if bound : remainder.val + 1 < p then consume p ⟨remainder.val + 1, bound⟩ else bump p

/-- Division is implemented by a static finite inc/dec/halt table. -/
def program : Counter.Program 2 (size p) := fun address =>
  if first : address.val < p then
    .dec 0 (transfer p ⟨address.val, first⟩) (next p ⟨address.val, first⟩)
  else if second : address.val < 2 * p then
    .dec 1 (finish p ⟨address.val - p, by omega⟩) (restore p ⟨address.val - p, by omega⟩)
  else if third : address.val < 3 * p then
    .inc 0 (transfer p ⟨address.val - 2 * p, by omega⟩)
  else if address.val < 4 * p then .halt
  else .inc 1 (consume p 0)

@[simp] theorem program_consume (remainder : Fin p) :
    program p (consume p remainder) = .dec 0 (transfer p remainder) (next p remainder) := by
  simp [program, consume, remainder.isLt]

@[simp] theorem program_transfer (remainder : Fin p) :
    program p (transfer p remainder) = .dec 1 (finish p remainder) (restore p remainder) := by
  have first : ¬ p + remainder.val < p := by omega
  have second : p + remainder.val < 2 * p := by omega
  simp [program, transfer, first, second]

@[simp] theorem program_restore (remainder : Fin p) :
    program p (restore p remainder) = .inc 0 (transfer p remainder) := by
  have first : ¬ 2 * p + remainder.val < p := by omega
  have second : ¬ 2 * p + remainder.val < 2 * p := by omega
  have third : 2 * p + remainder.val < 3 * p := by omega
  simp [program, restore, first, second, third]

@[simp] theorem program_finish (remainder : Fin p) : program p (finish p remainder) = .halt := by
  have first : ¬ 3 * p + remainder.val < p := by omega
  have second : ¬ 3 * p + remainder.val < 2 * p := by omega
  have third : ¬ 3 * p + remainder.val < 3 * p := by omega
  have fourth : 3 * p + remainder.val < 4 * p := by omega
  simp [program, finish, first, second, third, fourth]

@[simp] theorem program_bump : program p (bump p) = .inc 1 (consume p 0) := by
  have first : ¬ 4 * p < p := by omega
  have second : ¬ 4 * p < 2 * p := by omega
  have third : ¬ 4 * p < 3 * p := by omega
  simp [program, bump, first, second, third]

/-- The only unbounded storage is the same pair of natural-number counters. -/
def configuration (address : Fin (size p)) (first second : ℕ) : Counter.Configuration 2 (size p) :=
  ⟨address, ![first, second]⟩

private theorem update_first (first second value : ℕ) :
    Function.update ![first, second] 0 value = ![value, second] := by
  funext index
  fin_cases index <;> simp

private theorem update_second (first second value : ℕ) :
    Function.update ![first, second] 1 value = ![first, value] := by
  funext index
  fin_cases index <;> simp

@[simp] theorem step_consume_zero (remainder : Fin p) (second : ℕ) :
    Counter.step (program p) (configuration p (consume p remainder) 0 second) =
      some (configuration p (transfer p remainder) 0 second) := by
  simp [Counter.step, configuration]

@[simp] theorem step_consume_succ (remainder : Fin p) (first second : ℕ) :
    Counter.step (program p) (configuration p (consume p remainder) (first + 1) second) =
      some (configuration p (next p remainder) first second) := by
  simp [Counter.step, configuration, update_first]

@[simp] theorem step_bump (first second : ℕ) :
    Counter.step (program p) (configuration p (bump p) first second) =
      some (configuration p (consume p 0) first (second + 1)) := by
  simp [Counter.step, configuration, update_second]

@[simp] theorem step_transfer_zero (remainder : Fin p) (first : ℕ) :
    Counter.step (program p) (configuration p (transfer p remainder) first 0) =
      some (configuration p (finish p remainder) first 0) := by
  simp [Counter.step, configuration]

@[simp] theorem step_transfer_succ (remainder : Fin p) (first second : ℕ) :
    Counter.step (program p) (configuration p (transfer p remainder) first (second + 1)) =
      some (configuration p (restore p remainder) first second) := by
  simp [Counter.step, configuration, update_second]

@[simp] theorem step_restore (remainder : Fin p) (first second : ℕ) :
    Counter.step (program p) (configuration p (restore p remainder) first second) =
      some (configuration p (transfer p remainder) (first + 1) second) := by
  simp [Counter.step, configuration, update_first]

@[simp] theorem step_finish (remainder : Fin p) (first second : ℕ) :
    Counter.step (program p) (configuration p (finish p remainder) first second) = none := by
  simp [Counter.step, configuration]

def residue (value : ℕ) : Fin p :=
  ⟨value % p, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne p))⟩

theorem residue_small (remainder : Fin p) : residue p remainder.val = remainder := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt remainder.isLt


private theorem reaches_step {first second : Counter.Configuration 2 (size p)}
    (edge : Counter.step (program p) first = some second) :
    StateTransition.Reaches (Counter.step (program p)) first second := by
  apply Relation.ReflTransGen.single
  exact edge

private theorem prepend {first middle last : Counter.Configuration 2 (size p)}
    (edge : Counter.step (program p) first = some middle)
    (rest : StateTransition.Reaches (Counter.step (program p)) middle last) :
    StateTransition.Reaches (Counter.step (program p)) first last := by
  change Relation.ReflTransGen (fun a b => b ∈ Counter.step (program p) a) _ _
  exact Relation.ReflTransGen.head edge rest

/-- Consuming the first counter accumulates the quotient and retains the remainder in control. -/
theorem consume_reaches (first second : ℕ) (remainder : Fin p) :
    StateTransition.Reaches (Counter.step (program p))
      (configuration p (consume p remainder) first second)
      (configuration p (transfer p (residue p (first + remainder.val))) 0
        (second + (first + remainder.val) / p)) := by
  induction first generalizing second remainder with
  | zero =>
      simpa only [Nat.zero_add, residue_small, Nat.div_eq_of_lt remainder.isLt, Nat.add_zero] using
        (reaches_step p (step_consume_zero p remainder second))
  | succ first recursive =>
      by_cases bound : remainder.val + 1 < p
      · let next_remainder : Fin p := ⟨remainder.val + 1, bound⟩
        have next_step : Counter.step (program p)
            (configuration p (consume p remainder) (first + 1) second) =
            some (configuration p (consume p next_remainder) first second) := by
          simpa only [next, dite_eq_left bound] using step_consume_succ p remainder first second
        have run := prepend p next_step (recursive second next_remainder)
        have same_sum : first + next_remainder.val = first + 1 + remainder.val := by
          dsimp [next_remainder]
          omega
        simpa only [same_sum] using run
      · have last : remainder.val + 1 = p := by omega
        have next_step : Counter.step (program p)
            (configuration p (consume p remainder) (first + 1) second) =
            some (configuration p (bump p) first second) := by
          simpa only [next, dite_eq_right bound] using step_consume_succ p remainder first second
        have run := prepend p next_step
          (prepend p (step_bump p first second) (recursive (second + 1) 0))
        have same_sum : first + 1 + remainder.val = first + p := by omega
        have residue_eq : residue p (first + p) = residue p first := by
          apply Fin.ext
          exact Nat.add_mod_right first p
        simpa only [Fin.val_zero, Nat.add_zero, same_sum, residue_eq,
          Nat.add_div_right first (Nat.pos_of_ne_zero (NeZero.ne p)),
          Nat.add_assoc, Nat.add_comm 1 (first / p)] using run

/-- Moving the workspace back preserves its finite remainder address. -/
theorem transfer_reaches (remainder : Fin p) (first second : ℕ) :
    StateTransition.Reaches (Counter.step (program p))
      (configuration p (transfer p remainder) first second)
      (configuration p (finish p remainder) (first + second) 0) := by
  induction second generalizing first with
  | zero =>
      simpa only [Nat.add_zero] using
        (reaches_step p (step_transfer_zero p remainder first))
  | succ second recursive =>
      have run := prepend p (step_transfer_succ p remainder first second)
        (prepend p (step_restore p remainder first second) (recursive (first + 1)))
      simpa only [Nat.add_assoc, Nat.add_comm 1 second] using run

/-- The division macro uses no unbounded storage besides its two input counters. -/
theorem reaches_divmod (input : ℕ) :
    StateTransition.Reaches (Counter.step (program p))
      (configuration p (consume p 0) input 0)
      (configuration p (finish p (residue p input)) (input / p) 0) := by
  have consumed := consume_reaches p input 0 0
  simp only [Fin.val_zero, Nat.add_zero, Nat.zero_add] at consumed
  have restored := transfer_reaches p (residue p input) 0 (input / p)
  simp only [Nat.zero_add] at restored
  exact consumed.trans restored

/-- Quotient and remainder are specifications of the final counters and finite address. -/
theorem eval_divmod (input : ℕ) :
    Counter.eval (program p) (configuration p (consume p 0) input 0) =
      Part.some (configuration p (finish p (residue p input)) (input / p) 0) := by
  apply Part.eq_some_iff.mpr
  exact StateTransition.mem_eval.mpr ⟨reaches_divmod p input, step_finish p _ _ _⟩

omit [NeZero p] in
/-- Distinct bounded remainders remain distinct final program addresses. -/
theorem finish_injective : Function.Injective (finish p) := by
  intro first second same
  apply Fin.ext
  have values := congrArg Fin.val same
  dsimp [finish] at values
  omega

@[simp] theorem finish_residue_val (input : ℕ) :
    (finish p (residue p input)).val = 3 * p + input % p := rfl

end Monodromy.Counter.DivMod

namespace Monodromy.CounterPrimeProbe

variable (p : ℕ) [NeZero p]

/-- The program contains only the two already checked finite arithmetic tables. -/
def size : ℕ := Counter.DivMod.size p + (p + 4)

def divBlock (address : Fin (Counter.DivMod.size p)) : Fin (size p) :=
  Fin.castAdd (p + 4) address

def mulAddress (address : Fin (p + 4)) : Fin (size p) :=
  Fin.natAdd (Counter.DivMod.size p) address

/-- Nonzero remainder exits enter the multiplier's existing bounded countdown. -/
def divAddress (address : Fin (Counter.DivMod.size p)) : Fin (size p) :=
  match Counter.DivMod.program p address with
  | .halt =>
      if address.val = 3 * p then divBlock p address
      else mulAddress p (CounterMultiplication.phase p (address.val - 3 * p))
  | _ => divBlock p address

def entry : Fin (size p) := divAddress p (Counter.DivMod.consume p 0)
def success : Fin (size p) := divBlock p (Counter.DivMod.finish p 0)
def failure : Fin (size p) := mulAddress p (CounterMultiplication.finish p)

/-- Rewired finite program counters provide the conditional; the instructions remain inc/dec/halt. -/
def program : Counter.Program 2 (size p) :=
  Fin.addCases
    (fun address => Counter.mapInstruction (divAddress p) (Counter.DivMod.program p address))
    (fun address => Counter.mapInstruction (mulAddress p) (CounterMultiplication.program p address))

def configuration (address : Fin (size p)) (first second : ℕ) : Counter.Configuration 2 (size p) :=
  ⟨address, ![first, second]⟩

@[simp] theorem entry_eq : entry p = divBlock p (Counter.DivMod.consume p 0) := by
  simp [entry, divAddress]

@[simp] theorem program_divBlock (address : Fin (Counter.DivMod.size p)) :
    program p (divBlock p address) =
      Counter.mapInstruction (divAddress p) (Counter.DivMod.program p address) := by
  simp [program, divBlock]

@[simp] theorem program_mulAddress (address : Fin (p + 4)) :
    program p (mulAddress p address) =
      Counter.mapInstruction (mulAddress p) (CounterMultiplication.program p address) := by
  simp [program, mulAddress]

theorem div_agrees (address : Fin (Counter.DivMod.size p))
    (live : Counter.DivMod.program p address ≠ .halt) :
    program p (divAddress p address) =
      Counter.mapInstruction (divAddress p) (Counter.DivMod.program p address) := by
  have actual : divAddress p address = divBlock p address := by
    unfold divAddress
    cases operation : Counter.DivMod.program p address <;> simp_all
  rw [actual, program_divBlock]

@[simp] theorem div_finish_zero :
    divAddress p (Counter.DivMod.finish p 0) = success p := by
  unfold divAddress
  rw [Counter.DivMod.program_finish]
  simp [success, Counter.DivMod.finish]

theorem div_finish_nonzero (remainder : Fin p) (nonzero : remainder.val ≠ 0) :
    divAddress p (Counter.DivMod.finish p remainder) =
      mulAddress p (CounterMultiplication.phase p remainder.val) := by
  have different : 3 * p + remainder.val ≠ 3 * p := by omega
  unfold divAddress
  rw [Counter.DivMod.program_finish]
  change (if 3 * p + remainder.val = 3 * p then divBlock p (Counter.DivMod.finish p remainder)
    else mulAddress p (CounterMultiplication.phase p ((3 * p + remainder.val) - 3 * p))) = _
  rw [ite_eq_right different]
  simp only [Nat.add_sub_cancel_left]

@[simp] theorem program_success : program p (success p) = .halt := by
  simp [success, Counter.mapInstruction]

@[simp] theorem program_failure : program p (failure p) = .halt := by
  simp [failure, Counter.mapInstruction, CounterMultiplication.program_finish]

/-- The two final addresses are distinct finite-control outcomes. -/
theorem exits_distinct : success p ≠ failure p := by
  intro same
  have values := congrArg Fin.val same
  dsimp [success, failure, divBlock, mulAddress, Counter.DivMod.finish,
    Counter.DivMod.size, CounterMultiplication.finish] at values
  omega

private theorem div_configuration (address : Fin (Counter.DivMod.size p)) (first second : ℕ) :
    Counter.mapConfiguration (divAddress p) (Counter.DivMod.configuration p address first second) =
      configuration p (divAddress p address) first second := rfl

omit [NeZero p] in
private theorem mul_configuration (address : Fin (p + 4)) (first second : ℕ) :
    Counter.mapConfiguration (mulAddress p) (CounterMultiplication.configuration p address first second) =
      configuration p (mulAddress p address) first second := rfl

/-- Division reaches a success address or an actual multiplier countdown entry. -/
theorem divide_reaches (input : ℕ) :
    StateTransition.Reaches (Counter.step (program p))
      (configuration p (entry p) input 0)
      (configuration p (divAddress p (Counter.DivMod.finish p (Counter.DivMod.residue p input)))
        (input / p) 0) := by
  have run := Counter.reaches_map_live (divAddress p) (Counter.DivMod.program p) (program p)
    (div_agrees p) (Counter.DivMod.reaches_divmod p input)
  simpa only [div_configuration, entry] using run

/-- The multiplier countdown first writes the bounded remainder, then restores the original number. -/
theorem restore_reaches (remainder : Fin p) (quotient : ℕ) :
    StateTransition.Reaches (Counter.step (program p))
      (configuration p (mulAddress p (CounterMultiplication.phase p remainder.val)) quotient 0)
      (configuration p (failure p) (remainder.val + p * quotient) 0) := by
  have seeded := CounterMultiplication.increments_reach p remainder.val quotient 0
    (Nat.le_of_lt remainder.isLt)
  simp only [Nat.zero_add] at seeded
  have consumed := CounterMultiplication.consume_reach p quotient remainder.val
  have transferred := CounterMultiplication.transfer_reach p 0 (remainder.val + p * quotient)
  simp only [Nat.zero_add] at transferred
  have run : StateTransition.Reaches (Counter.step (CounterMultiplication.program p))
      (CounterMultiplication.configuration p (CounterMultiplication.phase p remainder.val) quotient 0)
      (CounterMultiplication.configuration p (CounterMultiplication.finish p) (remainder.val + p * quotient) 0) :=
    seeded.trans (consumed.trans
      (Relation.ReflTransGen.head
        (CounterMultiplication.step_begin_transfer p (remainder.val + p * quotient))
        (transferred.tail (CounterMultiplication.step_finish p (remainder.val + p * quotient)))))
  have mapped := Counter.reaches_map_live (mulAddress p) (CounterMultiplication.program p) (program p)
    (fun address _ => program_mulAddress p address) run
  simpa only [mul_configuration, failure] using mapped

/-- Divisible inputs are divided; the workspace returns to zero. -/
theorem reaches_success (input : ℕ) (divides : p ∣ input) :
    StateTransition.Reaches (Counter.step (program p))
      (configuration p (entry p) input 0)
      (configuration p (success p) (input / p) 0) := by
  have remainder_zero : Counter.DivMod.residue p input = 0 := by
    apply Fin.ext
    exact Nat.dvd_iff_mod_eq_zero.mp divides
  simpa only [remainder_zero, div_finish_zero] using divide_reaches p input

/-- Every other input is restored exactly, with a distinct final control outcome. -/
theorem reaches_failure (input : ℕ) (nondivides : ¬ p ∣ input) :
    StateTransition.Reaches (Counter.step (program p))
      (configuration p (entry p) input 0)
      (configuration p (failure p) input 0) := by
  have remainder_nonzero : (Counter.DivMod.residue p input).val ≠ 0 := by
    intro zero
    exact nondivides (Nat.dvd_iff_mod_eq_zero.mpr zero)
  have divided := divide_reaches p input
  rw [div_finish_nonzero p _ remainder_nonzero] at divided
  have restored := restore_reaches p (Counter.DivMod.residue p input) (input / p)
  have reconstruct : (Counter.DivMod.residue p input).val + p * (input / p) = input :=
    Nat.mod_add_div input p
  rw [reconstruct] at restored
  exact divided.trans restored

/-- Complete evaluation returns exactly one of the two finite-control outcomes. -/
theorem eval_result (input : ℕ) :
    Counter.eval (program p) (configuration p (entry p) input 0) =
      Part.some (if p ∣ input then configuration p (success p) (input / p) 0
        else configuration p (failure p) input 0) := by
  apply Part.eq_some_iff.mpr
  apply StateTransition.mem_eval.mpr
  by_cases divides : p ∣ input
  · simp only [ite_eq_left divides]
    exact ⟨reaches_success p input divides,
      Counter.step_halt _ _ (program_success p)⟩
  · simp only [ite_eq_right divides]
    exact ⟨reaches_failure p input divides,
      Counter.step_halt _ _ (program_failure p)⟩

theorem entry_live : program p (entry p) ≠ .halt := by
  rw [entry_eq, program_divBlock, Counter.DivMod.program_consume]
  simp [Counter.mapInstruction]

theorem entry_ne_success : entry p ≠ success p := by
  rw [entry_eq]
  intro same
  have values := congrArg Fin.val same
  have positive : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  dsimp [success, divBlock, Counter.DivMod.consume, Counter.DivMod.finish] at values
  omega

theorem entry_ne_failure : entry p ≠ failure p := by
  rw [entry_eq]
  intro same
  have values := congrArg Fin.val same
  dsimp [failure, divBlock, mulAddress, Counter.DivMod.consume,
    Counter.DivMod.size, CounterMultiplication.finish] at values
  omega

private theorem positive_run {first last : Counter.Configuration 2 (size p)}
    (run : StateTransition.Reaches (Counter.step (program p)) first last)
    (different : first ≠ last) :
    StateTransition.Reaches₁ (Counter.step (program p)) first last := by
  unfold StateTransition.Reaches at run
  unfold StateTransition.Reaches₁
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp run with same | moves
  · exact False.elim (different same.symm)
  · exact moves

/-- Positivity survives later rewiring, including source-machine self-loops. -/
theorem reaches_success₁ (input : ℕ) (divides : p ∣ input) :
    StateTransition.Reaches₁ (Counter.step (program p))
      (configuration p (entry p) input 0)
      (configuration p (success p) (input / p) 0) := by
  apply positive_run p (reaches_success p input divides)
  intro same
  exact entry_ne_success p (congrArg Counter.Configuration.pc same)

theorem reaches_failure₁ (input : ℕ) (nondivides : ¬ p ∣ input) :
    StateTransition.Reaches₁ (Counter.step (program p))
      (configuration p (entry p) input 0)
      (configuration p (failure p) input 0) := by
  apply positive_run p (reaches_failure p input nondivides)
  intro same
  exact entry_ne_failure p (congrArg Counter.Configuration.pc same)

end Monodromy.CounterPrimeProbe

namespace Monodromy.Counter.TuringCompiler

open Turing

variable (a q : ℕ) [NeZero a] [NeZero q]

def base : ℕ := a + 1
instance base_neZero : NeZero (base a) := ⟨by simp [base]⟩

abbrev Row := Fin q × Fin a
abbrev Phase := Unit ⊕ (Fin (base a + 4) ⊕ (Fin a ⊕ Fin (DivMod.size (base a))))
abbrev Address := Row a q × Phase a

def size : ℕ := Fintype.card (Address a q)

def address : Address a q ≃ Fin (size a q) := Fintype.equivFin _

def dispatch (row : Row a q) : Fin (size a q) := address a q (row, Sum.inl ())
def multiply (row : Row a q) (cell : Fin (base a + 4)) : Fin (size a q) :=
  address a q (row, Sum.inr (Sum.inl cell))
def add (row : Row a q) (remaining : Fin a) : Fin (size a q) :=
  address a q (row, Sum.inr (Sum.inr (Sum.inl remaining)))
def divide (row : Row a q) (cell : Fin (DivMod.size (base a))) : Fin (size a q) :=
  address a q (row, Sum.inr (Sum.inr (Sum.inr cell)))

omit [NeZero a] [NeZero q] in
@[simp] theorem address_dispatch (row : Row a q) :
    (address a q).symm (dispatch a q row) = (row, Sum.inl ()) :=
  (address a q).symm_apply_apply _
omit [NeZero a] [NeZero q] in
@[simp] theorem address_multiply (row : Row a q) (cell : Fin (base a + 4)) :
    (address a q).symm (multiply a q row cell) = (row, Sum.inr (Sum.inl cell)) :=
  (address a q).symm_apply_apply _
omit [NeZero a] [NeZero q] in
@[simp] theorem address_add (row : Row a q) (remaining : Fin a) :
    (address a q).symm (add a q row remaining) =
      (row, Sum.inr (Sum.inr (Sum.inl remaining))) :=
  (address a q).symm_apply_apply _
omit [NeZero a] [NeZero q] in
@[simp] theorem address_divide (row : Row a q) (cell : Fin (DivMod.size (base a))) :
    (address a q).symm (divide a q row cell) =
      (row, Sum.inr (Sum.inr (Sum.inr cell))) :=
  (address a q).symm_apply_apply _

omit [NeZero a] [NeZero q] in
theorem dispatch_injective : Function.Injective (dispatch a q) := by
  intro first second same
  exact congrArg Prod.fst ((address a q).injective same)

def counters (left right : ℕ) : Fin 3 → ℕ := ![left, right, 0]

def encode (state : TM0.Cfg (Fin a) (Fin q)) : Configuration 3 (size a q) :=
  ⟨dispatch a q (state.q, state.Tape.head),
    counters (TapeCode.encode state.Tape.left) (TapeCode.encode state.Tape.right)⟩

omit [NeZero q] in
theorem encode_injective : Function.Injective (encode a q) := by
  intro first second same
  cases first with
  | mk fq ft =>
    cases second with
    | mk sq st =>
      cases ft with
      | mk fh fl fr =>
        cases st with
        | mk sh sl sr =>
          have row := dispatch_injective a q (congrArg Configuration.pc same)
          have left : TapeCode.encode fl = TapeCode.encode sl :=
            congrFun (congrArg Configuration.counters same) 0
          have right : TapeCode.encode fr = TapeCode.encode sr :=
            congrFun (congrArg Configuration.counters same) 1
          have heq : fh = sh := congrArg Prod.snd row
          have qeq : fq = sq := congrArg Prod.fst row
          have leq := TapeCode.encode_injective left
          have req := TapeCode.encode_injective right
          cases heq
          cases qeq
          cases leq
          cases req
          rfl

def pushRegister : Dir → Fin 2 | .left => 1 | .right => 0
def popRegister : Dir → Fin 2 | .left => 0 | .right => 1

def mulTarget (row : Row a q) (cell : Fin (base a + 4)) : Fin (size a q) :=
  if cell = CounterMultiplication.finish (base a) then add a q row row.2
  else multiply a q row cell

def symbol (remainder : Fin (base a)) : Fin a :=
  if bound : remainder.val < a then ⟨remainder.val, bound⟩ else 0

def divTarget (row : Row a q) (target : Fin q)
    (cell : Fin (DivMod.size (base a))) : Fin (size a q) :=
  if terminal : ∃ remainder, cell = DivMod.finish (base a) remainder then
    dispatch a q (target, symbol a terminal.choose)
  else divide a q row cell

omit [NeZero a] [NeZero q] in
@[simp] theorem mulTarget_finish (row : Row a q) :
    mulTarget a q row (CounterMultiplication.finish (base a)) = add a q row row.2 := by
  simp [mulTarget]

omit [NeZero q] in
@[simp] theorem divTarget_finish (row : Row a q) (target : Fin q)
    (remainder : Fin (base a)) :
    divTarget a q row target (DivMod.finish (base a) remainder) =
      dispatch a q (target, symbol a remainder) := by
  have terminal : ∃ r, DivMod.finish (base a) remainder = DivMod.finish (base a) r :=
    ⟨remainder, rfl⟩
  have chosen : terminal.choose = remainder :=
    (DivMod.finish_injective (base a) terminal.choose_spec).symm
  simp only [divTarget, dite_eq_left terminal, chosen]

def previous (remaining : Fin a) : Fin a :=
  ⟨remaining.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) remaining.isLt⟩

def body (machine : TM0.Machine (Fin a) (Fin q)) (location : Address a q) :
    Instruction 3 (size a q) :=
  let row := location.1
  match machine row.1 row.2 with
  | none => .halt
  | some (target, .write value) =>
      match location.2 with
      | .inl () => .dec 2 (dispatch a q (target, value)) (dispatch a q (target, value))
      | .inr _ => .halt
  | some (target, .move direction) =>
      match location.2 with
      | .inl () => .dec 2 (mulTarget a q row 0) (mulTarget a q row 0)
      | .inr (.inl cell) =>
          mapInstruction (mulTarget a q row)
            (RegisterRelocation.instruction
              (RegisterRelocation.pairIntoThree (pushRegister direction))
              (CounterMultiplication.program (base a) cell))
      | .inr (.inr (.inl remaining)) =>
          if remaining.val = 0 then
            .dec 2 (divTarget a q row target (DivMod.consume (base a) 0))
              (divTarget a q row target (DivMod.consume (base a) 0))
          else .inc (pushRegister direction).castSucc (add a q row (previous a remaining))
      | .inr (.inr (.inr cell)) =>
          mapInstruction (divTarget a q row target)
            (RegisterRelocation.instruction
              (RegisterRelocation.pairIntoThree (popRegister direction))
              (DivMod.program (base a) cell))

def program (machine : TM0.Machine (Fin a) (Fin q)) : Program 3 (size a q) :=
  fun cell => body a q machine ((address a q).symm cell)

@[simp] theorem program_dispatch (machine : TM0.Machine (Fin a) (Fin q)) (row : Row a q) :
    program a q machine (dispatch a q row) =
      match machine row.1 row.2 with
      | none => .halt
      | some (target, .write value) =>
          .dec 2 (dispatch a q (target, value)) (dispatch a q (target, value))
      | some (_, .move _) => .dec 2 (mulTarget a q row 0) (mulTarget a q row 0) := by
  simp only [program, address_dispatch, body]

theorem halt_encode (machine : TM0.Machine (Fin a) (Fin q))
    (state : TM0.Cfg (Fin a) (Fin q)) :
    step (program a q machine) (encode a q state) = none ↔ TM0.step machine state = none := by
  simp only [step, encode, program_dispatch, TM0.step]
  cases result : machine state.q state.Tape.head with
  | none => simp
  | some command =>
      rcases command with ⟨target, operation⟩
      cases operation <;> simp [counters]

theorem write_step (machine : TM0.Machine (Fin a) (Fin q))
    (state : TM0.Cfg (Fin a) (Fin q)) (target : Fin q) (value : Fin a)
    (instruction : machine state.q state.Tape.head = some (target, .write value)) :
    step (program a q machine) (encode a q state) =
      some (encode a q ⟨target, state.Tape.write value⟩) := by
  simp [step, encode, instruction, counters, Tape.write]

/-- A marked source boundary is determined by the finite program counter alone. -/
def Boundary (cell : Fin (size a q)) : Prop := ∃ row, cell = dispatch a q row

omit [NeZero q] in
@[simp] theorem encode_boundary (state : TM0.Cfg (Fin a) (Fin q)) :
    Boundary a q (encode a q state).pc := ⟨(state.q, state.Tape.head), rfl⟩

omit [NeZero a] [NeZero q] in
theorem multiply_not_boundary (row : Row a q) (cell : Fin (base a + 4)) :
    ¬ Boundary a q (multiply a q row cell) := by
  rintro ⟨other, same⟩
  have incompatible := congrArg Prod.snd ((address a q).injective same)
  cases incompatible

omit [NeZero a] [NeZero q] in
theorem add_not_boundary (row : Row a q) (remaining : Fin a) :
    ¬ Boundary a q (add a q row remaining) := by
  rintro ⟨other, same⟩
  have incompatible := congrArg Prod.snd ((address a q).injective same)
  cases incompatible

omit [NeZero a] [NeZero q] in
theorem divide_not_boundary (row : Row a q) (cell : Fin (DivMod.size (base a))) :
    ¬ Boundary a q (divide a q row cell) := by
  rintro ⟨other, same⟩
  have incompatible := congrArg Prod.snd ((address a q).injective same)
  cases incompatible

/-- Internal arithmetic transitions exclude dispatch cells at their source. -/
def InternalStep (machine : TM0.Machine (Fin a) (Fin q))
    (first last : Configuration 3 (size a q)) : Prop :=
  step (program a q machine) first = some last ∧ ¬ Boundary a q first.pc

abbrev InternalReaches (machine : TM0.Machine (Fin a) (Fin q)) :=
  Relation.ReflTransGen (InternalStep a q machine)

private theorem map_internal {m : ℕ}
    (machine : TM0.Machine (Fin a) (Fin q)) (oldProgram : Program 3 m)
    (rename : Fin m → Fin (size a q))
    (agrees : ∀ cell, oldProgram cell ≠ .halt →
      program a q machine (rename cell) = mapInstruction rename (oldProgram cell))
    (internal : ∀ cell, oldProgram cell ≠ .halt → ¬ Boundary a q (rename cell))
    {first last : Configuration 3 m}
    (run : StateTransition.Reaches (step oldProgram) first last) :
    InternalReaches a q machine (mapConfiguration rename first) (mapConfiguration rename last) := by
  induction run with
  | refl => exact Relation.ReflTransGen.refl
  | @tail middle last _ edge previous =>
      apply previous.tail
      constructor
      · exact step_map_live rename oldProgram (program a q machine) agrees edge
      · apply internal
        intro halted
        simp [step, halted] at edge

private theorem mul_live (machine : TM0.Machine (Fin a) (Fin q))
    (row : Row a q) (target : Fin q) (direction : Dir)
    (selected : machine row.1 row.2 = some (target, .move direction))
    (cell : Fin (base a + 4))
    (live : RegisterRelocation.program
      (RegisterRelocation.pairIntoThree (pushRegister direction))
      (CounterMultiplication.program (base a)) cell ≠ .halt) :
    program a q machine (mulTarget a q row cell) =
      mapInstruction (mulTarget a q row)
        (RegisterRelocation.program
          (RegisterRelocation.pairIntoThree (pushRegister direction))
          (CounterMultiplication.program (base a)) cell) ∧
    ¬ Boundary a q (mulTarget a q row cell) := by
  have not_finish : cell ≠ CounterMultiplication.finish (base a) := by
    intro same
    subst cell
    simp [RegisterRelocation.program, RegisterRelocation.instruction,
      CounterMultiplication.program_finish] at live
  constructor
  · simp [mulTarget, not_finish, program, body, selected, RegisterRelocation.program]
  · simpa only [mulTarget, ite_eq_right not_finish] using multiply_not_boundary a q row cell

private theorem div_live (machine : TM0.Machine (Fin a) (Fin q))
    (row : Row a q) (target : Fin q) (direction : Dir)
    (selected : machine row.1 row.2 = some (target, .move direction))
    (cell : Fin (DivMod.size (base a)))
    (live : RegisterRelocation.program
      (RegisterRelocation.pairIntoThree (popRegister direction))
      (DivMod.program (base a)) cell ≠ .halt) :
    program a q machine (divTarget a q row target cell) =
      mapInstruction (divTarget a q row target)
        (RegisterRelocation.program
          (RegisterRelocation.pairIntoThree (popRegister direction))
          (DivMod.program (base a)) cell) ∧
    ¬ Boundary a q (divTarget a q row target cell) := by
  have not_finish : ¬ ∃ remainder, cell = DivMod.finish (base a) remainder := by
    rintro ⟨remainder, rfl⟩
    simp [RegisterRelocation.program, RegisterRelocation.instruction] at live
  constructor
  · simp [divTarget, not_finish, program, body, selected, RegisterRelocation.program]
  · simpa only [divTarget, dite_eq_right not_finish] using divide_not_boundary a q row cell

def frame (active : Fin 2) (first spectator : ℕ) : Fin 3 → ℕ :=
  if active = 0 then counters first spectator else counters spectator first

private theorem extend_frame (active : Fin 2) (old value spectator : ℕ) :
    Function.extend (RegisterRelocation.pairIntoThree active) ![value, 0]
      (frame active old spectator) = frame active value spectator := by
  have first := (RegisterRelocation.pairIntoThree_injective active).extend_apply
    ![value, 0] (frame active old spectator) (0 : Fin 2)
  have scratch := (RegisterRelocation.pairIntoThree_injective active).extend_apply
    ![value, 0] (frame active old spectator) (1 : Fin 2)
  fin_cases active <;> funext index <;> fin_cases index
  all_goals first
    | exact first
    | exact scratch
    | apply Function.extend_apply'
      rintro ⟨source, same⟩
      fin_cases source <;> norm_num [RegisterRelocation.pairIntoThree] at same

/-- Multiplication uses only its allocated stack and the shared zero scratch. -/
theorem multiply_reaches (machine : TM0.Machine (Fin a) (Fin q))
    (row : Row a q) (target : Fin q) (direction : Dir)
    (selected : machine row.1 row.2 = some (target, .move direction))
    (value spectator : ℕ) :
    InternalReaches a q machine
      ⟨mulTarget a q row 0, frame (pushRegister direction) value spectator⟩
      ⟨add a q row row.2, frame (pushRegister direction) (base a * value) spectator⟩ := by
  have relocated := RegisterRelocation.reaches_embed
    (RegisterRelocation.pairIntoThree (pushRegister direction))
    (RegisterRelocation.pairIntoThree_injective (pushRegister direction))
    (frame (pushRegister direction) value spectator)
    (CounterMultiplication.program (base a))
    (CounterMultiplication.reaches_result (base a) value)
  have embedded := map_internal a q machine _ (mulTarget a q row)
    (fun cell live => (mul_live a q machine row target direction selected cell live).1)
    (fun cell live => (mul_live a q machine row target direction selected cell live).2)
    relocated
  simpa only [mapConfiguration, RegisterRelocation.embed, CounterMultiplication.configuration,
    extend_frame, mulTarget_finish] using embedded

/-- Division returns the remainder in finite control and clears the shared scratch. -/
theorem divide_reaches (machine : TM0.Machine (Fin a) (Fin q))
    (row : Row a q) (target : Fin q) (direction : Dir)
    (selected : machine row.1 row.2 = some (target, .move direction))
    (value spectator : ℕ) :
    InternalReaches a q machine
      ⟨divTarget a q row target (DivMod.consume (base a) 0),
        frame (popRegister direction) value spectator⟩
      ⟨dispatch a q (target, symbol a (DivMod.residue (base a) value)),
        frame (popRegister direction) (value / base a) spectator⟩ := by
  have relocated := RegisterRelocation.reaches_embed
    (RegisterRelocation.pairIntoThree (popRegister direction))
    (RegisterRelocation.pairIntoThree_injective (popRegister direction))
    (frame (popRegister direction) value spectator)
    (DivMod.program (base a)) (DivMod.reaches_divmod (base a) value)
  have embedded := map_internal a q machine _ (divTarget a q row target)
    (fun cell live => (div_live a q machine row target direction selected cell live).1)
    (fun cell live => (div_live a q machine row target direction selected cell live).2)
    relocated
  simpa only [mapConfiguration, RegisterRelocation.embed, DivMod.configuration,
    extend_frame, divTarget_finish] using embedded

private theorem frame_scratch (active : Fin 2) (value spectator : ℕ) :
    frame active value spectator 2 = 0 := by
  fin_cases active <;> rfl

private theorem frame_increment (active : Fin 2) (value spectator : ℕ) :
    Function.update (frame active value spectator) active.castSucc
      (frame active value spectator active.castSucc + 1) = frame active (value + 1) spectator := by
  fin_cases active <;> funext index <;> fin_cases index <;> simp [frame, counters]

/-- A finite countdown writes the old head digit, then enters the division macro. -/
theorem add_reaches (machine : TM0.Machine (Fin a) (Fin q))
    (row : Row a q) (target : Fin q) (direction : Dir)
    (selected : machine row.1 row.2 = some (target, .move direction))
    (remaining : Fin a) (value spectator : ℕ) :
    InternalReaches a q machine
      ⟨add a q row remaining, frame (pushRegister direction) value spectator⟩
      ⟨divTarget a q row target (DivMod.consume (base a) 0),
        frame (pushRegister direction) (value + remaining.val) spectator⟩ := by
  have countdown : ∀ count (digit : Fin a), digit.val = count → ∀ current,
      InternalReaches a q machine
        ⟨add a q row digit, frame (pushRegister direction) current spectator⟩
        ⟨divTarget a q row target (DivMod.consume (base a) 0),
          frame (pushRegister direction) (current + count) spectator⟩ := by
    intro count
    induction count with
    | zero =>
        intro digit digit_zero current
        apply Relation.ReflTransGen.single
        constructor
        · simpa only [Nat.add_zero] using
            step_dec_zero (program a q machine)
              ⟨add a q row digit, frame (pushRegister direction) current spectator⟩
              (reg := 2)
              (zero := divTarget a q row target (DivMod.consume (base a) 0))
              (nonzero := divTarget a q row target (DivMod.consume (base a) 0))
              (by simp [program, body, selected, digit_zero])
              (frame_scratch (pushRegister direction) current spectator)
        · exact add_not_boundary a q row digit
    | succ count induction_hypothesis =>
        intro digit digit_succ current
        have nonzero : digit.val ≠ 0 := by omega
        have previous_count : (previous a digit).val = count := by
          simp only [previous]
          omega
        have edge : step (program a q machine)
            ⟨add a q row digit, frame (pushRegister direction) current spectator⟩ =
            some ⟨add a q row (previous a digit),
              frame (pushRegister direction) (current + 1) spectator⟩ := by
          simpa only [frame_increment] using
            step_inc (program a q machine)
              ⟨add a q row digit, frame (pushRegister direction) current spectator⟩
              (reg := (pushRegister direction).castSucc)
              (next := add a q row (previous a digit))
              (by simp [program, body, selected, nonzero])
        have rest := induction_hypothesis (previous a digit) previous_count (current + 1)
        have arithmetic : current + 1 + count = current + (count + 1) := by omega
        rw [arithmetic] at rest
        exact Relation.ReflTransGen.head ⟨edge, add_not_boundary a q row digit⟩ rest
  exact countdown remaining.val remaining rfl value

theorem symbol_tape (tape : ListBlank (Fin a)) :
    symbol a (DivMod.residue (base a) (TapeCode.encode tape)) = tape.head := by
  have remainder : (DivMod.residue (base a) (TapeCode.encode tape)).val = tape.head.val :=
    TapeCode.head_code tape
  have small : (DivMod.residue (base a) (TapeCode.encode tape)).val < a := by
    rw [remainder]
    exact tape.head.isLt
  apply Fin.ext
  simp only [symbol, dite_eq_left small]
  exact remainder

/-- A move traverses only arithmetic PCs until its exact successor dispatch. -/
theorem move_reaches (machine : TM0.Machine (Fin a) (Fin q))
    (state : TM0.Cfg (Fin a) (Fin q)) (target : Fin q) (direction : Dir)
    (selected : machine state.q state.Tape.head = some (target, .move direction)) :
    InternalReaches a q machine
      ⟨mulTarget a q (state.q, state.Tape.head) 0, (encode a q state).counters⟩
      (encode a q ⟨target, state.Tape.move direction⟩) := by
  cases direction with
  | left =>
      have multiplied := multiply_reaches a q machine (state.q, state.Tape.head) target .left
        selected (TapeCode.encode state.Tape.right) (TapeCode.encode state.Tape.left)
      have written := add_reaches a q machine (state.q, state.Tape.head) target .left
        selected state.Tape.head (base a * TapeCode.encode state.Tape.right)
        (TapeCode.encode state.Tape.left)
      have divided := divide_reaches a q machine (state.q, state.Tape.head) target .left
        selected (TapeCode.encode state.Tape.left)
        (base a * TapeCode.encode state.Tape.right + state.Tape.head.val)
      have combined := multiplied.trans (written.trans divided)
      rw [symbol_tape a state.Tape.left] at combined
      simpa [encode, Tape.move, TapeCode.encode_cons, ← TapeCode.tail_code,
        pushRegister, popRegister, frame, counters, Nat.add_comm, base] using combined
  | right =>
      have multiplied := multiply_reaches a q machine (state.q, state.Tape.head) target .right
        selected (TapeCode.encode state.Tape.left) (TapeCode.encode state.Tape.right)
      have written := add_reaches a q machine (state.q, state.Tape.head) target .right
        selected state.Tape.head (base a * TapeCode.encode state.Tape.left)
        (TapeCode.encode state.Tape.right)
      have divided := divide_reaches a q machine (state.q, state.Tape.head) target .right
        selected (TapeCode.encode state.Tape.right)
        (base a * TapeCode.encode state.Tape.left + state.Tape.head.val)
      have combined := multiplied.trans (written.trans divided)
      rw [symbol_tape a state.Tape.right] at combined
      simpa [encode, Tape.move, TapeCode.encode_cons, ← TapeCode.tail_code,
        pushRegister, popRegister, frame, counters, Nat.add_comm, base] using combined

/-- One dispatch edge followed by arithmetic steps whose sources are all unmarked. -/
def FirstReturn (machine : TM0.Machine (Fin a) (Fin q))
    (first last : Configuration 3 (size a q)) : Prop :=
  ∃ after, step (program a q machine) first = some after ∧
    InternalReaches a q machine after last

theorem internal_from_boundary (machine : TM0.Machine (Fin a) (Fin q))
    {first last : Configuration 3 (size a q)}
    (run : InternalReaches a q machine first last) (boundary : Boundary a q first.pc) :
    first = last := by
  rcases Relation.ReflTransGen.cases_head run with same | ⟨next, edge, _⟩
  · exact same
  · exact False.elim (edge.2 boundary)

/-- Each source transition is precisely one positive finite first return. -/
theorem step_firstReturn (machine : TM0.Machine (Fin a) (Fin q))
    {first last : TM0.Cfg (Fin a) (Fin q)} (source : TM0.step machine first = some last) :
    FirstReturn a q machine (encode a q first) (encode a q last) := by
  cases transition : machine first.q first.Tape.head with
  | none => simp [TM0.step, transition] at source
  | some command =>
      rcases command with ⟨target, operation⟩
      cases operation with
      | write value =>
          have destination : (⟨target, first.Tape.write value⟩ : TM0.Cfg (Fin a) (Fin q)) = last := by
            simpa [TM0.step, transition] using source
          subst last
          exact ⟨_, write_step a q machine first target value transition, Relation.ReflTransGen.refl⟩
      | move direction =>
          have destination : (⟨target, first.Tape.move direction⟩ : TM0.Cfg (Fin a) (Fin q)) = last := by
            simpa [TM0.step, transition] using source
          subst last
          refine ⟨⟨mulTarget a q (first.q, first.Tape.head) 0, (encode a q first).counters⟩, ?_,
            move_reaches a q machine first target direction transition⟩
          simp [step, encode, transition, counters]

theorem firstReturn_positive (machine : TM0.Machine (Fin a) (Fin q))
    {first last : Configuration 3 (size a q)} (run : FirstReturn a q machine first last) :
    StateTransition.Reaches₁ (step (program a q machine)) first last := by
  rcases run with ⟨after, initial, rest⟩
  apply Relation.TransGen.head'
    (r := fun current next => next ∈ step (program a q machine) current) initial
  induction rest with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ edge previous => exact previous.tail edge.1

/-- The statically compiled table refines the entire TM transition system. -/
theorem respects (machine : TM0.Machine (Fin a) (Fin q)) :
    StateTransition.Respects (TM0.step machine) (step (program a q machine))
      (fun source target => encode a q source = target) := by
  apply StateTransition.fun_respects.mpr
  intro state
  cases transition : TM0.step machine state with
  | none =>
      change step (program a q machine) (encode a q state) = none
      exact (halt_encode a q machine state).mpr transition
  | some next =>
      exact firstReturn_positive a q machine (step_firstReturn a q machine transition)

/-- Complete configurations, termination, and divergence are preserved together. -/
theorem eval_encode (machine : TM0.Machine (Fin a) (Fin q))
    (state : TM0.Cfg (Fin a) (Fin q)) :
    eval (program a q machine) (encode a q state) =
      encode a q <$> StateTransition.eval (TM0.step machine) state :=
  StateTransition.tr_eval' (TM0.step machine) (step (program a q machine))
    (encode a q) (respects a q machine) state

theorem eval_dom_encode (machine : TM0.Machine (Fin a) (Fin q))
    (state : TM0.Cfg (Fin a) (Fin q)) :
    (eval (program a q machine) (encode a q state)).Dom ↔
      (StateTransition.eval (TM0.step machine) state).Dom := by
  rw [eval_encode]
  rfl

end Monodromy.Counter.TuringCompiler

namespace Monodromy.Counter.Compression

variable {m : ℕ}

instance prime_neZero (register : Fin 3) : NeZero (PrimeCode.prime register) :=
  ⟨(PrimeCode.prime_prime register).ne_zero⟩

def blockSize : Instruction 3 m → ℕ
  | .inc register _ => PrimeCode.prime register + 4
  | .dec register _ _ => CounterPrimeProbe.size (PrimeCode.prime register)
  | .halt => 0

abbrev Address (source : Program 3 m) := Σ row : Fin m, Unit ⊕ Fin (blockSize (source row))

def size (source : Program 3 m) : ℕ := Fintype.card (Address source)
def address (source : Program 3 m) : Address source ≃ Fin (size source) := Fintype.equivFin _

def dispatch (source : Program 3 m) (row : Fin m) : Fin (size source) :=
  address source ⟨row, .inl ()⟩

def multiply (source : Program 3 m) (row : Fin m) (register : Fin 3) (next : Fin m)
    (selected : source row = .inc register next)
    (cell : Fin (PrimeCode.prime register + 4)) : Fin (size source) :=
  address source ⟨row, .inr (cell.cast (by simp [blockSize, selected]))⟩

def probe (source : Program 3 m) (row : Fin m) (register : Fin 3) (zero nonzero : Fin m)
    (selected : source row = .dec register zero nonzero)
    (cell : Fin (CounterPrimeProbe.size (PrimeCode.prime register))) : Fin (size source) :=
  address source ⟨row, .inr (cell.cast (by simp [blockSize, selected]))⟩

@[simp] theorem address_dispatch (source : Program 3 m) (row : Fin m) :
    (address source).symm (dispatch source row) = ⟨row, .inl ()⟩ :=
  (address source).symm_apply_apply _

@[simp] theorem address_multiply (source : Program 3 m) (row : Fin m)
    (register : Fin 3) (next : Fin m) (selected : source row = .inc register next)
    (cell : Fin (PrimeCode.prime register + 4)) :
    (address source).symm (multiply source row register next selected cell) =
      ⟨row, .inr (cell.cast (by simp [blockSize, selected]))⟩ :=
  (address source).symm_apply_apply _

@[simp] theorem address_probe (source : Program 3 m) (row : Fin m)
    (register : Fin 3) (zero nonzero : Fin m) (selected : source row = .dec register zero nonzero)
    (cell : Fin (CounterPrimeProbe.size (PrimeCode.prime register))) :
    (address source).symm (probe source row register zero nonzero selected cell) =
      ⟨row, .inr (cell.cast (by simp [blockSize, selected]))⟩ :=
  (address source).symm_apply_apply _

theorem dispatch_injective (source : Program 3 m) : Function.Injective (dispatch source) := by
  intro first second same
  exact congrArg Sigma.fst ((address source).injective same)

def mulTarget (source : Program 3 m) (row : Fin m) (register : Fin 3) (next : Fin m)
    (selected : source row = .inc register next)
    (cell : Fin (PrimeCode.prime register + 4)) : Fin (size source) :=
  if cell = CounterMultiplication.finish (PrimeCode.prime register) then dispatch source next
  else multiply source row register next selected cell

def probeTarget (source : Program 3 m) (row : Fin m) (register : Fin 3) (zero nonzero : Fin m)
    (selected : source row = .dec register zero nonzero)
    (cell : Fin (CounterPrimeProbe.size (PrimeCode.prime register))) : Fin (size source) :=
  if cell = CounterPrimeProbe.success (PrimeCode.prime register) then dispatch source nonzero
  else if cell = CounterPrimeProbe.failure (PrimeCode.prime register) then dispatch source zero
  else probe source row register zero nonzero selected cell

@[simp] theorem mulTarget_finish (source : Program 3 m) (row : Fin m) (register : Fin 3)
    (next : Fin m) (selected : source row = .inc register next) :
    mulTarget source row register next selected (CounterMultiplication.finish (PrimeCode.prime register)) =
      dispatch source next := by simp [mulTarget]

@[simp] theorem probeTarget_success (source : Program 3 m) (row : Fin m) (register : Fin 3)
    (zero nonzero : Fin m) (selected : source row = .dec register zero nonzero) :
    probeTarget source row register zero nonzero selected
      (CounterPrimeProbe.success (PrimeCode.prime register)) = dispatch source nonzero := by
  simp [probeTarget]

@[simp] theorem probeTarget_failure (source : Program 3 m) (row : Fin m) (register : Fin 3)
    (zero nonzero : Fin m) (selected : source row = .dec register zero nonzero) :
    probeTarget source row register zero nonzero selected
      (CounterPrimeProbe.failure (PrimeCode.prime register)) = dispatch source zero := by
  have distinct := (CounterPrimeProbe.exits_distinct (PrimeCode.prime register)).symm
  simp [probeTarget, distinct]

def body (source : Program 3 m) (location : Address source) : Instruction 2 (size source) :=
  match selected : source location.1 with
  | .halt => .halt
  | .inc register next =>
      match location.2 with
      | .inl () =>
          .dec 1 (mulTarget source location.1 register next selected 0)
            (mulTarget source location.1 register next selected 0)
      | .inr cell =>
          mapInstruction (mulTarget source location.1 register next selected)
            (CounterMultiplication.program (PrimeCode.prime register)
              (cell.cast (by simp [blockSize, selected])))
  | .dec register zero nonzero =>
      match location.2 with
      | .inl () =>
          .dec 1 (probeTarget source location.1 register zero nonzero selected
            (CounterPrimeProbe.entry (PrimeCode.prime register)))
            (probeTarget source location.1 register zero nonzero selected
              (CounterPrimeProbe.entry (PrimeCode.prime register)))
      | .inr cell =>
          mapInstruction (probeTarget source location.1 register zero nonzero selected)
            (CounterPrimeProbe.program (PrimeCode.prime register)
              (cell.cast (by simp [blockSize, selected])))

def program (source : Program 3 m) : Program 2 (size source) :=
  fun cell => body source ((address source).symm cell)

@[simp] theorem program_dispatch (source : Program 3 m) (row : Fin m) :
    program source (dispatch source row) =
      match selected : source row with
      | .halt => .halt
      | .inc register next =>
          .dec 1 (mulTarget source row register next selected 0)
            (mulTarget source row register next selected 0)
      | .dec register zero nonzero =>
          .dec 1 (probeTarget source row register zero nonzero selected
            (CounterPrimeProbe.entry (PrimeCode.prime register)))
            (probeTarget source row register zero nonzero selected
              (CounterPrimeProbe.entry (PrimeCode.prime register))) := by
  unfold program
  rw [address_dispatch]
  rfl

@[simp] theorem program_multiply (source : Program 3 m) (row : Fin m) (register : Fin 3)
    (next : Fin m) (selected : source row = .inc register next)
    (cell : Fin (PrimeCode.prime register + 4)) :
    program source (multiply source row register next selected cell) =
      mapInstruction (mulTarget source row register next selected)
        (CounterMultiplication.program (PrimeCode.prime register) cell) := by
  unfold program
  rw [address_multiply]
  simp only [body]
  split
  next chosen => cases selected.symm.trans chosen
  next other target chosen =>
    rcases Instruction.inc.inj (selected.symm.trans chosen) with ⟨rfl, rfl⟩
    rfl
  next other zero nonzero chosen => cases selected.symm.trans chosen

@[simp] theorem program_probe (source : Program 3 m) (row : Fin m) (register : Fin 3)
    (zero nonzero : Fin m) (selected : source row = .dec register zero nonzero)
    (cell : Fin (CounterPrimeProbe.size (PrimeCode.prime register))) :
    program source (probe source row register zero nonzero selected cell) =
      mapInstruction (probeTarget source row register zero nonzero selected)
        (CounterPrimeProbe.program (PrimeCode.prime register) cell) := by
  unfold program
  rw [address_probe]
  simp only [body]
  split
  next chosen => cases selected.symm.trans chosen
  next other target chosen => cases selected.symm.trans chosen
  next other z nz chosen =>
    rcases Instruction.dec.inj (selected.symm.trans chosen) with ⟨rfl, rfl, rfl⟩
    rfl

def encode (source : Program 3 m) (state : Configuration 3 m) : Configuration 2 (size source) :=
  ⟨dispatch source state.pc, ![PrimeCode.encode state.counters, 0]⟩

theorem encode_injective (source : Program 3 m) : Function.Injective (encode source) := by
  intro first second same
  have positions := dispatch_injective source (congrArg Configuration.pc same)
  have values : PrimeCode.encode first.counters = PrimeCode.encode second.counters :=
    congrFun (congrArg Configuration.counters same) 0
  have registers := PrimeCode.encode_injective values
  cases first
  cases second
  simp_all

def Boundary (source : Program 3 m) (cell : Fin (size source)) : Prop :=
  ∃ row, cell = dispatch source row

@[simp] theorem encode_boundary (source : Program 3 m) (state : Configuration 3 m) :
    Boundary source (encode source state).pc := ⟨state.pc, rfl⟩

theorem multiply_not_boundary (source : Program 3 m) (row : Fin m) (register : Fin 3)
    (next : Fin m) (selected : source row = .inc register next)
    (cell : Fin (PrimeCode.prime register + 4)) :
    ¬ Boundary source (multiply source row register next selected cell) := by
  rintro ⟨other, same⟩
  have incompatible := (address source).injective same
  cases incompatible

theorem probe_not_boundary (source : Program 3 m) (row : Fin m) (register : Fin 3)
    (zero nonzero : Fin m) (selected : source row = .dec register zero nonzero)
    (cell : Fin (CounterPrimeProbe.size (PrimeCode.prime register))) :
    ¬ Boundary source (probe source row register zero nonzero selected cell) := by
  rintro ⟨other, same⟩
  have incompatible := (address source).injective same
  cases incompatible


/-- Only dispatch cells are source boundaries; the scratch counter is never inspected here. -/
def InternalStep (source : Program 3 m)
    (first last : Configuration 2 (size source)) : Prop :=
  step (program source) first = some last ∧ ¬ Boundary source first.pc

abbrev InternalReaches (source : Program 3 m) :=
  Relation.ReflTransGen (InternalStep source)

private theorem map_internal {k : ℕ} (source : Program 3 m) (oldProgram : Program 2 k)
    (rename : Fin k → Fin (size source))
    (agrees : ∀ cell, oldProgram cell ≠ .halt →
      program source (rename cell) = mapInstruction rename (oldProgram cell))
    (internal : ∀ cell, oldProgram cell ≠ .halt → ¬ Boundary source (rename cell))
    {first last : Configuration 2 k}
    (run : StateTransition.Reaches (step oldProgram) first last) :
    InternalReaches source (mapConfiguration rename first) (mapConfiguration rename last) := by
  induction run with
  | refl => exact Relation.ReflTransGen.refl
  | @tail middle last _ edge previous =>
      apply previous.tail
      constructor
      · exact step_map_live rename oldProgram (program source) agrees edge
      · apply internal
        intro halted
        simp [step, halted] at edge

private theorem mul_live (source : Program 3 m) (row : Fin m) (register : Fin 3)
    (next : Fin m) (selected : source row = .inc register next)
    (cell : Fin (PrimeCode.prime register + 4))
    (live : CounterMultiplication.program (PrimeCode.prime register) cell ≠ .halt) :
    program source (mulTarget source row register next selected cell) =
      mapInstruction (mulTarget source row register next selected)
        (CounterMultiplication.program (PrimeCode.prime register) cell) ∧
    ¬ Boundary source (mulTarget source row register next selected cell) := by
  have not_finish : cell ≠ CounterMultiplication.finish (PrimeCode.prime register) := by
    intro same
    subst cell
    exact live (CounterMultiplication.program_finish _)
  constructor
  · simp only [mulTarget, ite_eq_right not_finish, program_multiply]
  · simpa only [mulTarget, ite_eq_right not_finish] using
      multiply_not_boundary source row register next selected cell

private theorem probe_live (source : Program 3 m) (row : Fin m) (register : Fin 3)
    (zero nonzero : Fin m) (selected : source row = .dec register zero nonzero)
    (cell : Fin (CounterPrimeProbe.size (PrimeCode.prime register)))
    (live : CounterPrimeProbe.program (PrimeCode.prime register) cell ≠ .halt) :
    program source (probeTarget source row register zero nonzero selected cell) =
      mapInstruction (probeTarget source row register zero nonzero selected)
        (CounterPrimeProbe.program (PrimeCode.prime register) cell) ∧
    ¬ Boundary source (probeTarget source row register zero nonzero selected cell) := by
  have not_success : cell ≠ CounterPrimeProbe.success (PrimeCode.prime register) := by
    intro same
    subst cell
    exact live (CounterPrimeProbe.program_success _)
  have not_failure : cell ≠ CounterPrimeProbe.failure (PrimeCode.prime register) := by
    intro same
    subst cell
    exact live (CounterPrimeProbe.program_failure _)
  constructor
  · simp only [probeTarget, ite_eq_right not_success, ite_eq_right not_failure, program_probe]
  · simpa only [probeTarget, ite_eq_right not_success, ite_eq_right not_failure] using
      probe_not_boundary source row register zero nonzero selected cell

/-- Multiplication runs only through its allocated internal addresses, then returns to dispatch. -/
theorem multiply_reaches (source : Program 3 m) (row : Fin m) (register : Fin 3)
    (next : Fin m) (selected : source row = .inc register next) (value : ℕ) :
    InternalReaches source
      ⟨mulTarget source row register next selected 0, ![value, 0]⟩
      ⟨dispatch source next, ![PrimeCode.prime register * value, 0]⟩ := by
  have run := map_internal source (CounterMultiplication.program (PrimeCode.prime register))
    (mulTarget source row register next selected)
    (fun cell live => (mul_live source row register next selected cell live).1)
    (fun cell live => (mul_live source row register next selected cell live).2)
    (CounterMultiplication.reaches_result (PrimeCode.prime register) value)
  simpa only [mapConfiguration, CounterMultiplication.configuration, mulTarget_finish] using run

/-- A divisible code loses exactly one prime factor; all intermediate sources are internal. -/
theorem probe_success_reaches (source : Program 3 m) (row : Fin m) (register : Fin 3)
    (zero nonzero : Fin m) (selected : source row = .dec register zero nonzero)
    (value : ℕ) (divides : PrimeCode.prime register ∣ value) :
    InternalReaches source
      ⟨probeTarget source row register zero nonzero selected
        (CounterPrimeProbe.entry (PrimeCode.prime register)), ![value, 0]⟩
      ⟨dispatch source nonzero, ![value / PrimeCode.prime register, 0]⟩ := by
  have run := map_internal source (CounterPrimeProbe.program (PrimeCode.prime register))
    (probeTarget source row register zero nonzero selected)
    (fun cell live => (probe_live source row register zero nonzero selected cell live).1)
    (fun cell live => (probe_live source row register zero nonzero selected cell live).2)
    (CounterPrimeProbe.reaches_success (PrimeCode.prime register) value divides)
  simpa only [mapConfiguration, CounterPrimeProbe.configuration, probeTarget_success] using run

/-- A failed divisibility test restores the entire code before taking its zero branch. -/
theorem probe_failure_reaches (source : Program 3 m) (row : Fin m) (register : Fin 3)
    (zero nonzero : Fin m) (selected : source row = .dec register zero nonzero)
    (value : ℕ) (nondivides : ¬ PrimeCode.prime register ∣ value) :
    InternalReaches source
      ⟨probeTarget source row register zero nonzero selected
        (CounterPrimeProbe.entry (PrimeCode.prime register)), ![value, 0]⟩
      ⟨dispatch source zero, ![value, 0]⟩ := by
  have run := map_internal source (CounterPrimeProbe.program (PrimeCode.prime register))
    (probeTarget source row register zero nonzero selected)
    (fun cell live => (probe_live source row register zero nonzero selected cell live).1)
    (fun cell live => (probe_live source row register zero nonzero selected cell live).2)
    (CounterPrimeProbe.reaches_failure (PrimeCode.prime register) value nondivides)
  simpa only [mapConfiguration, CounterPrimeProbe.configuration, probeTarget_failure] using run


private theorem dispatch_inc (source : Program 3 m) (row : Fin m) (register : Fin 3)
    (next : Fin m) (selected : source row = .inc register next) :
    program source (dispatch source row) =
      .dec 1 (mulTarget source row register next selected 0)
        (mulTarget source row register next selected 0) := by
  rw [program_dispatch]
  split
  next chosen => cases selected.symm.trans chosen
  next other target chosen =>
    rcases Instruction.inc.inj (selected.symm.trans chosen) with ⟨rfl, rfl⟩
    rfl
  next other zero nonzero chosen => cases selected.symm.trans chosen

private theorem dispatch_dec (source : Program 3 m) (row : Fin m) (register : Fin 3)
    (zero nonzero : Fin m) (selected : source row = .dec register zero nonzero) :
    program source (dispatch source row) =
      .dec 1 (probeTarget source row register zero nonzero selected
        (CounterPrimeProbe.entry (PrimeCode.prime register)))
        (probeTarget source row register zero nonzero selected
          (CounterPrimeProbe.entry (PrimeCode.prime register))) := by
  rw [program_dispatch]
  split
  next chosen => cases selected.symm.trans chosen
  next other target chosen => cases selected.symm.trans chosen
  next other z nz chosen =>
    rcases Instruction.dec.inj (selected.symm.trans chosen) with ⟨rfl, rfl, rfl⟩
    rfl

private theorem step_none_iff {n k : ℕ} (table : Program n k) (state : Configuration n k) :
    step table state = none ↔ table state.pc = .halt := by
  unfold step
  cases instruction : table state.pc with
  | halt => simp
  | inc => simp
  | dec register zero nonzero => cases value : state.counters register <;> simp [value]

/-- Halting is tested at the encoded dispatch cell, independently of all arithmetic loops. -/
theorem halt_encode (source : Program 3 m) (state : Configuration 3 m) :
    step (program source) (encode source state) = none ↔ step source state = none := by
  rw [step_none_iff, step_none_iff]
  change program source (dispatch source state.pc) = .halt ↔ source state.pc = .halt
  rw [program_dispatch]
  split <;> simp_all

/-- One dispatch transition followed by a path containing no intermediate source boundary. -/
def FirstReturn (source : Program 3 m) (first last : Configuration 2 (size source)) : Prop :=
  ∃ after, step (program source) first = some after ∧ InternalReaches source after last

theorem internal_from_boundary (source : Program 3 m)
    {first last : Configuration 2 (size source)}
    (run : InternalReaches source first last) (boundary : Boundary source first.pc) :
    first = last := by
  rcases Relation.ReflTransGen.cases_head run with same | ⟨next, edge, _⟩
  · exact same
  · exact False.elim (edge.2 boundary)

theorem inc_firstReturn (source : Program 3 m) (state : Configuration 3 m)
    (register : Fin 3) (next : Fin m) (selected : source state.pc = .inc register next) :
    FirstReturn source (encode source state)
      (encode source ⟨next, Function.update state.counters register (state.counters register + 1)⟩) := by
  refine ⟨⟨mulTarget source state.pc register next selected 0,
    ![PrimeCode.encode state.counters, 0]⟩, ?_, ?_⟩
  · exact step_dec_zero (program source) (encode source state)
      (dispatch_inc source state.pc register next selected) rfl
  · simpa only [encode, PrimeCode.encode_increment] using
      multiply_reaches source state.pc register next selected (PrimeCode.encode state.counters)

theorem dec_zero_firstReturn (source : Program 3 m) (state : Configuration 3 m)
    (register : Fin 3) (zero nonzero : Fin m)
    (selected : source state.pc = .dec register zero nonzero) (value : state.counters register = 0) :
    FirstReturn source (encode source state) (encode source ⟨zero, state.counters⟩) := by
  refine ⟨⟨probeTarget source state.pc register zero nonzero selected
    (CounterPrimeProbe.entry (PrimeCode.prime register)),
    ![PrimeCode.encode state.counters, 0]⟩, ?_, ?_⟩
  · exact step_dec_zero (program source) (encode source state)
      (dispatch_dec source state.pc register zero nonzero selected) rfl
  · simpa only [encode] using probe_failure_reaches source state.pc register zero nonzero selected
      (PrimeCode.encode state.counters) ((PrimeCode.register_zero_iff state.counters register).mp value)

theorem dec_succ_firstReturn (source : Program 3 m) (state : Configuration 3 m)
    (register : Fin 3) (zero nonzero : Fin m)
    (selected : source state.pc = .dec register zero nonzero)
    (value : ℕ) (counter : state.counters register = value + 1) :
    FirstReturn source (encode source state)
      (encode source ⟨nonzero, Function.update state.counters register value⟩) := by
  have positive : state.counters register ≠ 0 := by omega
  have code := PrimeCode.encode_decrement state.counters register positive
  have previous : state.counters register - 1 = value := by omega
  rw [previous] at code
  refine ⟨⟨probeTarget source state.pc register zero nonzero selected
    (CounterPrimeProbe.entry (PrimeCode.prime register)),
    ![PrimeCode.encode state.counters, 0]⟩, ?_, ?_⟩
  · exact step_dec_zero (program source) (encode source state)
      (dispatch_dec source state.pc register zero nonzero selected) rfl
  · simpa only [encode, code] using probe_success_reaches source state.pc register zero nonzero selected
      (PrimeCode.encode state.counters) ((PrimeCode.prime_dvd_encode_iff state.counters register).mpr positive)

/-- A source step is exactly a positive first return to the finite set of dispatch cells. -/
theorem step_firstReturn (source : Program 3 m) {first last : Configuration 3 m}
    (transition : step source first = some last) :
    FirstReturn source (encode source first) (encode source last) := by
  cases instruction : source first.pc with
  | halt => simp [step, instruction] at transition
  | inc register next =>
      have destination : (⟨next, Function.update first.counters register (first.counters register + 1)⟩ :
          Configuration 3 m) = last := by
        simpa only [step_inc source first instruction, Option.some.injEq] using transition
      subst last
      exact inc_firstReturn source first register next instruction
  | dec register zero nonzero =>
      cases counter : first.counters register with
      | zero =>
          have destination : (⟨zero, first.counters⟩ : Configuration 3 m) = last := by
            simpa only [step_dec_zero source first instruction counter, Option.some.injEq] using transition
          subst last
          exact dec_zero_firstReturn source first register zero nonzero instruction counter
      | succ value =>
          have destination : (⟨nonzero, Function.update first.counters register value⟩ :
              Configuration 3 m) = last := by
            simpa only [step_dec_succ source first instruction counter, Option.some.injEq] using transition
          subst last
          exact dec_succ_firstReturn source first register zero nonzero instruction value counter

theorem firstReturn_positive (source : Program 3 m)
    {first last : Configuration 2 (size source)} (run : FirstReturn source first last) :
    StateTransition.Reaches₁ (step (program source)) first last := by
  rcases run with ⟨after, initial, rest⟩
  apply Relation.TransGen.head'
    (r := fun current next => next ∈ step (program source) current) initial
  induction rest with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ edge previous => exact previous.tail edge.1

/-- The finite compiler preserves source execution and halting from every encoded configuration. -/
theorem respects (source : Program 3 m) :
    StateTransition.Respects (step source) (step (program source))
      (fun original compiled => encode source original = compiled) := by
  apply StateTransition.fun_respects.mpr
  intro state
  cases transition : step source state with
  | none =>
      change step (program source) (encode source state) = none
      exact (halt_encode source state).mpr transition
  | some next => exact firstReturn_positive source (step_firstReturn source transition)

/-- Complete configurations, termination, and divergence are preserved by prime compression. -/
theorem eval_encode (source : Program 3 m) (state : Configuration 3 m) :
    eval (program source) (encode source state) = encode source <$> eval source state :=
  StateTransition.tr_eval' (step source) (step (program source))
    (encode source) (respects source) state

theorem eval_dom_encode (source : Program 3 m) (state : Configuration 3 m) :
    (eval (program source) (encode source state)).Dom ↔ (eval source state).Dom := by
  rw [eval_encode]
  rfl

theorem divergence_iff (source : Program 3 m) (state : Configuration 3 m) :
    ¬ (eval (program source) (encode source state)).Dom ↔ ¬ (eval source state).Dom :=
  not_congr (eval_dom_encode source state)

end Monodromy.Counter.Compression

namespace Monodromy.Counter.EntryDispatch

variable {a m : ℕ}

/-- Prefix addresses contain only jumps through an already-zero workspace counter. -/
def program (source : Program 2 m) (entries : Fin a → Fin m) : Program 2 (a + m) :=
  Fin.addCases
    (fun symbol => .dec 1 (Fin.natAdd a (entries symbol)) (Fin.natAdd a (entries symbol)))
    (fun cell => mapInstruction (Fin.natAdd a) (source cell))

def entryState (symbol : Fin a) (registers : Fin 2 → ℕ) : Configuration 2 (a + m) :=
  ⟨Fin.castAdd m symbol, registers⟩

@[simp] theorem program_prefix (source : Program 2 m) (entries : Fin a → Fin m)
    (symbol : Fin a) :
    program source entries (Fin.castAdd m symbol) =
      .dec 1 (Fin.natAdd a (entries symbol)) (Fin.natAdd a (entries symbol)) := by
  simp [program]

@[simp] theorem program_body (source : Program 2 m) (entries : Fin a → Fin m) (cell : Fin m) :
    program source entries (Fin.natAdd a cell) = mapInstruction (Fin.natAdd a) (source cell) := by
  simp [program]

theorem address_injective : Function.Injective (Fin.natAdd a : Fin m → Fin (a + m)) := by
  intro first second same
  apply Fin.ext
  have values := congrArg Fin.val same
  simp only [Fin.val_natAdd] at values
  omega

theorem body_injective : Function.Injective (mapConfiguration (n := 2) (Fin.natAdd a) :
    Configuration 2 m → Configuration 2 (a + m)) :=
  mapConfiguration_injective (Fin.natAdd a) address_injective

theorem prefix_ne_body (symbol : Fin a) (cell : Fin m) :
    Fin.castAdd m symbol ≠ Fin.natAdd a cell := by
  intro same
  have values := congrArg Fin.val same
  simp only [Fin.val_castAdd, Fin.val_natAdd] at values
  omega

/-- One actual source instruction enters the selected body address without changing storage. -/
theorem prefix_step (source : Program 2 m) (entries : Fin a → Fin m)
    (symbol : Fin a) (registers : Fin 2 → ℕ) (workspace : registers 1 = 0) :
    step (program source entries) (entryState symbol registers) =
      some (mapConfiguration (Fin.natAdd a) ⟨entries symbol, registers⟩) := by
  simp [step, entryState, workspace, mapConfiguration]

/-- Every relocated body preserves its complete partial execution. -/
theorem eval_body (source : Program 2 m) (entries : Fin a → Fin m)
    (state : Configuration 2 m) :
    eval (program source entries) (mapConfiguration (Fin.natAdd a) state) =
      mapConfiguration (Fin.natAdd a) <$> eval source state :=
  eval_map (Fin.natAdd a) source (program source entries)
    (fun cell => program_body source entries cell) state

/-- Static entry dispatch preserves complete results, termination, and divergence. -/
theorem eval_prefix (source : Program 2 m) (entries : Fin a → Fin m)
    (symbol : Fin a) (registers : Fin 2 → ℕ) (workspace : registers 1 = 0) :
    eval (program source entries) (entryState symbol registers) =
      mapConfiguration (Fin.natAdd a) <$> eval source ⟨entries symbol, registers⟩ := by
  have run : StateTransition.Reaches (step (program source entries)) (entryState symbol registers)
      (mapConfiguration (Fin.natAdd a) ⟨entries symbol, registers⟩) :=
    Relation.ReflTransGen.single (prefix_step source entries symbol registers workspace)
  exact (StateTransition.reaches_eval run).trans (eval_body source entries _)

theorem eval_prefix_dom (source : Program 2 m) (entries : Fin a → Fin m)
    (symbol : Fin a) (registers : Fin 2 → ℕ) (workspace : registers 1 = 0) :
    (eval (program source entries) (entryState symbol registers)).Dom ↔
      (eval source ⟨entries symbol, registers⟩).Dom := by
  rw [eval_prefix source entries symbol registers workspace]
  rfl

end Monodromy.Counter.EntryDispatch
