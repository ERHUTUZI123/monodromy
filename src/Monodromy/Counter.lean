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

/-- A finite family of distinct primes represents independent natural registers. -/
structure Basis (n : ℕ) where
  prime : Fin n → ℕ
  isPrime : ∀ index, (prime index).Prime
  distinct : Function.Injective prime

namespace Basis

variable {n : ℕ} (basis : Basis n)

def encode (registers : Fin n → ℕ) : ℕ := ∏ index, basis.prime index ^ registers index

def decode (code : ℕ) : Fin n → ℕ := fun index => code.factorization (basis.prime index)

theorem encode_positive (registers : Fin n → ℕ) : 0 < basis.encode registers := by
  apply Finset.prod_pos
  intro index _
  exact pow_pos (basis.isPrime index).pos _

/-- Prime valuations recover every register, uniformly in the finite dimension. -/
theorem factorization_encode (registers : Fin n → ℕ) (index : Fin n) :
    (basis.encode registers).factorization (basis.prime index) = registers index := by
  unfold encode
  rw [Nat.factorization_prod_apply (fun other _ => pow_ne_zero _ (basis.isPrime other).ne_zero)]
  rw [Finset.sum_eq_single index]
  · exact Nat.factorization_pow_self (basis.isPrime index)
  · intro other _ different
    rw [(basis.isPrime other).factorization_pow]
    exact Finsupp.single_eq_of_ne' (basis.distinct.ne different)
  · simp

theorem decode_encode : Function.LeftInverse basis.decode basis.encode := by
  intro registers
  funext index
  exact basis.factorization_encode registers index

theorem encode_injective : Function.Injective basis.encode := basis.decode_encode.injective

@[simp] theorem encode_zero : basis.encode (fun _ => 0) = 1 := by simp [encode]

theorem encode_increment (registers : Fin n → ℕ) (index : Fin n) :
    basis.encode (Function.update registers index (registers index + 1)) =
      basis.prime index * basis.encode registers := by
  unfold encode
  rw [Fintype.prod_eq_mul_prod_compl index, Fintype.prod_eq_mul_prod_compl index]
  rw [Function.update_self, pow_succ]
  have unchanged :
      (∏ other ∈ ({index}ᶜ : Finset (Fin n)), basis.prime other ^
        Function.update registers index (registers index + 1) other) =
      ∏ other ∈ ({index}ᶜ : Finset (Fin n)), basis.prime other ^ registers other := by
    apply Finset.prod_congr rfl
    intro other present
    have different : other ≠ index := by simpa using present
    rw [Function.update_of_ne different]
  rw [unchanged]
  ac_rfl

theorem prime_dvd_encode_iff (registers : Fin n → ℕ) (index : Fin n) :
    basis.prime index ∣ basis.encode registers ↔ registers index ≠ 0 := by
  rw [(basis.isPrime index).dvd_iff_one_le_factorization (basis.encode_positive registers).ne',
    basis.factorization_encode]
  omega

theorem register_zero_iff (registers : Fin n → ℕ) (index : Fin n) :
    registers index = 0 ↔ ¬ basis.prime index ∣ basis.encode registers := by
  rw [basis.prime_dvd_encode_iff]
  omega

theorem remainder_zero_iff (registers : Fin n → ℕ) (index : Fin n) :
    basis.encode registers % basis.prime index = 0 ↔ registers index ≠ 0 := by
  rw [← Nat.dvd_iff_mod_eq_zero, basis.prime_dvd_encode_iff]

theorem encode_decrement (registers : Fin n → ℕ) (index : Fin n)
    (nonzero : registers index ≠ 0) :
    basis.encode (Function.update registers index (registers index - 1)) =
      basis.encode registers / basis.prime index := by
  let previous := Function.update registers index (registers index - 1)
  have restores : Function.update previous index (previous index + 1) = registers := by
    funext other
    by_cases same : other = index
    · subst other
      simp only [previous, Function.update_self]
      omega
    · simp [previous, same]
  have restores_code := basis.encode_increment previous index
  rw [restores] at restores_code
  change basis.encode previous = basis.encode registers / basis.prime index
  rw [restores_code, Nat.mul_div_cancel_left _ (basis.isPrime index).pos]

end Basis

/-- A classical proof-side encoding of three source registers, using fixed distinct primes. -/
def prime (index : Fin 3) : ℕ := if index = 0 then 2 else if index = 1 then 3 else 5

def encode (registers : Fin 3 → ℕ) : ℕ :=
  2 ^ registers 0 * 3 ^ registers 1 * 5 ^ registers 2

theorem prime_prime (index : Fin 3) : (prime index).Prime := by
  fin_cases index <;> norm_num [prime] <;> decide

def decode (code : ℕ) : Fin 3 → ℕ := fun index => code.factorization (prime index)

/-- The existing three-register code is the specialization with primes 2, 3 and 5. -/
def three : Basis 3 where
  prime := prime
  isPrime := prime_prime
  distinct := by
    intro first second same
    fin_cases first <;> fin_cases second <;> simp_all [prime]

@[simp] theorem three_prime (index : Fin 3) : three.prime index = prime index := rfl

@[simp] theorem three_decode (code : ℕ) : three.decode code = decode code := rfl

theorem three_encode (registers : Fin 3 → ℕ) : three.encode registers = encode registers := by
  change (∏ index : Fin 3, prime index ^ registers index) =
    2 ^ registers 0 * 3 ^ registers 1 * 5 ^ registers 2
  simp [Fin.prod_univ_succ, prime, mul_assoc]

theorem encode_positive (registers : Fin 3 → ℕ) : 0 < encode registers := by
  simpa only [three_encode] using three.encode_positive registers

/-- Prime valuations recover each source register exactly. -/
theorem factorization_encode (registers : Fin 3 → ℕ) (index : Fin 3) :
    (encode registers).factorization (prime index) = registers index := by
  simpa only [three_encode, three_prime] using three.factorization_encode registers index

theorem decode_encode : Function.LeftInverse decode encode := by
  intro registers
  simpa only [three_encode, three_decode] using three.decode_encode registers

theorem encode_injective : Function.Injective encode := decode_encode.injective

@[simp] theorem encode_zero : encode (fun _ => 0) = 1 := by
  simpa only [three_encode] using three.encode_zero

/-- Incrementing a source register multiplies the single code by its fixed prime. -/
theorem encode_increment (registers : Fin 3 → ℕ) (index : Fin 3) :
    encode (Function.update registers index (registers index + 1)) = prime index * encode registers := by
  simpa only [three_encode, three_prime] using three.encode_increment registers index

/-- Divisibility is precisely the nonzero test for the corresponding source register. -/
theorem prime_dvd_encode_iff (registers : Fin 3 → ℕ) (index : Fin 3) :
    prime index ∣ encode registers ↔ registers index ≠ 0 := by
  simpa only [three_encode, three_prime] using three.prime_dvd_encode_iff registers index

theorem register_zero_iff (registers : Fin 3 → ℕ) (index : Fin 3) :
    registers index = 0 ↔ ¬ prime index ∣ encode registers := by
  simpa only [three_encode, three_prime] using three.register_zero_iff registers index

theorem remainder_zero_iff (registers : Fin 3 → ℕ) (index : Fin 3) :
    encode registers % prime index = 0 ↔ registers index ≠ 0 := by
  simpa only [three_encode, three_prime] using three.remainder_zero_iff registers index

/-- A nonzero source decrement is exact division of the positive code. -/
theorem encode_decrement (registers : Fin 3 → ℕ) (index : Fin 3)
    (nonzero : registers index ≠ 0) :
    encode (Function.update registers index (registers index - 1)) = encode registers / prime index := by
  simpa only [three_encode, three_prime] using three.encode_decrement registers index nonzero

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

/-!
## Locally reversible counter tables
-/

namespace Monodromy.Counter.Reversible

inductive Action (n : ℕ)
  | shift (reg : Fin n) (amount : ℤ)
  | test (reg : Fin n) (atZero : Bool)
  deriving DecidableEq

abbrev State (n q : ℕ) := Fin q × (Fin n → ℤ)

structure Edge (n q : ℕ) where
  source : Fin q
  target : Fin q
  action : Action n
  deriving DecidableEq

abbrev Table (n q e : ℕ) := Fin e → Edge n q

namespace Action

variable {n : ℕ}

def enabled : Action n → (Fin n → ℤ) → Prop
  | .shift _ _, _ => True
  | .test reg atZero, values => (values reg = 0) ↔ atZero = true

instance (action : Action n) (values : Fin n → ℤ) : Decidable (enabled action values) := by
  cases action <;> simp only [enabled] <;> infer_instance

def apply : Action n → (Fin n → ℤ) → (Fin n → ℤ)
  | .shift reg amount, values => Function.update values reg (values reg + amount)
  | .test _ _, values => values

/-- The elementary source family required by reversible counter compression. -/
def UnitShift : Action n → Prop
  | .shift _ amount => amount = 1 ∨ amount = -1
  | .test _ _ => True

/-- The only two different alternatives allowed at a common port. -/
def Compatible : Action n → Action n → Prop
  | .test first firstZero, .test second secondZero => first = second ∧ firstZero ≠ secondZero
  | _, _ => False

theorem Compatible.symm {first second : Action n} (compatible : Compatible first second) :
    Compatible second first := by
  cases first <;> cases second <;> simp_all [Compatible, eq_comm]

theorem Compatible.not_both {first second : Action n} (compatible : Compatible first second)
    (values : Fin n → ℤ) : ¬ (enabled first values ∧ enabled second values) := by
  cases first <;> cases second <;> simp only [Compatible] at compatible
  rcases compatible with ⟨rfl, different⟩
  rename_i firstZero secondZero
  cases firstZero <;> cases secondZero <;> simp_all [enabled]

theorem apply_injective (action : Action n) : Function.Injective action.apply := by
  cases action with
  | test => exact Function.injective_id
  | shift reg amount =>
      intro first second same
      funext index
      by_cases selected : index = reg
      · subst index
        have at_register := congrFun same reg
        simpa only [apply, Function.update_self, Int.add_left_inj] using at_register
      · have elsewhere := congrFun same index
        simpa only [apply, Function.update_of_ne selected] using elsewhere

/-- Complementary tests preserve the values on which their guards disagree. -/
theorem Compatible.not_same_result {first second : Action n}
    (compatible : Compatible first second) {left right : Fin n → ℤ}
    (left_enabled : enabled first left) (right_enabled : enabled second right) :
    first.apply left ≠ second.apply right := by
  cases first <;> cases second <;> simp only [Compatible] at compatible
  rcases compatible with ⟨rfl, different⟩
  intro same
  change left = right at same
  subst right
  exact (Compatible.not_both (show Compatible (.test _ _) (.test _ _) from ⟨rfl, different⟩)
    left) ⟨left_enabled, right_enabled⟩

end Action

variable {n q e : ℕ}

namespace Edge

def enabled (edge : Edge n q) (state : State n q) : Prop :=
  edge.source = state.1 ∧ edge.action.enabled state.2

instance (edge : Edge n q) (state : State n q) : Decidable (edge.enabled state) :=
  inferInstanceAs (Decidable (edge.source = state.1 ∧ edge.action.enabled state.2))

def execute (edge : Edge n q) (state : State n q) : State n q :=
  (edge.target, edge.action.apply state.2)

end Edge

/-- Alternatives at the same source port have disjoint guards. -/
def Deterministic (table : Table n q e) : Prop :=
  ∀ first second, first ≠ second → (table first).source = (table second).source →
    Action.Compatible (table first).action (table second).action

/-- Alternatives at the same target port have disjoint, unchanged test data. -/
def TargetCompatible (table : Table n q e) : Prop :=
  ∀ first second, first ≠ second → (table first).target = (table second).target →
    Action.Compatible (table first).action (table second).action

/-- Every live address can move at every integer register valuation. -/
def Complete (table : Table n q e) : Prop :=
  ∀ state : State n q, (∃ index, (table index).source = state.1) →
    ∃ index, (table index).enabled state

/-- Relational source semantics, before selecting a finite edge index. -/
def StepRel (table : Table n q e) (first last : State n q) : Prop :=
  ∃ index, (table index).enabled first ∧ (table index).execute first = last

theorem enabled_index_unique (table : Table n q e) (deterministic : Deterministic table)
    {first second : Fin e} {state : State n q}
    (first_enabled : (table first).enabled state) (second_enabled : (table second).enabled state) :
    first = second := by
  by_contra different
  have compatible := deterministic first second different (first_enabled.1.trans second_enabled.1.symm)
  exact (compatible.not_both state.2) ⟨first_enabled.2, second_enabled.2⟩

theorem StepRel.deterministic (table : Table n q e) (deterministic : Deterministic table)
    {initial first second : State n q} (left : StepRel table initial first)
    (right : StepRel table initial second) : first = second := by
  obtain ⟨left_index, left_enabled, rfl⟩ := left
  obtain ⟨right_index, right_enabled, rfl⟩ := right
  rw [enabled_index_unique table deterministic left_enabled right_enabled]

theorem StepRel.backward_unique (table : Table n q e) (reversible : TargetCompatible table)
    {first second final : State n q} (left : StepRel table first final)
    (right : StepRel table second final) : first = second := by
  obtain ⟨left_index, left_enabled, left_result⟩ := left
  obtain ⟨right_index, right_enabled, right_result⟩ := right
  have same_result : (table left_index).execute first = (table right_index).execute second :=
    left_result.trans right_result.symm
  have same_target : (table left_index).target = (table right_index).target :=
    congrArg Prod.fst same_result
  have same_values : (table left_index).action.apply first.2 =
      (table right_index).action.apply second.2 := congrArg Prod.snd same_result
  by_cases same_index : left_index = right_index
  · subst right_index
    apply Prod.ext
    · exact left_enabled.1.symm.trans right_enabled.1
    · exact Action.apply_injective _ same_values
  · exact False.elim ((reversible left_index right_index same_index same_target).not_same_result
      left_enabled.2 right_enabled.2 same_values)

/-- Bounded finite search; this source executor is independent of native geometry. -/
def step (table : Table n q e) (state : State n q) : Option (State n q) :=
  if available : ∃ index, (table index).enabled state then
    some ((table (Fin.find (fun index => (table index).enabled state) available)).execute state)
  else none

theorem step_iff (table : Table n q e) (deterministic : Deterministic table)
    {first last : State n q} : step table first = some last ↔ StepRel table first last := by
  unfold step
  split_ifs with available
  · constructor
    · intro result
      exact ⟨_, Fin.find_spec available, Option.some.inj result⟩
    · intro result
      exact congrArg some (StepRel.deterministic table deterministic
        ⟨_, Fin.find_spec available, rfl⟩ result)
  · simp only [false_iff]
    rintro ⟨index, enabled, _⟩
    exact available ⟨index, enabled⟩

theorem step_some_injective (table : Table n q e) (deterministic : Deterministic table)
    (reversible : TargetCompatible table) {first second final : State n q}
    (left : step table first = some final) (right : step table second = some final) : first = second :=
  StepRel.backward_unique table reversible ((step_iff table deterministic).mp left)
    ((step_iff table deterministic).mp right)

theorem step_none_iff (table : Table n q e) (state : State n q) :
    step table state = none ↔ ¬ ∃ index, (table index).enabled state := by
  unfold step
  split_ifs <;> simp_all

/-- Completeness makes halting a static source-address property. -/
theorem step_none_iff_no_outgoing (table : Table n q e) (complete : Complete table)
    (state : State n q) : step table state = none ↔ ¬ ∃ index, (table index).source = state.1 := by
  rw [step_none_iff]
  constructor
  · intro halted outgoing
    exact halted (complete state outgoing)
  · rintro halted ⟨index, enabled⟩
    exact halted ⟨index, enabled.1⟩

namespace Action

def IsShift : Action n → Prop
  | .shift _ _ => True
  | .test _ _ => False

instance (action : Action n) : Decidable action.IsShift := by
  cases action <;> simp only [IsShift] <;> infer_instance

instance (first second : Action n) : Decidable (Compatible first second) := by
  cases first <;> cases second <;> simp only [Compatible] <;> infer_instance

theorem Compatible.one_enabled {first second : Action n}
    (compatible : Compatible first second) (values : Fin n → ℤ) :
    enabled first values ∨ enabled second values := by
  cases first with
  | shift => simp [Compatible] at compatible
  | test register firstZero =>
      cases second with
      | shift => simp [Compatible] at compatible
      | test other secondZero =>
          rcases compatible with ⟨rfl, different⟩
          by_cases zero : values register = 0 <;>
            cases firstZero <;> cases secondZero <;> simp_all [enabled]

theorem test_disabled (register : Fin n) (atZero : Bool) :
    ∃ values : Fin n → ℤ, ¬ enabled (.test register atZero) values := by
  cases atZero
  · exact ⟨fun _ => 0, by simp [enabled]⟩
  · exact ⟨fun _ => 1, by simp [enabled]⟩

end Action

/-- A live port is covered by one unconditional shift or two complementary tests. -/
def CoveredAt (table : Table n q e) (position : Fin q) : Prop :=
  (¬ ∃ index, (table index).source = position) ∨
  (∃ index, (table index).source = position ∧ (table index).action.IsShift) ∨
  ∃ first second, (table first).source = position ∧ (table second).source = position ∧
    Action.Compatible (table first).action (table second).action

instance (table : Table n q e) (position : Fin q) : Decidable (CoveredAt table position) :=
  inferInstanceAs (Decidable (
    (¬ ∃ index, (table index).source = position) ∨
    (∃ index, (table index).source = position ∧ (table index).action.IsShift) ∨
    ∃ first second, (table first).source = position ∧ (table second).source = position ∧
      Action.Compatible (table first).action (table second).action))

theorem complete_of_covered (table : Table n q e)
    (covered : ∀ position, CoveredAt table position) : Complete table := by
  intro state outgoing
  rcases covered state.1 with empty | ⟨index, source, shift⟩ | ⟨first, second, fs, ss, compatible⟩
  · exact False.elim (empty outgoing)
  · refine ⟨index, source, ?_⟩
    cases action : (table index).action with
    | shift => trivial
    | test => simp [Action.IsShift, action] at shift
  · rcases compatible.one_enabled state.2 with first_enabled | second_enabled
    · exact ⟨first, fs, first_enabled⟩
    · exact ⟨second, ss, second_enabled⟩

theorem covered_of_complete (table : Table n q e) (deterministic : Deterministic table)
    (complete : Complete table) : ∀ position, CoveredAt table position := by
  intro position
  by_cases outgoing : ∃ index, (table index).source = position
  · obtain ⟨index, source⟩ := outgoing
    cases action : (table index).action with
    | shift register amount =>
        exact Or.inr (Or.inl ⟨index, source, by simp [Action.IsShift, action]⟩)
    | test register atZero =>
        obtain ⟨values, disabled⟩ := Action.test_disabled register atZero
        obtain ⟨other, other_source, other_enabled⟩ :=
          complete (position, values) ⟨index, source⟩
        have different : index ≠ other := by
          intro same
          subst other
          exact disabled (action ▸ other_enabled)
        exact Or.inr (Or.inr ⟨index, other, source, other_source,
          deterministic index other different (source.trans other_source.symm)⟩)
  · exact Or.inl outgoing

/-- Semantic completeness of a deterministic table has a finite syntactic test. -/
theorem complete_iff_covered (table : Table n q e) (deterministic : Deterministic table) :
    Complete table ↔ ∀ position, CoveredAt table position :=
  ⟨covered_of_complete table deterministic, complete_of_covered table⟩

/-- All quantified positions and edge indices in the coverage criterion are finite. -/
def decideComplete (table : Table n q e) (deterministic : Deterministic table) :
    Decidable (Complete table) :=
  decidable_of_iff (∀ position, CoveredAt table position)
    (complete_iff_covered table deterministic).symm

/-- Complete partial execution retains the final halted source configuration. -/
def eval (table : Table n q e) : State n q → Part (State n q) :=
  StateTransition.eval (step table)

/-- Every syntactically live address has an enabled edge on the stated invariant. -/
def CompleteOn (table : Table n q e) (invariant : State n q → Prop) : Prop :=
  ∀ state, invariant state → (∃ edge, (table edge).source = state.1) →
    ∃ edge, (table edge).enabled state

/-- Every defined source step preserves the stated invariant. -/
def Stable (table : Table n q e) (invariant : State n q → Prop) : Prop :=
  ∀ ⦃first last⦄, invariant first → step table first = some last → invariant last

theorem Complete.completeOn {table : Table n q e} (complete : Complete table)
    (invariant : State n q → Prop) : CompleteOn table invariant :=
  fun state _ outgoing => complete state outgoing

theorem step_none_iff_no_outgoing_on (table : Table n q e) (invariant : State n q → Prop)
    (complete : CompleteOn table invariant) (state : State n q) (valid : invariant state) :
    step table state = none ↔ ¬ ∃ edge, (table edge).source = state.1 := by
  rw [step_none_iff]
  constructor
  · intro halted outgoing
    exact halted (complete state valid outgoing)
  · rintro halted ⟨edge, enabled⟩
    exact halted ⟨edge, enabled.1⟩

def reverseAction : Action n → Action n
  | .shift register amount => .shift register (-amount)
  | .test register atZero => .test register atZero

@[simp] theorem reverseAction_involutive (action : Action n) :
    reverseAction (reverseAction action) = action := by
  cases action <;> simp [reverseAction]

@[simp] theorem reverseAction_enabled (action : Action n) (values : Fin n → ℤ) :
    (reverseAction action).enabled values ↔ action.enabled values := by
  cases action <;> rfl

@[simp] theorem reverseAction_apply (action : Action n) (values : Fin n → ℤ) :
    (reverseAction action).apply (action.apply values) = values := by
  cases action with
  | test => rfl
  | shift register amount =>
      funext index
      by_cases selected : index = register
      · subst index
        simp [reverseAction, Action.apply]
      · simp [reverseAction, Action.apply, Function.update_of_ne selected]

@[simp] theorem reverseAction_enabled_apply (action : Action n) (values : Fin n → ℤ) :
    (reverseAction action).enabled (action.apply values) ↔ action.enabled values := by
  cases action <;> rfl

@[simp] theorem reverseAction_compatible (first second : Action n) :
    Action.Compatible (reverseAction first) (reverseAction second) ↔
      Action.Compatible first second := by
  cases first <;> cases second <;> rfl

namespace Action

@[simp] theorem unitShift_reverse (action : Action n) :
    UnitShift (reverseAction action) ↔ UnitShift action := by
  cases action with
  | test => rfl
  | shift register amount =>
      change (-amount = 1 ∨ -amount = -1) ↔ amount = 1 ∨ amount = -1
      omega

end Action

def reverseEdge (edge : Edge n q) : Edge n q :=
  ⟨edge.target, edge.source, reverseAction edge.action⟩

@[simp] theorem reverseEdge_involutive (edge : Edge n q) :
    reverseEdge (reverseEdge edge) = edge := by
  cases edge
  simp [reverseEdge]

def reverseTable (table : Table n q e) : Table n q e :=
  fun index => reverseEdge (table index)

@[simp] theorem reverseTable_involutive (table : Table n q e) :
    reverseTable (reverseTable table) = table := by
  funext index
  exact reverseEdge_involutive _

theorem reverseTable_deterministic (table : Table n q e) (compatible : TargetCompatible table) :
    Deterministic (reverseTable table) := by
  intro first second different same
  exact (reverseAction_compatible _ _).mpr (compatible first second different same)

theorem reverseTable_targetCompatible (table : Table n q e) (deterministic : Deterministic table) :
    TargetCompatible (reverseTable table) := by
  intro first second different same
  exact (reverseAction_compatible _ _).mpr (deterministic first second different same)

/-- Reversing an enabled edge retraces precisely the same values and control addresses. -/
theorem StepRel.reverse {table : Table n q e} {first last : State n q}
    (transition : StepRel table first last) : StepRel (reverseTable table) last first := by
  obtain ⟨index, enabled, rfl⟩ := transition
  refine ⟨index, ⟨rfl, ?_⟩, ?_⟩
  · exact (reverseAction_enabled_apply _ _).mpr enabled.2
  · apply Prod.ext
    · exact enabled.1
    · exact reverseAction_apply _ _

theorem StepRel_reverse_iff (table : Table n q e) (first last : State n q) :
    StepRel table first last ↔ StepRel (reverseTable table) last first := by
  constructor
  · exact StepRel.reverse
  · intro transition
    simpa only [reverseTable_involutive] using transition.reverse

/-- The bounded finite edge search realizes graph reversal exactly. -/
theorem step_reverse_iff (table : Table n q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) (first last : State n q) :
    step table first = some last ↔ step (reverseTable table) last = some first := by
  rw [step_iff table deterministic,
    step_iff (reverseTable table) (reverseTable_deterministic table compatible), StepRel_reverse_iff]

/-- Every actual finite execution is traversable in reverse by the reversed static table. -/
theorem reaches_reverse (table : Table n q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) {first last : State n q}
    (run : StateTransition.Reaches (step table) first last) :
    StateTransition.Reaches (step (reverseTable table)) last first := by
  apply Relation.ReflTransGen.mono (fun before after transition =>
    (step_reverse_iff table deterministic compatible after before).mp transition)
  exact Relation.ReflTransGen.swap last first run

end Monodromy.Counter.Reversible

/-!
## Static finite port matchings
-/

namespace Monodromy.ReversiblePorts

variable {q e : ℕ}

/-- This finite lookup depends only on the static table and a finite vertex. -/
def mate (owner : Fin e → Fin q) (active : Fin e → Bool) (vertex : Fin q) : Option (Fin e) :=
  if found : ∃ edge, active edge = true ∧ owner edge = vertex then
    some (Fin.find (fun edge => active edge = true ∧ owner edge = vertex) found)
  else none

def Matching (owner : Fin e → Fin q) (active : Fin e → Bool) : Prop :=
  ∀ first second, active first = true → active second = true →
    owner first = owner second → first = second

theorem mate_some (owner : Fin e → Fin q) (active : Fin e → Bool)
    (matching : Matching owner active) (vertex : Fin q) (edge : Fin e) :
    mate owner active vertex = some edge ↔ active edge = true ∧ owner edge = vertex := by
  unfold mate
  split_ifs with found
  · constructor
    · intro same
      have chosen := Fin.find_spec found
      have equal_index := Option.some.inj same
      simpa only [equal_index] using chosen
    · intro selected
      apply congrArg some
      have chosen := Fin.find_spec found
      exact matching _ _ chosen.1 selected.1 (chosen.2.trans selected.2.symm)
  · constructor
    · simp
    · intro selected
      exact (found ⟨edge, selected⟩).elim

def exchange (owner : Fin e → Fin q) (active : Fin e → Bool) : Fin q ⊕ Fin e → Fin q ⊕ Fin e
  | .inl vertex => (mate owner active vertex).elim (.inl vertex) Sum.inr
  | .inr edge => if active edge then .inl (owner edge) else .inr edge

theorem exchange_involutive (owner : Fin e → Fin q) (active : Fin e → Bool)
    (matching : Matching owner active) : Function.Involutive (exchange owner active) := by
  intro port
  cases port with
  | inl vertex =>
      cases chosen : mate owner active vertex with
      | none => simp [exchange, chosen]
      | some edge =>
          obtain ⟨enabled, endpoint⟩ := (mate_some owner active matching vertex edge).mp chosen
          simp [exchange, chosen, enabled, endpoint]
  | inr edge =>
      cases selected : active edge with
      | false => simp [exchange, selected]
      | true =>
          have chosen := (mate_some owner active matching (owner edge) edge).mpr ⟨selected, rfl⟩
          simp [exchange, selected, chosen]

def pairing (owner : Fin e → Fin q) (active : Fin e → Bool)
    (matching : Matching owner active) : Equiv.Perm (Fin q ⊕ Fin e) where
  toFun := exchange owner active
  invFun := exchange owner active
  left_inv := exchange_involutive owner active matching
  right_inv := exchange_involutive owner active matching

def permutation (owner : Fin e → Fin q) (active : Fin e → Bool)
    (matching : Matching owner active) : Equiv.Perm (Fin (q + e)) :=
  finSumFinEquiv.symm.trans ((pairing owner active matching).trans finSumFinEquiv)

theorem permutation_apply (owner : Fin e → Fin q) (active : Fin e → Bool)
    (matching : Matching owner active) (port : Fin (q + e)) :
    permutation owner active matching port =
      finSumFinEquiv (exchange owner active (finSumFinEquiv.symm port)) := rfl

theorem permutation_involutive (owner : Fin e → Fin q) (active : Fin e → Bool)
    (matching : Matching owner active) : Function.Involutive (permutation owner active matching) := by
  intro port
  simp only [permutation_apply, Equiv.symm_apply_apply]
  rw [exchange_involutive owner active matching (finSumFinEquiv.symm port)]
  exact finSumFinEquiv.apply_symm_apply port

theorem permutation_owner (owner : Fin e → Fin q) (active : Fin e → Bool)
    (matching : Matching owner active) (edge : Fin e) (selected : active edge = true) :
    permutation owner active matching (Fin.castAdd e (owner edge)) = Fin.natAdd q edge := by
  have chosen := (mate_some owner active matching (owner edge) edge).mpr ⟨selected, rfl⟩
  simp [permutation_apply, exchange, chosen]

theorem permutation_port (owner : Fin e → Fin q) (active : Fin e → Bool)
    (matching : Matching owner active) (edge : Fin e) :
    permutation owner active matching (Fin.natAdd q edge) =
      if active edge then Fin.castAdd e (owner edge) else Fin.natAdd q edge := by
  cases selected : active edge <;> simp [permutation_apply, exchange, selected]

theorem permutation_fixed_owner (owner : Fin e → Fin q) (active : Fin e → Bool)
    (matching : Matching owner active) (vertex : Fin q)
    (missing : ∀ edge, active edge = true → owner edge ≠ vertex) :
    permutation owner active matching (Fin.castAdd e vertex) = Fin.castAdd e vertex := by
  have absent : ¬ ∃ edge, active edge = true ∧ owner edge = vertex := by
    rintro ⟨edge, selected, endpoint⟩
    exact missing edge selected endpoint
  simp [permutation_apply, exchange, mate, absent]

open Counter.Reversible

/-- The guard class depends only on a static source instruction. -/
def actionGuard : Action 2 → ReversibleControl.Guard
  | .shift _ _ => none
  | .test register atZero => some (register, atZero)

theorem compatible_guards_ne {first second : Action 2}
    (compatible : first.Compatible second) : actionGuard first ≠ actionGuard second := by
  cases first <;> cases second <;> simp only [Action.Compatible] at compatible
  rcases compatible with ⟨rfl, different⟩
  simpa only [actionGuard, ne_eq, Option.some.injEq, Prod.mk.injEq, true_and] using different

/-- Numerical guard evaluation is used only in the proof interpretation. -/
theorem guard_enabled_iff (action : Action 2) (values : Fin 2 → ℤ) :
    ReversibleControl.enabled (actionGuard action) (values 0) (values 1) = true ↔
      action.enabled values := by
  cases action with
  | shift => simp [actionGuard, ReversibleControl.enabled, Action.enabled]
  | test register atZero =>
      fin_cases register <;> cases atZero <;>
        simp [actionGuard, ReversibleControl.enabled, Action.enabled] <;>
          exact decide_eq_true_iff

/-- Static selection of one of the five possible guard classes. -/
def selected (table : Table 2 q e) (guard : ReversibleControl.Guard) (edge : Fin e) : Bool :=
  decide (actionGuard (table edge).action = guard)

@[simp] theorem selected_iff (table : Table 2 q e) (guard : ReversibleControl.Guard)
    (edge : Fin e) : selected table guard edge = true ↔ actionGuard (table edge).action = guard := by
  simp [selected]

theorem sourceMatching (table : Table 2 q e) (deterministic : Deterministic table)
    (guard : ReversibleControl.Guard) :
    Matching (fun edge => (table edge).source) (selected table guard) := by
  intro first second fs ss same_source
  by_contra different
  exact compatible_guards_ne (deterministic first second different same_source)
    (((selected_iff table guard first).mp fs).trans ((selected_iff table guard second).mp ss).symm)

theorem targetMatching (table : Table 2 q e) (compatible : TargetCompatible table)
    (guard : ReversibleControl.Guard) :
    Matching (fun edge => (table edge).target) (selected table guard) := by
  intro first second fs ss same_target
  by_contra different
  exact compatible_guards_ne (compatible first second different same_target)
    (((selected_iff table guard first).mp fs).trans ((selected_iff table guard second).mp ss).symm)

/-- These are all guard classes; the list is independent of the compiled table. -/
def guards : List ReversibleControl.Guard :=
  [none, some (0, true), some (0, false), some (1, true), some (1, false)]

theorem guards_distinct : guards.Nodup := by decide

theorem guards_exhaustive (guard : ReversibleControl.Guard) : guard ∈ guards := by
  cases guard with
  | none => simp [guards]
  | some entry =>
      rcases entry with ⟨register, atZero⟩
      fin_cases register <;> cases atZero <;> simp [guards]

end Monodromy.ReversiblePorts

/-!
## Native guarded routing
-/

namespace Monodromy.ReversibleRouting

open CoupledContinuation Counter.Reversible ReversiblePorts

variable {q e : ℕ} [NeZero (q + e)]

/-- Alternatives attached to a common owner are complementary unchanged tests. -/
def CompatibleOwner (table : Table 2 q e) (owner : Fin e → Fin q) : Prop :=
  ∀ first second, first ≠ second → owner first = owner second →
    Action.Compatible (table first).action (table second).action

variable (table : Table 2 q e) (owner : Fin e → Fin q)
  (matching : ∀ guard, Matching owner (selected table guard))

/-- This stage contains only a fixed guard and its static finite port permutation. -/
def route (guard : ReversibleControl.Guard) : Program (q + e) :=
  ReversibleControl.program guard (permutation owner (selected table guard) (matching guard))

/-- Head-first execution of actual native return maps. -/
noncomputable def run (stages : List ReversibleControl.Guard) (state : Memory) : Memory :=
  stages.foldl (fun current guard => (route table owner matching guard).advance current) state

@[simp] theorem run_nil (state : Memory) : run table owner matching [] state = state := rfl

@[simp] theorem run_cons (guard : ReversibleControl.Guard)
    (stages : List ReversibleControl.Guard) (state : Memory) :
    run table owner matching (guard :: stages) state =
      run table owner matching stages ((route table owner matching guard).advance state) := rfl

/-- Only the finite address is abbreviated; the retained state is the same three roots. -/
noncomputable def point (values : Fin 2 → ℤ) (index : Fin (q + e)) : Memory :=
  prepare (values 0) (values 1) (index.val : ℤ)

theorem route_prepare (guard : ReversibleControl.Guard) (values : Fin 2 → ℤ)
    (index : Fin (q + e)) :
    (route table owner matching guard).advance (point values index) =
      if ReversibleControl.enabled guard (values 0) (values 1) then
        point values (permutation owner (selected table guard) (matching guard) index)
      else point values index := by
  simpa only [route, point, mul_zero, zero_add] using
    ReversibleControl.advance_prepare guard
      (permutation owner (selected table guard) (matching guard)) (values 0) (values 1) 0 index

theorem route_bijective (guard : ReversibleControl.Guard) :
    Function.Bijective (route table owner matching guard).advance :=
  (ReversibleControl.executionEquiv guard
    (permutation owner (selected table guard) (matching guard))).bijective

/-- The same actual native route reverses itself on the entire state fiber. -/
theorem route_involutive (guard : ReversibleControl.Guard) :
    Function.Involutive (route table owner matching guard).advance := by
  let pairing := permutation owner (selected table guard) (matching guard)
  have symmetry : pairing.symm = pairing := by
    apply Equiv.ext
    intro index
    apply pairing.injective
    calc
      pairing (pairing.symm index) = index := pairing.apply_symm_apply index
      _ = pairing (pairing index) :=
        (permutation_involutive owner (selected table guard) (matching guard) index).symm
  intro state
  change (ReversibleControl.program guard pairing).advance
    ((ReversibleControl.program guard pairing).advance state) = state
  simpa only [symmetry] using ReversibleControl.inverse guard pairing state

omit [NeZero (q + e)] in
/-- A different guard cannot activate any alternative at the enabled edge's owner. -/
theorem off_guard_owner (compatible : CompatibleOwner table owner)
    (values : Fin 2 → ℤ) (edge : Fin e) (enabled : (table edge).action.enabled values)
    (guard : ReversibleControl.Guard) (different : actionGuard (table edge).action ≠ guard)
    (active : ReversibleControl.enabled guard (values 0) (values 1) = true) :
    ∀ other, selected table guard other = true → owner other ≠ owner edge := by
  intro other chosen same_owner
  have other_guard := (selected_iff table guard other).mp chosen
  have other_enabled : (table other).action.enabled values :=
    (guard_enabled_iff (table other).action values).mp (other_guard ▸ active)
  have distinct : other ≠ edge := by
    intro same
    subst other
    exact different other_guard
  exact (compatible other edge distinct same_owner).not_both values ⟨other_enabled, enabled⟩

theorem route_owner (compatible : CompatibleOwner table owner) (values : Fin 2 → ℤ)
    (edge : Fin e) (enabled : (table edge).action.enabled values)
    (guard : ReversibleControl.Guard) :
    (route table owner matching guard).advance (point values (Fin.castAdd e (owner edge))) =
      if actionGuard (table edge).action = guard then point values (Fin.natAdd q edge)
      else point values (Fin.castAdd e (owner edge)) := by
  rw [route_prepare]
  by_cases chosen : actionGuard (table edge).action = guard
  · have active : ReversibleControl.enabled guard (values 0) (values 1) = true :=
      chosen ▸ (guard_enabled_iff (table edge).action values).mpr enabled
    rw [ite_eq_left active, ite_eq_left chosen,
      permutation_owner owner (selected table guard) (matching guard) edge
        ((selected_iff table guard edge).mpr chosen)]
  · rw [ite_eq_right chosen]
    by_cases active : ReversibleControl.enabled guard (values 0) (values 1) = true
    · rw [ite_eq_left active,
        permutation_fixed_owner owner (selected table guard) (matching guard) (owner edge)
          (off_guard_owner table owner compatible values edge enabled guard chosen active)]
    · rw [ite_eq_right active]

theorem route_port (values : Fin 2 → ℤ) (edge : Fin e)
    (enabled : (table edge).action.enabled values) (guard : ReversibleControl.Guard) :
    (route table owner matching guard).advance (point values (Fin.natAdd q edge)) =
      if actionGuard (table edge).action = guard then point values (Fin.castAdd e (owner edge))
      else point values (Fin.natAdd q edge) := by
  rw [route_prepare]
  by_cases chosen : actionGuard (table edge).action = guard
  · have active : ReversibleControl.enabled guard (values 0) (values 1) = true :=
      chosen ▸ (guard_enabled_iff (table edge).action values).mpr enabled
    rw [ite_eq_left active, permutation_port, ite_eq_left ((selected_iff table guard edge).mpr chosen),
      ite_eq_left chosen]
  · rw [ite_eq_right chosen]
    by_cases active : ReversibleControl.enabled guard (values 0) (values 1) = true
    · rw [ite_eq_left active, permutation_port]
      have unselected : selected table guard edge = false := by simpa [selected] using chosen
      rw [unselected]
      rfl
    · rw [ite_eq_right active]

/-- A guard occurring once exchanges precisely the enabled owner and its edge port. -/
theorem run_pair (compatible : CompatibleOwner table owner) (values : Fin 2 → ℤ)
    (edge : Fin e) (enabled : (table edge).action.enabled values)
    (stages : List ReversibleControl.Guard) (distinct : stages.Nodup) :
    (run table owner matching stages (point values (Fin.castAdd e (owner edge))) =
      if actionGuard (table edge).action ∈ stages then point values (Fin.natAdd q edge)
      else point values (Fin.castAdd e (owner edge))) ∧
    (run table owner matching stages (point values (Fin.natAdd q edge)) =
      if actionGuard (table edge).action ∈ stages then point values (Fin.castAdd e (owner edge))
      else point values (Fin.natAdd q edge)) := by
  induction stages with
  | nil => simp
  | cons guard stages induction_hypothesis =>
      obtain ⟨not_member, rest_distinct⟩ := List.nodup_cons.mp distinct
      obtain ⟨owner_run, port_run⟩ := induction_hypothesis rest_distinct
      by_cases chosen : actionGuard (table edge).action = guard
      · constructor
        · rw [run_cons, route_owner table owner matching compatible values edge enabled,
            ite_eq_left chosen, port_run]
          simp [chosen, not_member]
        · rw [run_cons, route_port table owner matching values edge enabled,
            ite_eq_left chosen, owner_run]
          simp [chosen, not_member]
      · constructor
        · rw [run_cons, route_owner table owner matching compatible values edge enabled,
            ite_eq_right chosen, owner_run]
          simp [chosen]
        · rw [run_cons, route_port table owner matching values edge enabled,
            ite_eq_right chosen, port_run]
          simp [chosen]

/-- All five stages send an enabled source or target owner to its exact edge port. -/
theorem run_owner (compatible : CompatibleOwner table owner) (values : Fin 2 → ℤ)
    (edge : Fin e) (enabled : (table edge).action.enabled values) :
    run table owner matching guards (point values (Fin.castAdd e (owner edge))) =
      point values (Fin.natAdd q edge) := by
  have result := (run_pair table owner matching compatible values edge enabled guards guards_distinct).1
  simpa only [ite_eq_left (guards_exhaustive _)] using result

/-- Reverse stage order returns the edge port to its owner with both memories unchanged. -/
theorem run_port (compatible : CompatibleOwner table owner) (values : Fin 2 → ℤ)
    (edge : Fin e) (enabled : (table edge).action.enabled values) :
    run table owner matching guards.reverse (point values (Fin.natAdd q edge)) =
      point values (Fin.castAdd e (owner edge)) := by
  have result := (run_pair table owner matching compatible values edge enabled guards.reverse
    (List.nodup_reverse.mpr guards_distinct)).2
  simpa only [List.mem_reverse, ite_eq_left (guards_exhaustive _)] using result

end Monodromy.ReversibleRouting

/-!
## The fixed reversible native compiler
-/

namespace Monodromy.ReversibleCompilation

open Counter.Reversible CoupledContinuation ReversiblePorts

variable {q e : ℕ} [NeZero q]

instance : NeZero (q + e) := ⟨by have := NeZero.ne q; omega⟩

/-- A finite source instruction fixes a signed displacement before execution. -/
def displacement : Action 2 → ℤ × ℤ
  | .shift register amount => if register = 0 then (amount, 0) else (0, amount)
  | .test _ _ => (0, 0)

theorem apply_coordinates (action : Action 2) (values : Fin 2 → ℤ) :
    ((action.apply values) 0, (action.apply values) 1) =
      (values 0 + (displacement action).1, values 1 + (displacement action).2) := by
  cases action with
  | test => simp [Action.apply, displacement]
  | shift register amount => fin_cases register <;> simp [Action.apply, displacement]

theorem enabled_after_apply (action : Action 2) (values : Fin 2 → ℤ)
    (enabled : action.enabled values) : action.enabled (action.apply values) := by
  cases action <;> exact enabled

/-- Source vertices and edge ports are finite addresses in the same control root. -/
def point (address : Fin (q + e)) (values : Fin 2 → ℤ) : Memory :=
  prepare (values 0) (values 1) address.val

def sourcePoint (state : State 2 q) : Memory :=
  point (Fin.castAdd e state.1) state.2

def portPoint (edge : Fin e) (values : Fin 2 → ℤ) : Memory :=
  point (Fin.natAdd q edge) values

omit [NeZero q] in
theorem sourcePoint_injective : Function.Injective (@sourcePoint q e) := by
  rintro ⟨first, values⟩ ⟨second, other⟩ same
  change prepare (values 0) (values 1) (first.val : ℤ) =
    prepare (other 0) (other 1) (second.val : ℤ) at same
  have coordinates := @prepare_injective ((values 0, values 1), (first.val : ℤ))
    ((other 0, other 1), (second.val : ℤ)) same
  have first_values : values 0 = other 0 := congrArg (fun labels => labels.1.1) coordinates
  have second_values : values 1 = other 1 := congrArg (fun labels => labels.1.2) coordinates
  have controls : (first.val : ℤ) = second.val := congrArg (fun labels => labels.2) coordinates
  apply Prod.ext
  · exact Fin.ext (by exact_mod_cast controls)
  · funext register
    fin_cases register
    · exact first_values
    · exact second_values

/-- Program data specifies the displacement at each finite edge port. -/
def moves (table : Table 2 q e) (address : Fin (q + e)) : ℤ × ℤ :=
  match finSumFinEquiv.symm address with
  | .inl _ => (0, 0)
  | .inr edge => displacement (table edge).action

def update (table : Table 2 q e) : Program (q + e) := ReversibleMemory.program (moves table)

theorem update_port (table : Table 2 q e) (edge : Fin e) (values : Fin 2 → ℤ) :
    (update table).advance (portPoint (q := q) edge values) =
      portPoint (q := q) edge ((table edge).action.apply values) := by
  have actual := ReversibleMemory.advance_prepare (moves table) (values 0) (values 1) 0
    (Fin.natAdd q edge)
  simp only [mul_zero, zero_add] at actual
  have coordinates := apply_coordinates (table edge).action values
  have left : ((table edge).action.apply values) 0 =
      values 0 + (displacement (table edge).action).1 := congrArg Prod.fst coordinates
  have right : ((table edge).action.apply values) 1 =
      values 1 + (displacement (table edge).action).2 := congrArg Prod.snd coordinates
  simpa only [update, portPoint, point, moves, finSumFinEquiv_symm_apply_natAdd,
    left, right] using actual

theorem update_bijective (table : Table 2 q e) : Function.Bijective (update table).advance :=
  (ReversibleMemory.executionEquiv (moves table)).bijective

def sourceLayers (table : Table 2 q e) (deterministic : Deterministic table) :
    List (Program (q + e)) :=
  guards.map (ReversibleRouting.route table (fun edge => (table edge).source)
    (sourceMatching table deterministic))

def targetLayers (table : Table 2 q e) (compatible : TargetCompatible table) :
    List (Program (q + e)) :=
  guards.reverse.map (ReversibleRouting.route table (fun edge => (table edge).target)
    (targetMatching table compatible))

/-- Five outward matchings, one memory update, and five reverse inward matchings. -/
def layers (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) : List (Program (q + e)) :=
  sourceLayers table deterministic ++ update table :: targetLayers table compatible

omit [NeZero q] in
theorem layers_length (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) : (layers table deterministic compatible).length = 11 := by
  simp [layers, sourceLayers, targetLayers, guards]

theorem sourceLayers_edge (table : Table 2 q e) (deterministic : Deterministic table)
    (edge : Fin e) (values : Fin 2 → ℤ) (enabled : (table edge).action.enabled values) :
    (sourceLayers table deterministic).foldl (fun state program => program.advance state)
      (sourcePoint (e := e) ((table edge).source, values)) = portPoint (q := q) edge values := by
  simpa only [sourceLayers, List.foldl_map, sourcePoint, point, portPoint,
    ReversibleRouting.run, ReversibleRouting.point] using
    ReversibleRouting.run_owner table (fun edge => (table edge).source)
      (sourceMatching table deterministic) deterministic values edge enabled

theorem targetLayers_edge (table : Table 2 q e) (compatible : TargetCompatible table)
    (edge : Fin e) (values : Fin 2 → ℤ) (enabled : (table edge).action.enabled values) :
    (targetLayers table compatible).foldl (fun state program => program.advance state)
      (portPoint (q := q) edge values) = sourcePoint (e := e) ((table edge).target, values) := by
  simpa only [targetLayers, List.foldl_map, sourcePoint, point, portPoint,
    ReversibleRouting.run, ReversibleRouting.point] using
    ReversibleRouting.run_port table (fun edge => (table edge).target)
      (targetMatching table compatible) compatible values edge enabled

/-- The actual native layers execute an enabled source edge, without calling its successor. -/
theorem layers_edge (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) (edge : Fin e) (values : Fin 2 → ℤ)
    (enabled : (table edge).action.enabled values) :
    (layers table deterministic compatible).foldl (fun state program => program.advance state)
      (sourcePoint (e := e) ((table edge).source, values)) =
      sourcePoint (e := e) ((table edge).target, (table edge).action.apply values) := by
  rw [layers, List.foldl_append, sourceLayers_edge table deterministic edge values enabled,
    List.foldl_cons, update_port, targetLayers_edge table compatible edge _
      (enabled_after_apply (table edge).action values enabled)]

/-- Finite stages are packed into the existing upper branch, with eleven fixed clock phases. -/
def stages (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) (phase : Fin 11) : Program (q + e) :=
  (layers table deterministic compatible).get
    ⟨phase.val, by rw [layers_length]; exact phase.isLt⟩

omit [NeZero q] in
theorem ofFn_stages (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) :
    List.ofFn (stages table deterministic compatible) = layers table deterministic compatible := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, layers_length]
  · intro index _ _
    rw [List.getElem_ofFn]
    rfl

def program (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) : Program (11 * (q + e)) :=
  StagedProgram.compile 11 (q + e) (stages table deterministic compatible)

def iota (state : State 2 q) : Memory := StagedProgram.embed 11 0 (sourcePoint (e := e) state)

omit [NeZero q] in
theorem iota_injective : Function.Injective (@iota q e) := by
  intro first second same
  have pair := (StagedProgram.packedEquiv 11).injective same
  exact sourcePoint_injective (congrArg Prod.fst pair)

/-- One source edge is eleven consecutive returns of one fixed native word table. -/
theorem cycle_edge (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) (edge : Fin e) (values : Fin 2 → ℤ)
    (enabled : (table edge).action.enabled values) :
    ((program table deterministic compatible).advance)^[11]
      (iota (e := e) ((table edge).source, values)) =
      iota (e := e) ((table edge).target, (table edge).action.apply values) := by
  change ((StagedProgram.compile 11 (q + e) (stages table deterministic compatible)).advance)^[11]
    (StagedProgram.embed 11 0 (sourcePoint (e := e) ((table edge).source, values))) = _
  rw [StagedProgram.cycle_ofFn, ofFn_stages, layers_edge table deterministic compatible edge values enabled]
  rfl

theorem cycle_step (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) {first last : State 2 q}
    (transition : step table first = some last) :
    ((program table deterministic compatible).advance)^[11] (iota (e := e) first) =
      iota (e := e) last := by
  obtain ⟨edge, enabled, rfl⟩ := (step_iff table deterministic).mp transition
  rcases first with ⟨position, values⟩
  obtain ⟨rfl, action_enabled⟩ := enabled
  exact cycle_edge table deterministic compatible edge values action_enabled

/-- The only non-involutive layer is undone by the negated static memory displacement. -/
def backwardStages (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) (phase : Fin 11) : Program (q + e) :=
  if phase = 5 then ReversibleMemory.program (ReversibleMemory.negate (moves table))
  else stages table deterministic compatible phase

omit [NeZero q] in
theorem stages_update (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) : stages table deterministic compatible 5 = update table := rfl

theorem stages_involutive (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) (phase : Fin 11) (different : phase ≠ 5) :
    Function.Involutive (stages table deterministic compatible phase).advance := by
  fin_cases phase <;> first
    | exact (different rfl).elim
    | exact ReversibleRouting.route_involutive _ _ _ _

theorem backward_left (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) (phase : Fin 11) (state : Memory) :
    (backwardStages table deterministic compatible phase).advance
      ((stages table deterministic compatible phase).advance state) = state := by
  by_cases middle : phase = 5
  · subst phase
    rw [backwardStages, ite_eq_left rfl, stages_update]
    exact ReversibleMemory.inverse (moves table) state
  · rw [backwardStages, ite_eq_right middle]
    exact stages_involutive table deterministic compatible phase middle state

theorem backward_right (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) (phase : Fin 11) (state : Memory) :
    (stages table deterministic compatible phase).advance
      ((backwardStages table deterministic compatible phase).advance state) = state := by
  by_cases middle : phase = 5
  · subst phase
    rw [backwardStages, ite_eq_left rfl, stages_update]
    simpa only [update, ReversibleMemory.negate_negate] using
      ReversibleMemory.inverse (ReversibleMemory.negate (moves table)) state
  · rw [backwardStages, ite_eq_right middle]
    exact stages_involutive table deterministic compatible phase middle state

/-- Reverse execution is another fixed native word table, selected from returned roots. -/
def reverseProgram (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) : Program (11 * (q + e)) :=
  StagedProgram.compileReverse 11 (q + e) (backwardStages table deterministic compatible)

theorem reverse_after_forward (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) (state : Memory) :
    (reverseProgram table deterministic compatible).advance
      ((program table deterministic compatible).advance state) = state :=
  StagedProgram.left_inverse 11 (q + e) _ _
    (backward_left table deterministic compatible) state

theorem forward_after_reverse (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) (state : Memory) :
    (program table deterministic compatible).advance
      ((reverseProgram table deterministic compatible).advance state) = state :=
  StagedProgram.right_inverse 11 (q + e) _ _
    (backward_right table deterministic compatible) state

/-- Both directions are fixed native tables on the same retained fiber. -/
def executionEquiv (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) : Memory ≃ Memory where
  toFun := (program table deterministic compatible).advance
  invFun := (reverseProgram table deterministic compatible).advance
  left_inv := reverse_after_forward table deterministic compatible
  right_inv := forward_after_reverse table deterministic compatible

theorem program_bijective (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) : Function.Bijective (program table deterministic compatible).advance :=
  (executionEquiv table deterministic compatible).bijective

/-- The native inverse traverses each complete source step backwards. -/
theorem reverse_cycle_step (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) {first last : State 2 q}
    (transition : step table first = some last) :
    ((reverseProgram table deterministic compatible).advance)^[11] (iota (e := e) last) =
      iota (e := e) first := by
  rw [← cycle_step table deterministic compatible transition]
  exact (Function.LeftInverse.iterate (reverse_after_forward table deterministic compatible) 11) _

end Monodromy.ReversibleCompilation

/-!
## Complete execution and actual lifted results
-/

namespace Monodromy.ReversibleCompilation

open Counter.Reversible CoupledContinuation

variable {q e : ℕ} [NeZero q]

/-- This finite bit table examines only static source edges, never current register values. -/
def haltMark (table : Table 2 q e) (address : Fin (q + e)) : Bool :=
  match finSumFinEquiv.symm address with
  | .inl position => decide (¬ ∃ edge, (table edge).source = position)
  | .inr _ => false

omit [NeZero q] in
@[simp] theorem haltMark_source (table : Table 2 q e) (position : Fin q) :
    haltMark table (Fin.castAdd e position) =
      decide (¬ ∃ edge, (table edge).source = position) := by
  simp [haltMark]

omit [NeZero q] in
@[simp] theorem haltMark_port (table : Table 2 q e) (edge : Fin e) :
    haltMark table (Fin.natAdd q edge) = false := by
  simp [haltMark]

/-- Only stopping bits change; the entire fixed geometric word table is retained. -/
def haltingProgram (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) : Program (11 * (q + e)) :=
  StagedProgram.markedCompile 11 (q + e) (stages table deterministic compatible) (haltMark table)

@[simp] theorem haltingProgram_advance (table : Table 2 q e)
    (deterministic : Deterministic table) (compatible : TargetCompatible table) :
    (haltingProgram table deterministic compatible).advance = (program table deterministic compatible).advance := rfl

theorem haltingProgram_bijective (table : Table 2 q e)
    (deterministic : Deterministic table) (compatible : TargetCompatible table) :
    Function.Bijective (haltingProgram table deterministic compatible).advance := by
  rw [haltingProgram_advance]
  exact program_bijective table deterministic compatible

theorem haltSignal_iota (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) (state : State 2 q) :
    (haltingProgram table deterministic compatible).haltSignal (iota (e := e) state) =
      if haltMark table (Fin.castAdd e state.1) then 1 else 0 := by
  have actual := StagedProgram.haltSignal_embed 11 (q + e)
    (stages table deterministic compatible) (haltMark table)
    (state.2 0) (state.2 1) 0 (Fin.castAdd e state.1) 0
  simpa only [haltingProgram, iota, sourcePoint, point, mul_zero, zero_add, ite_true] using actual

theorem haltSignal_iota_iff (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) (state : State 2 q) :
    (haltingProgram table deterministic compatible).haltSignal (iota (e := e) state) = 1 ↔
      ¬ ∃ edge, (table edge).source = state.1 := by
  rw [haltSignal_iota, haltMark_source]
  by_cases outgoing : ∃ edge, (table edge).source = state.1 <;> simp [outgoing]

/-- Completeness is the explicit hypothesis identifying finite address halting with source halting. -/
theorem halting_at_iota (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) (complete : Complete table) (state : State 2 q) :
    (haltingProgram table deterministic compatible).step (iota (e := e) state) = none ↔
      Counter.Reversible.step table state = none := by
  rw [Counter.Reversible.step_none_iff_no_outgoing table complete]
  unfold Program.step
  simp only [haltSignal_iota_iff]
  split_ifs <;> simp_all

/-- Every live source transition is a positive sequence of the actual stopped native returns. -/
theorem step_reaches (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) {first last : State 2 q}
    (transition : Counter.Reversible.step table first = some last) :
    StateTransition.Reaches₁ (haltingProgram table deterministic compatible).step
      (iota (e := e) first) (iota (e := e) last) := by
  obtain ⟨edge, enabled, _⟩ := (Counter.Reversible.step_iff table deterministic).mp transition
  have outgoing : ∃ edge, (table edge).source = first.1 := ⟨edge, enabled.1⟩
  have unmarked : haltMark table (Fin.castAdd e first.1) = false := by
    simp [haltMark_source, outgoing]
  have run := StagedProgram.cycle_reaches 11 (q + e)
    (stages table deterministic compatible) (haltMark table)
    (first.2 0) (first.2 1) 0 (Fin.castAdd e first.1) unmarked
  have ending :
      StagedProgram.embed 11 0
        ((List.ofFn (stages table deterministic compatible)).foldl
          (fun point stage => stage.advance point) (sourcePoint (e := e) first)) =
      iota (e := e) last :=
    (StagedProgram.cycle_ofFn 11 (q + e) (stages table deterministic compatible)
      (sourcePoint (e := e) first)).symm.trans
      (cycle_step table deterministic compatible transition)
  have actual :
      StateTransition.Reaches₁ (haltingProgram table deterministic compatible).step
        (iota (e := e) first)
        (StagedProgram.embed 11 0
          ((List.ofFn (stages table deterministic compatible)).foldl
            (fun point stage => stage.advance point) (sourcePoint (e := e) first))) := by
    simpa only [haltingProgram, iota, sourcePoint, point, mul_zero, zero_add] using run
  rw [ending] at actual
  exact actual

/-- Finite source traces lift without any assumption about states outside the trace. -/
theorem reaches_iota (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) {first last : State 2 q}
    (run : StateTransition.Reaches (Counter.Reversible.step table) first last) :
    StateTransition.Reaches (haltingProgram table deterministic compatible).step
      (iota (e := e) first) (iota (e := e) last) := by
  induction run with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ transition previous =>
      exact previous.trans (step_reaches table deterministic compatible transition).to_reflTransGen

theorem eval_of_reaches (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) {first last : State 2 q}
    (run : StateTransition.Reaches (Counter.Reversible.step table) first last)
    (stopped : ¬ ∃ edge, (table edge).source = last.1) :
    (haltingProgram table deterministic compatible).eval (iota (e := e) first) =
      Part.some (iota (e := e) last) := by
  apply Part.eq_some_iff.mpr
  apply StateTransition.mem_eval.mpr
  refine ⟨reaches_iota table deterministic compatible run, ?_⟩
  have signal := (haltSignal_iota_iff table deterministic compatible last).mpr stopped
  simp only [Program.step, signal, ite_true]

/-- On the invariant, the existing static halting marks agree with source stopping. -/
theorem halting_at_iota_on (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) (invariant : State 2 q → Prop)
    (complete : CompleteOn table invariant) (state : State 2 q) (valid : invariant state) :
    (haltingProgram table deterministic compatible).step (iota (e := e) state) = none ↔
      Counter.Reversible.step table state = none := by
  rw [Counter.Reversible.step_none_iff_no_outgoing_on table invariant complete state valid]
  unfold Program.step
  simp only [haltSignal_iota_iff]
  split_ifs <;> simp_all

/-- The invariant belongs to the simulation relation, rather than the runtime state. -/
theorem respects_on (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) (invariant : State 2 q → Prop)
    (complete : CompleteOn table invariant) (stable : Stable table invariant) :
    StateTransition.Respects (Counter.Reversible.step table)
      (haltingProgram table deterministic compatible).step
      (fun original native => invariant original ∧ iota (e := e) original = native) := by
  intro state native related
  rcases related with ⟨valid, rfl⟩
  cases transition : Counter.Reversible.step table state with
  | none =>
      exact (halting_at_iota_on table deterministic compatible invariant complete state valid).mpr
        transition
  | some next =>
      exact ⟨iota (e := e) next, ⟨stable valid transition, rfl⟩,
        step_reaches table deterministic compatible transition⟩

/-- Every result and undefined computation is preserved from an invariant initial state. -/
theorem eval_iota_on (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) (invariant : State 2 q → Prop)
    (complete : CompleteOn table invariant) (stable : Stable table invariant)
    (state : State 2 q) (valid : invariant state) :
    (haltingProgram table deterministic compatible).eval (iota (e := e) state) =
      iota (e := e) <$> Counter.Reversible.eval table state := by
  have simulation := respects_on table deterministic compatible invariant complete stable
  exact Part.ext fun final =>
    ⟨fun completed => by
      obtain ⟨source, related, result⟩ := StateTransition.tr_eval_rev simulation ⟨valid, rfl⟩ completed
      exact (Part.mem_map_iff _).mpr ⟨source, result, related.2⟩,
      fun completed => by
        obtain ⟨source, result, same⟩ := (Part.mem_map_iff _).mp completed
        obtain ⟨native, related, execution⟩ := StateTransition.tr_eval simulation ⟨valid, rfl⟩ result
        rw [← related.2, same] at execution
        exact execution⟩

theorem halting_iff_on (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) (invariant : State 2 q → Prop)
    (complete : CompleteOn table invariant) (stable : Stable table invariant)
    (state : State 2 q) (valid : invariant state) :
    ((haltingProgram table deterministic compatible).eval (iota (e := e) state)).Dom ↔
      (Counter.Reversible.eval table state).Dom := by
  rw [eval_iota_on table deterministic compatible invariant complete stable state valid]
  rfl

theorem divergence_iff_on (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) (invariant : State 2 q → Prop)
    (complete : CompleteOn table invariant) (stable : Stable table invariant)
    (state : State 2 q) (valid : invariant state) :
    ¬ ((haltingProgram table deterministic compatible).eval (iota (e := e) state)).Dom ↔
      ¬ (Counter.Reversible.eval table state).Dom :=
  not_congr (halting_iff_on table deterministic compatible invariant complete stable state valid)

theorem respects (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) (complete : Complete table) :
    StateTransition.Respects (Counter.Reversible.step table)
      (haltingProgram table deterministic compatible).step
      (fun original native => iota (e := e) original = native) := by
  simpa only [true_and] using
    respects_on table deterministic compatible (fun _ => True)
      (complete.completeOn _) (fun {_ _} _ _ => trivial)

/-- The entire final integer configuration, and undefinedness, are preserved. -/
theorem eval_iota (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) (complete : Complete table) (state : State 2 q) :
    (haltingProgram table deterministic compatible).eval (iota (e := e) state) =
      iota (e := e) <$> Counter.Reversible.eval table state :=
  eval_iota_on table deterministic compatible (fun _ => True)
    (complete.completeOn _) (fun {_ _} _ _ => trivial) state trivial

theorem halting_iff (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) (complete : Complete table) (state : State 2 q) :
    ((haltingProgram table deterministic compatible).eval (iota (e := e) state)).Dom ↔
      (Counter.Reversible.eval table state).Dom := by
  rw [eval_iota table deterministic compatible complete]
  rfl

theorem divergence_iff (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) (complete : Complete table) (state : State 2 q) :
    ¬ ((haltingProgram table deterministic compatible).eval (iota (e := e) state)).Dom ↔
      ¬ (Counter.Reversible.eval table state).Dom :=
  not_congr (halting_iff table deterministic compatible complete state)

theorem result (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) (complete : Complete table) {first last : State 2 q}
    (completed : last ∈ Counter.Reversible.eval table first) :
    iota (e := e) last ∈ (haltingProgram table deterministic compatible).eval (iota (e := e) first) := by
  rw [eval_iota table deterministic compatible complete]
  exact (Part.mem_map_iff _).mpr ⟨last, completed, rfl⟩

theorem result_iff (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) (complete : Complete table) (first last : State 2 q) :
    iota (e := e) last ∈ (haltingProgram table deterministic compatible).eval (iota (e := e) first) ↔
      last ∈ Counter.Reversible.eval table first := by
  rw [eval_iota table deterministic compatible complete]
  constructor
  · intro found
    obtain ⟨source, completed, same⟩ := (Part.mem_map_iff _).mp found
    have recovered := iota_injective same
    simpa only [recovered] using completed
  · intro completed
    exact (Part.mem_map_iff _).mpr ⟨last, completed, rfl⟩

/-- Eleven actual native returns form the first positive phase-zero return. -/
theorem step_firstReturn (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) {first last : State 2 q}
    (transition : Counter.Reversible.step table first = some last) :
    ((haltingProgram table deterministic compatible).advance)^[11] (iota (e := e) first) =
        iota (e := e) last ∧
      StagedProgram.PhaseBoundary 11 (iota (e := e) first) ∧
      StagedProgram.PhaseBoundary 11 (iota (e := e) last) ∧
      (∀ round : ℕ, 0 < round → round < 11 →
        ¬ StagedProgram.PhaseBoundary 11
          (((haltingProgram table deterministic compatible).advance)^[round] (iota (e := e) first))) ∧
      StateTransition.Reaches₁ (haltingProgram table deterministic compatible).step
        (iota (e := e) first) (iota (e := e) last) := by
  refine ⟨?_, ?_, ?_, ?_, step_reaches table deterministic compatible transition⟩
  · rw [haltingProgram_advance]
    exact cycle_step table deterministic compatible transition
  · exact (StagedProgram.phaseBoundary_embed_iff 11 0 (sourcePoint (e := e) first)).mpr rfl
  · exact (StagedProgram.phaseBoundary_embed_iff 11 0 (sourcePoint (e := e) last)).mpr rfl
  · intro round positive before
    exact StagedProgram.cycle_interior 11 (q + e) (stages table deterministic compatible)
      (haltMark table) (sourcePoint (e := e) first) round positive before

/-- A complete result is realized by the two actual covering lifts of the native generated path. -/
theorem result_actual_lifts (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) (complete : Complete table) {first last : State 2 q}
    (completed : last ∈ Counter.Reversible.eval table first) :
    ∃ count : ℕ,
      let initial := iota (e := e) first
      let driver := (haltingProgram table deterministic compatible).runDriver count initial
      intermediateCurve driver initial =
        CoupledPullback.lowerCovering.liftPath driver.restrictedPath
          (CoupledPullback.upperProjection (restrictedState initial))
          (driver.restrictedPath.source.trans (restrictedState_over_base initial).symm) ∧
      restrictedTrajectory driver initial =
        CoupledPullback.upperCovering.liftPath (intermediatePath driver initial) (restrictedState initial)
          (intermediatePath driver initial).source ∧
      restrictedTrajectory driver initial 1 = restrictedState (iota (e := e) last) := by
  obtain ⟨count, endpoint⟩ := (haltingProgram table deterministic compatible).runDriver_of_eval
    (result table deterministic compatible complete completed)
  refine ⟨count, ?_⟩
  dsimp only
  refine ⟨intermediateCurve_actual_lift _ _, restrictedTrajectory_actual_lift _ _, ?_⟩
  rw [restrictedTrajectory_end, endpoint]

end Monodromy.ReversibleCompilation

/-!
## Protected source register relocation
-/

namespace Monodromy.Counter.Reversible.RegisterRelocation

variable {n m q e : ℕ}

def mapAction (register : Fin n → Fin m) : Action n → Action m
  | .shift index amount => .shift (register index) amount
  | .test index atZero => .test (register index) atZero

@[simp] theorem unitShift_mapAction (register : Fin n → Fin m) (action : Action n) :
    Action.UnitShift (mapAction register action) ↔ Action.UnitShift action := by
  cases action <;> rfl

def mapTable (register : Fin n → Fin m) (source : Table n q e) : Table m q e :=
  fun edge => ⟨(source edge).source, (source edge).target, mapAction register (source edge).action⟩

theorem compatible_iff (register : Fin n → Fin m) (faithful : Function.Injective register)
    (first second : Action n) :
    Action.Compatible (mapAction register first) (mapAction register second) ↔
      Action.Compatible first second := by
  cases first <;> cases second <;> simp [mapAction, Action.Compatible, faithful.eq_iff]

theorem deterministic (register : Fin n → Fin m) (faithful : Function.Injective register)
    (source : Table n q e) (valid : Deterministic source) :
    Deterministic (mapTable register source) := by
  intro first second different same
  exact (compatible_iff register faithful _ _).mpr (valid first second different same)

theorem targetCompatible (register : Fin n → Fin m) (faithful : Function.Injective register)
    (source : Table n q e) (valid : TargetCompatible source) :
    TargetCompatible (mapTable register source) := by
  intro first second different same
  exact (compatible_iff register faithful _ _).mpr (valid first second different same)

theorem enabled_project (register : Fin n → Fin m) (action : Action n) (values : Fin m → ℤ) :
    (mapAction register action).enabled values ↔ action.enabled (values ∘ register) := by
  cases action <;> rfl

theorem apply_project (register : Fin n → Fin m) (faithful : Function.Injective register)
    (action : Action n) (values : Fin m → ℤ) :
    (mapAction register action).apply values ∘ register = action.apply (values ∘ register) := by
  cases action with
  | test => rfl
  | shift index amount =>
      funext selected
      by_cases same : selected = index
      · subst selected
        simp [mapAction, Action.apply]
      · have distinct : register selected ≠ register index := fun equal => same (faithful equal)
        simp [mapAction, Action.apply, Function.update_of_ne, same, distinct]

/-- Protected registers retain their arbitrary prior values. -/
theorem apply_outside (register : Fin n → Fin m) (action : Action n) (values : Fin m → ℤ)
    (index : Fin m) (outside : ∀ selected, register selected ≠ index) :
    (mapAction register action).apply values index = values index := by
  cases action with
  | test => rfl
  | shift selected amount =>
      exact Function.update_of_ne (outside selected).symm _ _

/-- Only the selected source registers are inserted into the protected background. -/
def embed (register : Fin n → Fin m) (background : Fin m → ℤ) (state : State n q) : State m q :=
  (state.1, Function.extend register state.2 background)

theorem embed_read (register : Fin n → Fin m) (faithful : Function.Injective register)
    (background : Fin m → ℤ) (state : State n q) (index : Fin n) :
    (embed register background state).2 (register index) = state.2 index :=
  faithful.extend_apply _ _ _

theorem embed_outside (register : Fin n → Fin m) (background : Fin m → ℤ)
    (state : State n q) (index : Fin m) (outside : ∀ selected, register selected ≠ index) :
    (embed register background state).2 index = background index :=
  Function.extend_apply' _ _ _ (by rintro ⟨selected, same⟩; exact outside selected same)

theorem embed_injective (register : Fin n → Fin m) (faithful : Function.Injective register)
    (background : Fin m → ℤ) : Function.Injective (embed (q := q) register background) := by
  intro first second same
  apply Prod.ext
  · exact congrArg (fun state : State m q => state.1) same
  · funext index
    simpa only [embed_read register faithful] using congrArg (fun state => state.2 (register index)) same

theorem action_embed (register : Fin n → Fin m) (faithful : Function.Injective register)
    (background : Fin m → ℤ) (action : Action n) (values : Fin n → ℤ) :
    (mapAction register action).apply (Function.extend register values background) =
      Function.extend register (action.apply values) background := by
  cases action with
  | test => rfl
  | shift index amount =>
      simp only [mapAction, Action.apply, faithful.extend_apply, faithful.extend_update]

theorem edge_enabled_embed (register : Fin n → Fin m) (faithful : Function.Injective register)
    (background : Fin m → ℤ) (source : Table n q e) (edge : Fin e) (state : State n q) :
    (mapTable register source edge).enabled (embed register background state) ↔
      (source edge).enabled state := by
  simp only [Edge.enabled, mapTable, embed, enabled_project, Function.extend_comp faithful]

theorem edge_execute_embed (register : Fin n → Fin m) (faithful : Function.Injective register)
    (background : Fin m → ℤ) (source : Table n q e) (edge : Fin e) (state : State n q) :
    (mapTable register source edge).execute (embed register background state) =
      embed register background ((source edge).execute state) := by
  simp only [Edge.execute, mapTable, embed, action_embed register faithful]

/-- Relocation preserves the complete step, including its stopping decision. -/
theorem step_embed (register : Fin n → Fin m) (faithful : Function.Injective register)
    (background : Fin m → ℤ) (source : Table n q e) (valid : Deterministic source)
    (state : State n q) :
    step (mapTable register source) (embed register background state) =
      (step source state).map (embed register background) := by
  cases result : step source state with
  | none =>
      rw [Option.map_none, step_none_iff]
      have absent := (step_none_iff source state).mp result
      rintro ⟨edge, enabled⟩
      exact absent ⟨edge, (edge_enabled_embed register faithful background source edge state).mp enabled⟩
  | some next =>
      rw [Option.map_some]
      apply (step_iff _ (deterministic register faithful source valid)).mpr
      obtain ⟨edge, enabled, result⟩ := (step_iff source valid).mp result
      refine ⟨edge, (edge_enabled_embed register faithful background source edge state).mpr enabled, ?_⟩
      rw [edge_execute_embed register faithful background source edge state, result]

theorem reaches_embed (register : Fin n → Fin m) (faithful : Function.Injective register)
    (background : Fin m → ℤ) (source : Table n q e) (valid : Deterministic source)
    {first last : State n q} (run : StateTransition.Reaches (step source) first last) :
    StateTransition.Reaches (step (mapTable register source))
      (embed register background first) (embed register background last) := by
  induction run with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ transition previous =>
      apply previous.tail
      rw [step_embed register faithful background source valid, transition]
      rfl

theorem eval_embed (register : Fin n → Fin m) (faithful : Function.Injective register)
    (background : Fin m → ℤ) (source : Table n q e) (valid : Deterministic source)
    (state : State n q) :
    eval (mapTable register source) (embed register background state) =
      embed register background <$> eval source state := by
  apply StateTransition.tr_eval' (step source) (step (mapTable register source))
    (embed register background)
  apply StateTransition.fun_respects.mpr
  intro current
  cases result : step source current with
  | none =>
      change step (mapTable register source) (embed register background current) = none
      simp [step_embed register faithful background source valid, result]
  | some next =>
      apply Relation.TransGen.single
      simp [step_embed register faithful background source valid, result]

end Monodromy.Counter.Reversible.RegisterRelocation

/-!
## Composition by gluing control interfaces
-/

namespace Monodromy.Counter.Reversible.Glue

variable {n q₁ q₂ e₁ e₂ : ℕ}

def leftControl (exit : Fin (q₁ + 1)) (entry : Fin q₂) : Fin (q₁ + 1) → Fin (q₁ + q₂) :=
  Fin.insertNth exit (Fin.natAdd q₁ entry) (Fin.castAdd q₂)

def rightControl (position : Fin q₂) : Fin (q₁ + q₂) := Fin.natAdd q₁ position

@[simp] theorem leftControl_exit (exit : Fin (q₁ + 1)) (entry : Fin q₂) :
    leftControl exit entry exit = rightControl entry := by
  simp [leftControl, rightControl]

@[simp] theorem leftControl_other (exit : Fin (q₁ + 1)) (entry : Fin q₂) (position : Fin q₁) :
    leftControl exit entry (exit.succAbove position) = Fin.castAdd q₂ position := by
  simp [leftControl]

/-- The two sets of control addresses meet at precisely the identified interface. -/
theorem controls_eq_iff (exit : Fin (q₁ + 1)) (entry : Fin q₂)
    (left : Fin (q₁ + 1)) (right : Fin q₂) :
    leftControl exit entry left = rightControl right ↔ left = exit ∧ right = entry := by
  cases left using Fin.succAboveCases exit with
  | x => simp [leftControl, rightControl, eq_comm]
  | p position =>
      simp only [leftControl_other]
      constructor
      · intro same
        have values := congrArg Fin.val same
        have bound := position.isLt
        simp only [Fin.val_castAdd, rightControl, Fin.val_natAdd] at values
        omega
      · rintro ⟨same, _⟩
        exact False.elim (Fin.succAbove_ne exit position same)

theorem leftControl_injective (exit : Fin (q₁ + 1)) (entry : Fin q₂) :
    Function.Injective (leftControl exit entry) := by
  intro first second same
  rcases Fin.eq_self_or_eq_succAbove exit first with first_exit | ⟨first_rank, first_other⟩
  · rw [first_exit] at same ⊢
    have second_exit := ((controls_eq_iff exit entry second entry).mp
      (same.symm.trans (leftControl_exit exit entry))).1
    exact second_exit.symm
  · rw [first_other] at same ⊢
    rcases Fin.eq_self_or_eq_succAbove exit second with second_exit | ⟨second_rank, second_other⟩
    · rw [second_exit] at same ⊢
      exact ((controls_eq_iff exit entry (exit.succAbove first_rank) entry).mp
        (same.trans (leftControl_exit exit entry))).1
    · rw [second_other] at same ⊢
      rw [leftControl_other, leftControl_other] at same
      have values : first_rank.val = second_rank.val :=
        congrArg (fun position : Fin (q₁ + q₂) => position.val) same
      exact congrArg exit.succAbove (Fin.ext values)

theorem rightControl_injective : Function.Injective (@rightControl q₁ q₂) := by
  intro first second same
  apply Fin.ext
  have values := congrArg Fin.val same
  simp only [rightControl, Fin.val_natAdd] at values
  omega

def mapEdge {q k : ℕ} (control : Fin q → Fin k) (edge : Edge n q) : Edge n k :=
  ⟨control edge.source, control edge.target, edge.action⟩

def mapState {q k : ℕ} (control : Fin q → Fin k) (state : State n q) : State n k :=
  (control state.1, state.2)

def table (first : Table n (q₁ + 1) e₁) (second : Table n q₂ e₂)
    (exit : Fin (q₁ + 1)) (entry : Fin q₂) : Table n (q₁ + q₂) (e₁ + e₂) :=
  fun index => match finSumFinEquiv.symm index with
    | .inl edge => mapEdge (leftControl exit entry) (first edge)
    | .inr edge => mapEdge rightControl (second edge)

@[simp] theorem table_left (first : Table n (q₁ + 1) e₁) (second : Table n q₂ e₂)
    (exit : Fin (q₁ + 1)) (entry : Fin q₂) (index : Fin e₁) :
    table first second exit entry (Fin.castAdd e₂ index) =
      mapEdge (leftControl exit entry) (first index) := by
  simp [table]

@[simp] theorem table_right (first : Table n (q₁ + 1) e₁) (second : Table n q₂ e₂)
    (exit : Fin (q₁ + 1)) (entry : Fin q₂) (index : Fin e₂) :
    table first second exit entry (Fin.natAdd e₁ index) =
      mapEdge rightControl (second index) := by
  simp [table]

theorem deterministic (first : Table n (q₁ + 1) e₁) (second : Table n q₂ e₂)
    (exit : Fin (q₁ + 1)) (entry : Fin q₂)
    (first_deterministic : Deterministic first) (second_deterministic : Deterministic second)
    (no_outgoing : ∀ index, (first index).source ≠ exit) :
    Deterministic (table first second exit entry) := by
  intro left right different same
  induction left using Fin.addCases
  · rename_i left
    induction right using Fin.addCases
    · rename_i right
      simp only [table_left, mapEdge] at same ⊢
      exact first_deterministic left right
        (fun equal => different (congrArg (Fin.castAdd e₂) equal))
        (leftControl_injective exit entry same)
    · rename_i right
      simp only [table_left, table_right, mapEdge] at same ⊢
      exact False.elim (no_outgoing left ((controls_eq_iff exit entry _ _).mp same).1)
  · rename_i left
    induction right using Fin.addCases
    · rename_i right
      simp only [table_left, table_right, mapEdge] at same ⊢
      exact False.elim (no_outgoing right ((controls_eq_iff exit entry _ _).mp same.symm).1)
    · rename_i right
      simp only [table_right, mapEdge] at same ⊢
      exact second_deterministic left right
        (fun equal => different (congrArg (Fin.natAdd e₁) equal))
        (rightControl_injective same)

theorem targetCompatible (first : Table n (q₁ + 1) e₁) (second : Table n q₂ e₂)
    (exit : Fin (q₁ + 1)) (entry : Fin q₂)
    (first_compatible : TargetCompatible first) (second_compatible : TargetCompatible second)
    (no_incoming : ∀ index, (second index).target ≠ entry) :
    TargetCompatible (table first second exit entry) := by
  intro left right different same
  induction left using Fin.addCases
  · rename_i left
    induction right using Fin.addCases
    · rename_i right
      simp only [table_left, mapEdge] at same ⊢
      exact first_compatible left right
        (fun equal => different (congrArg (Fin.castAdd e₂) equal))
        (leftControl_injective exit entry same)
    · rename_i right
      simp only [table_left, table_right, mapEdge] at same ⊢
      exact False.elim (no_incoming right ((controls_eq_iff exit entry _ _).mp same).2)
  · rename_i left
    induction right using Fin.addCases
    · rename_i right
      simp only [table_left, table_right, mapEdge] at same ⊢
      exact False.elim (no_incoming left ((controls_eq_iff exit entry _ _).mp same.symm).2)
    · rename_i right
      simp only [table_right, mapEdge] at same ⊢
      exact second_compatible left right
        (fun equal => different (congrArg (Fin.natAdd e₁) equal))
        (rightControl_injective same)

/-- The two source configurations at the interface are literally the same glued state. -/
@[simp] theorem interface (exit : Fin (q₁ + 1)) (entry : Fin q₂) (values : Fin n → ℤ) :
    mapState (leftControl exit entry) (exit, values) = mapState rightControl (entry, values) := by
  exact Prod.ext (leftControl_exit exit entry) rfl

theorem step_left (first : Table n (q₁ + 1) e₁) (second : Table n q₂ e₂)
    (exit : Fin (q₁ + 1)) (entry : Fin q₂)
    (first_deterministic : Deterministic first) (second_deterministic : Deterministic second)
    (no_outgoing : ∀ index, (first index).source ≠ exit)
    {initial final : State n (q₁ + 1)} (transition : step first initial = some final) :
    step (table first second exit entry) (mapState (leftControl exit entry) initial) =
      some (mapState (leftControl exit entry) final) := by
  obtain ⟨index, enabled, result⟩ := (step_iff first first_deterministic).mp transition
  apply (step_iff _ (deterministic first second exit entry first_deterministic second_deterministic
    no_outgoing)).mpr
  refine ⟨Fin.castAdd e₂ index, ?_, ?_⟩
  · rw [table_left]
    exact ⟨congrArg (leftControl exit entry) enabled.1, enabled.2⟩
  · rw [table_left]
    exact congrArg (mapState (leftControl exit entry)) result

theorem step_right (first : Table n (q₁ + 1) e₁) (second : Table n q₂ e₂)
    (exit : Fin (q₁ + 1)) (entry : Fin q₂)
    (first_deterministic : Deterministic first) (second_deterministic : Deterministic second)
    (no_outgoing : ∀ index, (first index).source ≠ exit)
    {initial final : State n q₂} (transition : step second initial = some final) :
    step (table first second exit entry) (mapState rightControl initial) =
      some (mapState rightControl final) := by
  obtain ⟨index, enabled, result⟩ := (step_iff second second_deterministic).mp transition
  apply (step_iff _ (deterministic first second exit entry first_deterministic second_deterministic
    no_outgoing)).mpr
  refine ⟨Fin.natAdd e₁ index, ?_, ?_⟩
  · rw [table_right]
    exact ⟨congrArg rightControl enabled.1, enabled.2⟩
  · rw [table_right]
    exact congrArg (mapState rightControl) result

theorem reaches_left (first : Table n (q₁ + 1) e₁) (second : Table n q₂ e₂)
    (exit : Fin (q₁ + 1)) (entry : Fin q₂)
    (first_deterministic : Deterministic first) (second_deterministic : Deterministic second)
    (no_outgoing : ∀ index, (first index).source ≠ exit)
    {initial final : State n (q₁ + 1)} (run : StateTransition.Reaches (step first) initial final) :
    StateTransition.Reaches (step (table first second exit entry))
      (mapState (leftControl exit entry) initial) (mapState (leftControl exit entry) final) := by
  exact Relation.ReflTransGen.lift (mapState (leftControl exit entry))
    (fun _ _ transition => step_left first second exit entry first_deterministic
      second_deterministic no_outgoing transition) _ _ run

theorem reaches_right (first : Table n (q₁ + 1) e₁) (second : Table n q₂ e₂)
    (exit : Fin (q₁ + 1)) (entry : Fin q₂)
    (first_deterministic : Deterministic first) (second_deterministic : Deterministic second)
    (no_outgoing : ∀ index, (first index).source ≠ exit)
    {initial final : State n q₂} (run : StateTransition.Reaches (step second) initial final) :
    StateTransition.Reaches (step (table first second exit entry))
      (mapState rightControl initial) (mapState rightControl final) := by
  exact Relation.ReflTransGen.lift (mapState rightControl)
    (fun _ _ transition => step_right first second exit entry first_deterministic
      second_deterministic no_outgoing transition) _ _ run

/-- A completed first trace and a second trace compose at the identified control point. -/
theorem reaches_compose (first : Table n (q₁ + 1) e₁) (second : Table n q₂ e₂)
    (exit : Fin (q₁ + 1)) (entry : Fin q₂)
    (first_deterministic : Deterministic first) (second_deterministic : Deterministic second)
    (no_outgoing : ∀ index, (first index).source ≠ exit)
    {initial : State n (q₁ + 1)} {final : State n q₂} (values : Fin n → ℤ)
    (first_run : StateTransition.Reaches (step first) initial (exit, values))
    (second_run : StateTransition.Reaches (step second) (entry, values) final) :
    StateTransition.Reaches (step (table first second exit entry))
      (mapState (leftControl exit entry) initial) (mapState rightControl final) := by
  have first_trace := reaches_left first second exit entry first_deterministic second_deterministic
    no_outgoing first_run
  rw [interface] at first_trace
  exact first_trace.trans (reaches_right first second exit entry first_deterministic
    second_deterministic no_outgoing second_run)

/-! Finite traces inside larger control graphs. -/

section FiniteTrace

variable {n m q k e f : ℕ}

/-- Inclusion of the chosen edges preserves live steps; exit edges may be added. -/
theorem step_map_live (source : Table n q e) (target : Table n k f)
    (control : Fin q → Fin k) (edge : Fin e → Fin f)
    (agrees : ∀ index, target (edge index) = mapEdge control (source index))
    (source_valid : Deterministic source) (target_valid : Deterministic target)
    {first last : State n q} (transition : step source first = some last) :
    step target (mapState control first) = some (mapState control last) := by
  obtain ⟨index, enabled, result⟩ := (step_iff source source_valid).mp transition
  apply (step_iff target target_valid).mpr
  refine ⟨edge index, ?_, ?_⟩
  · rw [agrees]
    exact ⟨congrArg control enabled.1, enabled.2⟩
  · rw [agrees]
    exact congrArg (mapState control) result

/-- Every finite source trace runs inside the target with its full register vector. -/
theorem reaches_map_live (source : Table n q e) (target : Table n k f)
    (control : Fin q → Fin k) (edge : Fin e → Fin f)
    (agrees : ∀ index, target (edge index) = mapEdge control (source index))
    (source_valid : Deterministic source) (target_valid : Deterministic target)
    {first last : State n q} (run : StateTransition.Reaches (step source) first last) :
    StateTransition.Reaches (step target) (mapState control first) (mapState control last) := by
  exact Relation.ReflTransGen.lift (mapState control)
    (fun _ _ transition => step_map_live source target control edge agrees
      source_valid target_valid transition) _ _ run

/-- Register relocation precedes control inclusion and protects all background values. -/
theorem reaches_embed_map_live (source : Table n q e) (target : Table m k f)
    (register : Fin n → Fin m) (faithful : Function.Injective register)
    (background : Fin m → ℤ) (control : Fin q → Fin k) (edge : Fin e → Fin f)
    (agrees : ∀ index, target (edge index) =
      mapEdge control (RegisterRelocation.mapTable register source index))
    (source_valid : Deterministic source) (target_valid : Deterministic target)
    {first last : State n q} (run : StateTransition.Reaches (step source) first last) :
    StateTransition.Reaches (step target)
      (mapState control (RegisterRelocation.embed register background first))
      (mapState control (RegisterRelocation.embed register background last)) := by
  exact reaches_map_live (RegisterRelocation.mapTable register source) target control edge agrees
    (RegisterRelocation.deterministic register faithful source source_valid) target_valid
    (RegisterRelocation.reaches_embed register faithful background source source_valid run)

end FiniteTrace

end Monodromy.Counter.Reversible.Glue

/-!
## Finite port identification

A partial matching identifies existing output and input positions. Original
edges and actions are retained, including in cyclic networks.
-/

noncomputable section

namespace Monodromy.Counter.Reversible.PortNetwork

variable {n q e : ℕ}

/-- A partial injective matching from exits with no outgoing edge to entries
with no incoming edge. Destinations are not themselves matched exits. -/
structure Wiring (original : Table n q e) where
  link : Fin q → Option (Fin q)
  terminal : ∀ {exit entry}, link exit = some entry → link entry = none
  injective : ∀ {first second entry}, link first = some entry →
    link second = some entry → first = second
  source_free : ∀ index, link (original index).source = none
  target_free : ∀ index exit, link exit ≠ some (original index).target

variable {original : Table n q e} (wiring : Wiring original)

/-- Matched exits disappear; their incident targets use the selected entry. -/
abbrev Node := {position : Fin q // wiring.link position = none}

def representative (position : Fin q) : Node wiring :=
  match selected : wiring.link position with
  | none => ⟨position, selected⟩
  | some entry => ⟨entry, wiring.terminal selected⟩

def size : ℕ := Fintype.card (Node wiring)

def nodeEquiv : Node wiring ≃ Fin (size wiring) := Fintype.equivFin _

def control (position : Fin q) : Fin (size wiring) :=
  nodeEquiv wiring (representative wiring position)

def table : Table n (size wiring) e := fun index =>
  Glue.mapEdge (control wiring) (original index)

@[simp] theorem table_source (index : Fin e) :
    (table wiring index).source = control wiring (original index).source := rfl

@[simp] theorem table_target (index : Fin e) :
    (table wiring index).target = control wiring (original index).target := rfl

@[simp] theorem table_action (index : Fin e) :
    (table wiring index).action = (original index).action := rfl

@[simp] theorem representative_unlinked (position : Fin q)
    (unlinked : wiring.link position = none) :
    (representative wiring position).val = position := by
  unfold representative
  split <;> simp_all

@[simp] theorem representative_linked (exit entry : Fin q)
    (linked : wiring.link exit = some entry) :
    (representative wiring exit).val = entry := by
  unfold representative
  split <;> simp_all

/-- Retained vertices are already their own representatives. -/
@[simp] theorem control_on_retained (position : Node wiring) :
    control wiring position.val = nodeEquiv wiring position := by
  apply congrArg (nodeEquiv wiring)
  apply Subtype.ext
  exact representative_unlinked wiring position.val position.property

/-- A wire is a literal equality of control positions, not a new transition. -/
theorem interface {exit entry : Fin q} (linked : wiring.link exit = some entry) :
    control wiring exit = control wiring entry := by
  apply congrArg (nodeEquiv wiring)
  apply Subtype.ext
  rw [representative_linked wiring exit entry linked,
    representative_unlinked wiring entry (wiring.terminal linked)]

theorem control_unlinked_injective {first second : Fin q}
    (first_free : wiring.link first = none) (second_free : wiring.link second = none)
    (same : control wiring first = control wiring second) : first = second := by
  have representatives := (nodeEquiv wiring).injective same
  have positions := congrArg Subtype.val representatives
  simpa only [representative_unlinked wiring first first_free,
    representative_unlinked wiring second second_free] using positions

/-- Sources are never normalized, so their incidence is preserved exactly. -/
theorem source_eq_iff (first second : Fin e) :
    control wiring (original first).source = control wiring (original second).source ↔
      (original first).source = (original second).source := by
  constructor
  · exact control_unlinked_injective wiring (wiring.source_free first) (wiring.source_free second)
  · exact congrArg (control wiring)

/-- Distinct original targets cannot merge: matched entries have no incoming edge,
and the exit-to-entry wiring is injective. -/
theorem target_eq_iff (first second : Fin e) :
    control wiring (original first).target = control wiring (original second).target ↔
      (original first).target = (original second).target := by
  constructor
  · intro same
    have positions := congrArg Subtype.val ((nodeEquiv wiring).injective same)
    cases left : wiring.link (original first).target with
    | none =>
      cases right : wiring.link (original second).target with
      | none => exact control_unlinked_injective wiring left right same
      | some entry =>
        have eq_entry : (original first).target = entry := by
          simpa only [representative_unlinked wiring _ left,
            representative_linked wiring _ _ right] using positions
        exact False.elim (wiring.target_free first (original second).target (eq_entry ▸ right))
    | some entry =>
      cases right : wiring.link (original second).target with
      | none =>
        have eq_entry : entry = (original second).target := by
          simpa only [representative_linked wiring _ _ left,
            representative_unlinked wiring _ right] using positions
        exact False.elim (wiring.target_free second (original first).target (eq_entry ▸ left))
      | some other =>
        have entries : entry = other := by
          simpa only [representative_linked wiring _ _ left,
            representative_linked wiring _ _ right] using positions
        exact wiring.injective left (entries ▸ right)
  · exact congrArg (control wiring)

/-- Gluing preserves the original forward local reversibility condition. -/
theorem deterministic (valid : Deterministic original) : Deterministic (table wiring) := by
  intro first second different same
  exact valid first second different ((source_eq_iff wiring first second).mp same)

/-- Gluing preserves the original backward local reversibility condition. -/
theorem targetCompatible (valid : TargetCompatible original) : TargetCompatible (table wiring) := by
  intro first second different same
  exact valid first second different ((target_eq_iff wiring first second).mp same)

/-- Every original live step remains an actual step of the graph with identified ports. -/
theorem step_map_live (valid : Deterministic original) {first last : State n q}
    (transition : step original first = some last) :
    step (table wiring) (Glue.mapState (control wiring) first) =
      some (Glue.mapState (control wiring) last) := by
  exact Glue.step_map_live original (table wiring) (control wiring) id
    (fun _ => rfl) valid (deterministic wiring valid) transition

/-- Finite runs compose through literal port equalities and preserve all registers. -/
theorem reaches_map_live (valid : Deterministic original) {first last : State n q}
    (run : StateTransition.Reaches (step original) first last) :
    StateTransition.Reaches (step (table wiring))
      (Glue.mapState (control wiring) first) (Glue.mapState (control wiring) last) := by
  exact Glue.reaches_map_live original (table wiring) (control wiring) id
    (fun _ => rfl) valid (deterministic wiring valid) run

/-- A positive run remains positive even when an exit is identified with its own entry. -/
theorem reaches1_map_live (valid : Deterministic original) {first last : State n q}
    (run : StateTransition.Reaches₁ (step original) first last) :
    StateTransition.Reaches₁ (step (table wiring))
      (Glue.mapState (control wiring) first) (Glue.mapState (control wiring) last) := by
  exact Relation.TransGen.lift (Glue.mapState (control wiring))
    (fun _ _ transition => step_map_live wiring valid transition) _ _ run

/-- Bounded selection of an entry from a finite, functional port relation. -/
def relationLink (connection : Fin q → Fin q → Prop) [DecidableRel connection]
    (exit : Fin q) : Option (Fin q) :=
  if connected : ∃ entry, connection exit entry then
    some (Fin.find (connection exit) connected)
  else none

theorem relationLink_some_iff (connection : Fin q → Fin q → Prop) [DecidableRel connection]
    (functional : ∀ {exit first second}, connection exit first →
      connection exit second → first = second) (exit entry : Fin q) :
    relationLink connection exit = some entry ↔ connection exit entry := by
  unfold relationLink
  split_ifs with connected
  · rw [Option.some.injEq]
    constructor
    · intro same
      rw [← same]
      exact Fin.find_spec connected
    · intro actual
      exact functional (Fin.find_spec connected) actual
  · constructor
    · intro impossible
      cases impossible
    · intro actual
      exact False.elim (connected ⟨entry, actual⟩)

theorem relationLink_none_iff (connection : Fin q → Fin q → Prop) [DecidableRel connection]
    (exit : Fin q) :
    relationLink connection exit = none ↔ ∀ entry, ¬ connection exit entry := by
  unfold relationLink
  split_ifs with connected
  · constructor
    · intro impossible
      cases impossible
    · intro absent
      exact False.elim (absent _ (Fin.find_spec connected))
  · exact ⟨fun _ entry actual => connected ⟨entry, actual⟩, fun _ => rfl⟩

/-- A partial matching of existing exits and entries supplies static wiring. -/
def Wiring.ofRelation (original : Table n q e)
    (connection : Fin q → Fin q → Prop) [DecidableRel connection]
    (functional : ∀ {exit first second}, connection exit first →
      connection exit second → first = second)
    (backward : ∀ {first second entry}, connection first entry →
      connection second entry → first = second)
    (terminal : ∀ {exit entry}, connection exit entry → ∀ next, ¬ connection entry next)
    (source_free : ∀ index entry, ¬ connection (original index).source entry)
    (target_free : ∀ index exit, ¬ connection exit (original index).target) :
    Wiring original where
  link := relationLink connection
  terminal := fun linked => (relationLink_none_iff connection _).mpr
    (terminal ((relationLink_some_iff connection functional _ _).mp linked))
  injective := fun first second => backward
    ((relationLink_some_iff connection functional _ _).mp first)
    ((relationLink_some_iff connection functional _ _).mp second)
  source_free := fun index => (relationLink_none_iff connection _).mpr (source_free index)
  target_free := fun index exit linked => target_free index exit
    ((relationLink_some_iff connection functional _ _).mp linked)

end Monodromy.Counter.Reversible.PortNetwork

end


/-!
## One reversible radix graph: unpacking and packing
-/

namespace Monodromy.Counter.Reversible.Radix

variable (p : ℕ) [NeZero p]

def size : ℕ := 3 + p * 8
def edges : ℕ := 3 + p * 9

abbrev Node := Fin 3 ⊕ (Fin p × Fin 8)
abbrev Arc := Fin 3 ⊕ (Fin p × Fin 9)

def nodeEquiv : Node p ≃ Fin (size p) :=
  (Equiv.sumCongr (Equiv.refl _) finProdFinEquiv).trans finSumFinEquiv

def arcEquiv : Arc p ≃ Fin (edges p) :=
  (Equiv.sumCongr (Equiv.refl _) finProdFinEquiv).trans finSumFinEquiv

def global (position : Fin 3) : Fin (size p) := nodeEquiv p (.inl position)
def block (remainder : Fin p) (phase : Fin 8) : Fin (size p) :=
  nodeEquiv p (.inr (remainder, phase))

def entry : Fin (size p) := global p 0
def finish (remainder : Fin p) : Fin (size p) := block p remainder 7

/-- A full block increments the quotient before returning to remainder zero. -/
def next (remainder : Fin p) : Node p :=
  if bound : remainder.val + 1 < p then .inr (⟨remainder.val + 1, bound⟩, 0)
  else .inl 1

omit [NeZero p] in
@[simp] theorem next_eq_block (remainder other : Fin p) (phase : Fin 8) :
    next p remainder = Sum.inr (other, phase) ↔
      remainder.val + 1 = other.val ∧ phase = 0 := by
  unfold next
  split_ifs with bound
  · simp only [Sum.inr.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨same, phase_eq⟩
      exact ⟨congrArg Fin.val same, phase_eq.symm⟩
    · rintro ⟨same, phase_eq⟩
      exact ⟨Fin.ext same, phase_eq.symm⟩
  · constructor
    · intro impossible
      cases impossible
    · rintro ⟨same, _⟩
      exact (bound (same ▸ other.isLt)).elim

omit [NeZero p] in
@[simp] theorem next_eq_global (remainder : Fin p) (position : Fin 3) :
    next p remainder = Sum.inl position ↔ position = 1 ∧ remainder.val + 1 = p := by
  unfold next
  split_ifs with bound
  · constructor
    · intro impossible
      cases impossible
    · rintro ⟨_, same⟩
      omega
  · simp only [Sum.inl.injEq]
    have last : remainder.val + 1 = p := by have := remainder.isLt; omega
    simp [last, eq_comm]

omit [NeZero p] in
theorem next_injective : Function.Injective (next p) := by
  intro first second same
  unfold next at same
  split_ifs at same <;> try cases same
  · have values := congrArg (fun node : Node p => node.elim (fun _ => 0) (fun pair => pair.1.val)) same
    apply Fin.ext
    dsimp at values
    omega
  · apply Fin.ext
    have := first.isLt
    have := second.isLt
    omega

omit [NeZero p] in
@[simp] theorem next_eq_next (first second : Fin p) : next p first = next p second ↔ first = second :=
  (next_injective p).eq_iff

/-- Only finite control data and unit shifts occur in the edge descriptions. -/
def origin : Arc p → Node p
  | .inl position => .inl position
  | .inr (remainder, edge) =>
      ![Sum.inr (remainder, 0), Sum.inr (remainder, 0), Sum.inr (remainder, 1),
        Sum.inr (remainder, 2), Sum.inr (remainder, 3), Sum.inr (remainder, 3),
        Sum.inr (remainder, 4), Sum.inr (remainder, 5), Sum.inr (remainder, 6)] edge

def destination : Arc p → Node p
  | .inl position => ![Sum.inr (0, 0), Sum.inl 2, Sum.inr (0, 0)] position
  | .inr (remainder, edge) =>
      ![Sum.inr (remainder, 2), Sum.inr (remainder, 1), next p remainder,
        Sum.inr (remainder, 3), Sum.inr (remainder, 7), Sum.inr (remainder, 4),
        Sum.inr (remainder, 5), Sum.inr (remainder, 6), Sum.inr (remainder, 3)] edge

def operation : Arc p → Action 2
  | .inl position => ![Action.test 1 true, Action.shift 1 1, Action.test 1 false] position
  | .inr (_, edge) =>
      ![Action.test 0 true, Action.test 0 false, Action.shift 0 (-1),
        Action.test 0 true, Action.test 1 true, Action.test 1 false,
        Action.shift 1 (-1), Action.shift 0 1, Action.test 0 false] edge

def table : Table 2 (size p) (edges p) := fun index =>
  let arc := (arcEquiv p).symm index
  ⟨nodeEquiv p (origin p arc), nodeEquiv p (destination p arc), operation p arc⟩

@[simp] theorem table_arc (arc : Arc p) :
    table p (arcEquiv p arc) =
      ⟨nodeEquiv p (origin p arc), nodeEquiv p (destination p arc), operation p arc⟩ := by
  simp [table]

theorem unitShift (index : Fin (edges p)) : Action.UnitShift (table p index).action := by
  obtain ⟨arc, rfl⟩ := (arcEquiv p).surjective index
  rw [table_arc]
  change Action.UnitShift (operation p arc)
  rcases arc with position | ⟨remainder, phase⟩
  · fin_cases position <;> simp [operation, Action.UnitShift]
  · fin_cases phase <;> simp [operation, Action.UnitShift]

theorem deterministic : Deterministic (table p) := by
  intro first second different same_source
  obtain ⟨first, rfl⟩ := (arcEquiv p).surjective first
  obtain ⟨second, rfl⟩ := (arcEquiv p).surjective second
  have distinct : first ≠ second := fun same => different (congrArg (arcEquiv p) same)
  have same : origin p first = origin p second := (nodeEquiv p).injective (by simpa using same_source)
  clear different same_source
  simp only [table_arc]
  change Action.Compatible (operation p first) (operation p second)
  rcases first with first | ⟨r, first⟩ <;>
    rcases second with second | ⟨s, second⟩ <;>
    fin_cases first <;> fin_cases second <;>
    simp_all [origin, operation, Action.Compatible]

theorem targetCompatible : TargetCompatible (table p) := by
  intro first second different same_target
  obtain ⟨first, rfl⟩ := (arcEquiv p).surjective first
  obtain ⟨second, rfl⟩ := (arcEquiv p).surjective second
  have distinct : first ≠ second := fun same => different (congrArg (arcEquiv p) same)
  have same : destination p first = destination p second :=
    (nodeEquiv p).injective (by simpa using same_target)
  clear different same_target
  simp only [table_arc]
  change Action.Compatible (operation p first) (operation p second)
  rcases first with first | ⟨r, first⟩ <;>
    rcases second with second | ⟨s, second⟩ <;>
    fin_cases first <;> fin_cases second <;>
    simp_all [destination, operation, Action.Compatible]
  all_goals
    have reversed := same.symm
    simp at reversed

def point (position : Fin (size p)) (left right : ℤ) : State 2 (size p) :=
  (position, ![left, right])


instance : NeZero (size p) := ⟨by simp [size]⟩

/-- The finite port determines the conditions required by singleton tests and decrements. -/
def admissible : Node p → ℤ → ℤ → Prop
  | .inl position, _, right => ![right = 0, True, right ≠ 0] position
  | .inr (_, phase), left, right =>
      ![True, 0 < left, left = 0, True, 0 < right, True, left ≠ 0, True] phase

def Valid (state : State 2 (size p)) : Prop :=
  0 ≤ state.2 0 ∧ 0 ≤ state.2 1 ∧
    admissible p ((nodeEquiv p).symm state.1) (state.2 0) (state.2 1)

omit [NeZero p] in
theorem valid_input (input : ℕ) : Valid p (point p (entry p) input 0) := by
  simp [Valid, point, entry, global, admissible]

omit [NeZero p] in
theorem valid_output (remainder : Fin p) (quotient : ℕ) :
    Valid p (point p (finish p remainder) quotient 0) := by
  simp [Valid, point, finish, block, admissible]

theorem valid_step {first last : State 2 (size p)}
    (valid : Valid p first) (transition : step (table p) first = some last) : Valid p last := by
  obtain ⟨index, enabled, rfl⟩ := (step_iff (table p) (deterministic p)).mp transition
  obtain ⟨arc, rfl⟩ := (arcEquiv p).surjective index
  rcases first with ⟨position, values⟩
  have position_eq : nodeEquiv p (origin p arc) = position := by simpa using enabled.1
  subst position
  have action_enabled : (operation p arc).enabled values := by simpa using enabled.2
  clear enabled
  rcases arc with index | ⟨remainder, index⟩ <;> fin_cases index <;>
    simp_all [Valid, admissible, table_arc, Edge.execute, Action.apply, Action.enabled,
      origin, destination, operation]
  all_goals try omega
  all_goals unfold next; split_ifs <;> simp_all <;> omega

/-- The existing finite-port invariant is stable under the actual reversed graph. -/
theorem valid_reverse_step {first last : State 2 (size p)}
    (valid : Valid p first) (transition : step (reverseTable (table p)) first = some last) :
    Valid p last := by
  obtain ⟨index, enabled, rfl⟩ :=
    (step_iff _ (reverseTable_deterministic _ (targetCompatible p))).mp transition
  obtain ⟨arc, rfl⟩ := (arcEquiv p).surjective index
  rcases first with ⟨position, values⟩
  have position_eq : nodeEquiv p (destination p arc) = position := by
    simpa only [reverseTable, reverseEdge, table_arc, Edge.enabled] using enabled.1
  subst position
  have action_enabled : (reverseAction (operation p arc)).enabled values := by
    simpa only [reverseTable, reverseEdge, table_arc] using enabled.2
  clear enabled
  rcases arc with index | ⟨remainder, index⟩ <;> fin_cases index <;>
    simp_all [Valid, admissible, reverseTable, reverseEdge, table_arc, Edge.execute,
      reverseAction, Action.apply, Action.enabled, origin, destination, operation]
  all_goals try omega

omit [NeZero p] in
theorem origin_ne_finish (arc : Arc p) (remainder : Fin p) :
    origin p arc ≠ Sum.inr (remainder, (7 : Fin 8)) := by
  rcases arc with position | ⟨other, index⟩
  · simp [origin]
  · fin_cases index <;> simp [origin]

theorem no_outgoing_finish (remainder : Fin p) :
    ¬ ∃ index, (table p index).source = finish p remainder := by
  rintro ⟨index, source⟩
  obtain ⟨arc, rfl⟩ := (arcEquiv p).surjective index
  have same : origin p arc = Sum.inr (remainder, (7 : Fin 8)) := by
    apply (nodeEquiv p).injective
    simpa only [table_arc, finish, block] using source
  exact origin_ne_finish p arc remainder same

private theorem available (arc : Arc p) (values : Fin 2 → ℤ)
    (enabled : (operation p arc).enabled values) :
    ∃ index, (table p index).enabled (nodeEquiv p (origin p arc), values) := by
  refine ⟨arcEquiv p arc, ?_⟩
  simpa only [table_arc, Edge.enabled, true_and] using enabled

theorem completeOn : CompleteOn (table p) (Valid p) := by
  rintro ⟨position, values⟩ valid outgoing
  obtain ⟨node, rfl⟩ := (nodeEquiv p).surjective position
  have local_domain : admissible p node (values 0) (values 1) := by simpa [Valid] using valid.2.2
  rcases node with position | ⟨remainder, phase⟩
  · fin_cases position
    · simpa [origin] using available p (.inl 0) values (by simpa [operation, Action.enabled, admissible] using local_domain)
    · simpa [origin] using available p (.inl 1) values (by simp [operation, Action.enabled])
    · simpa [origin] using available p (.inl 2) values (by simpa [operation, Action.enabled, admissible] using local_domain)
  · fin_cases phase
    · by_cases zero : values 0 = 0
      · simpa [origin] using available p (.inr (remainder, 0)) values (by simp [operation, Action.enabled, zero])
      · simpa [origin] using available p (.inr (remainder, 1)) values (by simp [operation, Action.enabled, zero])
    · simpa [origin] using available p (.inr (remainder, 2)) values (by simp [operation, Action.enabled])
    · simpa [origin] using available p (.inr (remainder, 3)) values (by simpa [operation, Action.enabled, admissible] using local_domain)
    · by_cases zero : values 1 = 0
      · simpa [origin] using available p (.inr (remainder, 4)) values (by simp [operation, Action.enabled, zero])
      · simpa [origin] using available p (.inr (remainder, 5)) values (by simp [operation, Action.enabled, zero])
    · simpa [origin] using available p (.inr (remainder, 6)) values (by simp [operation, Action.enabled])
    · simpa [origin] using available p (.inr (remainder, 7)) values (by simp [operation, Action.enabled])
    · simpa [origin] using available p (.inr (remainder, 8)) values (by simpa [operation, Action.enabled, admissible] using local_domain)
    · exact (no_outgoing_finish p remainder outgoing).elim


private theorem update_left (left right value : ℤ) :
    Function.update ![left, right] 0 value = ![value, right] := by
  funext index
  fin_cases index <;> simp

private theorem update_right (left right value : ℤ) :
    Function.update ![left, right] 1 value = ![left, value] := by
  funext index
  fin_cases index <;> simp

private theorem move (arc : Arc p) (first last : State 2 (size p))
    (enabled : (table p (arcEquiv p arc)).enabled first)
    (result : (table p (arcEquiv p arc)).execute first = last) :
    StateTransition.Reaches (step (table p)) first last := by
  apply Relation.ReflTransGen.single
  exact (step_iff (table p) (deterministic p)).mpr ⟨arcEquiv p arc, enabled, result⟩

/-- Consuming one unit reaches the next remainder port, before any quotient carry. -/
theorem consume_step (remainder : Fin p) (input accumulator : ℕ) :
    StateTransition.Reaches (step (table p))
      (point p (block p remainder 0) (input + 1 : ℕ) accumulator)
      (point p (nodeEquiv p (next p remainder)) input accumulator) := by
  have reading : StateTransition.Reaches (step (table p))
      (point p (block p remainder 0) (input + 1 : ℕ) accumulator)
      (point p (block p remainder 1) (input + 1 : ℕ) accumulator) := by
    apply move p (.inr (remainder, 1))
    · simp [table_arc, origin, operation, Edge.enabled, Action.enabled, point, block]
      omega
    · simp [table_arc, destination, operation, Edge.execute, Action.apply, point, block]
  apply reading.trans
  apply move p (.inr (remainder, 2))
  · simp [table_arc, origin, operation, Edge.enabled, Action.enabled, point, block]
  · simp [table_arc, destination, operation, Edge.execute, Action.apply, point, update_left]

/-- A completed radix block increments the quotient and re-enters remainder zero. -/
theorem carry_reaches (input accumulator : ℕ) :
    StateTransition.Reaches (step (table p))
      (point p (global p 1) input accumulator)
      (point p (block p 0 0) input (accumulator + 1 : ℕ)) := by
  have increment : StateTransition.Reaches (step (table p))
      (point p (global p 1) input accumulator)
      (point p (global p 2) input (accumulator + 1 : ℕ)) := by
    apply move p (.inl 1)
    · simp [table_arc, origin, operation, Edge.enabled, Action.enabled, point, global]
    · simp [table_arc, destination, operation, Edge.execute, Action.apply, point, global, update_right]
  apply increment.trans
  apply move p (.inl 2)
  · simp [table_arc, origin, operation, Edge.enabled, Action.enabled, point, global]
    omega
  · simp [table_arc, destination, operation, Edge.execute, Action.apply, point, block]

/-- The quotient accumulates in the second register; the remainder stays in finite control. -/
theorem consume_reaches (input accumulator : ℕ) (remainder : Fin p) :
    StateTransition.Reaches (step (table p))
      (point p (block p remainder 0) input accumulator)
      (point p (block p (Counter.DivMod.residue p (input + remainder.val)) 2) 0
        (accumulator + (input + remainder.val) / p : ℕ)) := by
  change Relation.ReflTransGen (fun first last => last ∈ step (table p) first) _ _
  induction input generalizing accumulator remainder with
  | zero =>
      have stopped : StateTransition.Reaches (step (table p))
          (point p (block p remainder 0) 0 accumulator)
          (point p (block p remainder 2) 0 accumulator) := by
        apply move p (.inr (remainder, 0))
        · simp [table_arc, origin, operation, Edge.enabled, Action.enabled, point, block]
        · simp [table_arc, destination, operation, Edge.execute, Action.apply, point, block]
      simpa only [StateTransition.Reaches, Nat.zero_add, Counter.DivMod.residue_small,
        Nat.div_eq_of_lt remainder.isLt, Nat.add_zero, Int.natCast_zero] using stopped
  | succ input recursive =>
      by_cases bound : remainder.val + 1 < p
      · let successor : Fin p := ⟨remainder.val + 1, bound⟩
        have consumed : StateTransition.Reaches (step (table p))
            (point p (block p remainder 0) (input + 1 : ℕ) accumulator)
            (point p (block p successor 0) input accumulator) := by
          simpa only [next, dite_eq_left bound, block] using consume_step p remainder input accumulator
        have run := consumed.trans (recursive accumulator successor)
        have same_sum : input + successor.val = input + 1 + remainder.val := by
          dsimp [successor]
          omega
        simpa only [same_sum] using run
      · have last : remainder.val + 1 = p := by omega
        have consumed : StateTransition.Reaches (step (table p))
            (point p (block p remainder 0) (input + 1 : ℕ) accumulator)
            (point p (global p 1) input accumulator) := by
          simpa only [next, dite_eq_right bound, global] using consume_step p remainder input accumulator
        have run := consumed.trans
          ((carry_reaches p input accumulator).trans (recursive (accumulator + 1) 0))
        have same_sum : input + 1 + remainder.val = input + p := by omega
        have residue_eq : Counter.DivMod.residue p (input + p) = Counter.DivMod.residue p input := by
          apply Fin.ext
          exact Nat.add_mod_right input p
        simpa only [Fin.val_zero, Nat.add_zero, same_sum, residue_eq,
          Nat.add_div_right input (Nat.pos_of_ne_zero (NeZero.ne p)),
          Nat.add_assoc, Nat.add_comm 1 (input / p)] using run

/-- One transfer cycle preserves the remainder address and returns one unit to the first register. -/
theorem transfer_cycle (remainder : Fin p) (input accumulator : ℕ) :
    StateTransition.Reaches (step (table p))
      (point p (block p remainder 3) accumulator (input + 1 : ℕ))
      (point p (block p remainder 3) (accumulator + 1 : ℕ) input) := by
  have reading : StateTransition.Reaches (step (table p))
      (point p (block p remainder 3) accumulator (input + 1 : ℕ))
      (point p (block p remainder 4) accumulator (input + 1 : ℕ)) := by
    apply move p (.inr (remainder, 5))
    · simp [table_arc, origin, operation, Edge.enabled, Action.enabled, point, block]
      omega
    · simp [table_arc, destination, operation, Edge.execute, Action.apply, point, block]
  have decrement : StateTransition.Reaches (step (table p))
      (point p (block p remainder 4) accumulator (input + 1 : ℕ))
      (point p (block p remainder 5) accumulator input) := by
    apply move p (.inr (remainder, 6))
    · simp [table_arc, origin, operation, Edge.enabled, Action.enabled, point, block]
    · simp [table_arc, destination, operation, Edge.execute, Action.apply, point, block, update_right]
  have increment : StateTransition.Reaches (step (table p))
      (point p (block p remainder 5) accumulator input)
      (point p (block p remainder 6) (accumulator + 1 : ℕ) input) := by
    apply move p (.inr (remainder, 7))
    · simp [table_arc, origin, operation, Edge.enabled, Action.enabled, point, block]
    · simp [table_arc, destination, operation, Edge.execute, Action.apply, point, block, update_left]
  have returning : StateTransition.Reaches (step (table p))
      (point p (block p remainder 6) (accumulator + 1 : ℕ) input)
      (point p (block p remainder 3) (accumulator + 1 : ℕ) input) := by
    apply move p (.inr (remainder, 8))
    · simp [table_arc, origin, operation, Edge.enabled, Action.enabled, point, block]
      omega
    · simp [table_arc, destination, operation, Edge.execute, Action.apply, point, block]
  exact reading.trans (decrement.trans (increment.trans returning))

/-- Transferring the quotient back clears the second register. -/
theorem transfer_reaches (remainder : Fin p) (input accumulator : ℕ) :
    StateTransition.Reaches (step (table p))
      (point p (block p remainder 3) accumulator input)
      (point p (finish p remainder) (accumulator + input : ℕ) 0) := by
  change Relation.ReflTransGen (fun first last => last ∈ step (table p) first) _ _
  induction input generalizing accumulator with
  | zero =>
      have stopped : StateTransition.Reaches (step (table p))
          (point p (block p remainder 3) accumulator 0)
          (point p (finish p remainder) accumulator 0) := by
        apply move p (.inr (remainder, 4))
        · simp [table_arc, origin, operation, Edge.enabled, Action.enabled, point, block]
        · simp [table_arc, destination, operation, Edge.execute, Action.apply, point, finish, block]
      simpa only [StateTransition.Reaches, Nat.add_zero, Int.natCast_zero] using stopped
  | succ input recursive =>
      have run := (transfer_cycle p remainder input accumulator).trans (recursive (accumulator + 1))
      simpa only [Nat.add_assoc, Nat.add_comm 1 input] using run

/-- One fixed table computes quotient and remainder for every natural input. -/
theorem reaches_result (input : ℕ) :
    StateTransition.Reaches (step (table p)) (point p (entry p) input 0)
      (point p (finish p (Counter.DivMod.residue p input)) (input / p : ℕ) 0) := by
  have entering : StateTransition.Reaches (step (table p))
      (point p (entry p) input 0) (point p (block p 0 0) input 0) := by
    apply move p (.inl 0)
    · simp [table_arc, origin, operation, Edge.enabled, Action.enabled, point, entry, global]
    · simp [table_arc, destination, operation, Edge.execute, Action.apply, point, block]
  have consumed := consume_reaches p input 0 0
  simp only [Fin.val_zero, Nat.add_zero, Nat.zero_add] at consumed
  have transfer_entry : StateTransition.Reaches (step (table p))
      (point p (block p (Counter.DivMod.residue p input) 2) 0 (input / p : ℕ))
      (point p (block p (Counter.DivMod.residue p input) 3) 0 (input / p : ℕ)) := by
    apply move p (.inr (Counter.DivMod.residue p input, 3))
    · simp [table_arc, origin, operation, Edge.enabled, Action.enabled, point, block]
    · simp [table_arc, destination, operation, Edge.execute, Action.apply, point, block]
  have transferred := transfer_reaches p (Counter.DivMod.residue p input) (input / p) 0
  simp only [Nat.zero_add] at transferred
  exact entering.trans (consumed.trans (transfer_entry.trans transferred))

theorem halt_result (remainder : Fin p) (quotient : ℕ) :
    step (table p) (point p (finish p remainder) quotient 0) = none := by
  rw [step_none_iff]
  rintro ⟨index, enabled⟩
  exact no_outgoing_finish p remainder ⟨index, enabled.1⟩

theorem eval_result (input : ℕ) :
    eval (table p) (point p (entry p) input 0) =
      Part.some (point p (finish p (Counter.DivMod.residue p input)) (input / p : ℕ) 0) := by
  apply Part.eq_some_iff.mpr
  exact StateTransition.mem_eval.mpr ⟨reaches_result p input, halt_result p _ _⟩

/-- The same three-root execution realizes the quotient, with its remainder in finite control. -/
theorem native_eval (input : ℕ) :
    (ReversibleCompilation.haltingProgram (table p) (deterministic p) (targetCompatible p)).eval
      (ReversibleCompilation.iota (e := edges p) (point p (entry p) input 0)) =
      Part.some (ReversibleCompilation.iota (e := edges p)
        (point p (finish p (Counter.DivMod.residue p input)) (input / p : ℕ) 0)) := by
  have stable : Stable (table p) (Valid p) := fun {_ _} valid transition => valid_step p valid transition
  rw [ReversibleCompilation.eval_iota_on (table p) (deterministic p) (targetCompatible p)
    (Valid p) (completeOn p) stable _ (valid_input p input), eval_result p input]
  rfl


/-- The original entry has no incoming edge, so the reversed graph stops there. -/
theorem no_incoming_entry (index : Fin (edges p)) : (table p index).target ≠ entry p := by
  obtain ⟨arc, rfl⟩ := (arcEquiv p).surjective index
  intro incoming
  have same : destination p arc = Sum.inl (0 : Fin 3) := by
    apply (nodeEquiv p).injective
    simpa only [table_arc, entry, global] using incoming
  rcases arc with index | ⟨remainder, index⟩ <;> fin_cases index <;> simp [destination] at same

/-- Reversing the same radix graph packs a quotient and its finite remainder. -/
theorem reverse_pack (quotient : ℕ) (remainder : Fin p) :
    StateTransition.Reaches (step (reverseTable (table p)))
      (point p (finish p remainder) quotient 0)
      (point p (entry p) (p * quotient + remainder.val : ℕ) 0) := by
  have run := reaches_reverse (table p) (deterministic p) (targetCompatible p)
    (reaches_result p (p * quotient + remainder.val))
  have digit : Counter.DivMod.residue p (p * quotient + remainder.val) = remainder := by
    apply Fin.ext
    exact (Nat.mul_add_mod_self_left p quotient remainder.val).trans (Nat.mod_eq_of_lt remainder.isLt)
  have divide : (p * quotient + remainder.val) / p = quotient := by
    rw [Nat.add_comm, Nat.add_mul_div_left remainder.val quotient (Nat.pos_of_ne_zero (NeZero.ne p)),
      Nat.div_eq_of_lt remainder.isLt, Nat.zero_add]
  simpa only [digit, divide] using run

/-- Packing is generated by the reversed fixed table and the same three-root compiler. -/
theorem native_reverse_pack (quotient : ℕ) (remainder : Fin p) :
    let reversed := reverseTable (table p)
    let native := ReversibleCompilation.haltingProgram reversed
      (reverseTable_deterministic _ (targetCompatible p))
      (reverseTable_targetCompatible _ (deterministic p))
    native.eval (ReversibleCompilation.iota (e := edges p) (point p (finish p remainder) quotient 0)) =
      Part.some (ReversibleCompilation.iota (e := edges p)
        (point p (entry p) (p * quotient + remainder.val : ℕ) 0)) := by
  dsimp only
  apply ReversibleCompilation.eval_of_reaches
  · exact reverse_pack p quotient remainder
  · rintro ⟨index, incoming⟩
    exact no_incoming_entry p index incoming

end Monodromy.Counter.Reversible.Radix

/-!
## Read-only remainder observation by identified radix ports
-/

noncomputable section

namespace Monodromy.Counter.Reversible.RadixObservation

variable (p m : ℕ) [NeZero p]

abbrev RawNode := (Fin 2 × Fin m) × Fin (Radix.size p)
abbrev RawArc := (Fin 2 × Fin m) × Fin (Radix.edges p)

def rawSize : ℕ := (2 * m) * Radix.size p
def edges : ℕ := (2 * m) * Radix.edges p

def rawNodeEquiv : RawNode p m ≃ Fin (rawSize p m) :=
  (Equiv.prodCongr finProdFinEquiv (Equiv.refl _)).trans finProdFinEquiv

def arcEquiv : RawArc p m ≃ Fin (edges p m) :=
  (Equiv.prodCongr finProdFinEquiv (Equiv.refl _)).trans finProdFinEquiv

def rawControl (direction : Fin 2) (row : Fin m) (position : Fin (Radix.size p)) :
    Fin (rawSize p m) := rawNodeEquiv p m ((direction, row), position)

def component (direction : Fin 2) : Table 2 (Radix.size p) (Radix.edges p) :=
  if direction = 0 then Radix.table p else reverseTable (Radix.table p)

private theorem component_deterministic (direction : Fin 2) : Deterministic (component p direction) := by
  unfold component
  split_ifs
  · exact Radix.deterministic p
  · exact reverseTable_deterministic _ (Radix.targetCompatible p)

private theorem component_targetCompatible (direction : Fin 2) :
    TargetCompatible (component p direction) := by
  unfold component
  split_ifs
  · exact Radix.targetCompatible p
  · exact reverseTable_targetCompatible _ (Radix.deterministic p)

def rawTable : Table 2 (rawSize p m) (edges p m) := fun index =>
  let arc := (arcEquiv p m).symm index
  Glue.mapEdge (rawControl p m arc.1.1 arc.1.2) (component p arc.1.1 arc.2)

@[simp] theorem rawTable_arc (owner : Fin 2 × Fin m) (index : Fin (Radix.edges p)) :
    rawTable p m (arcEquiv p m (owner, index)) =
      Glue.mapEdge (rawControl p m owner.1 owner.2) (component p owner.1 index) := by
  simp only [rawTable, Equiv.symm_apply_apply]

omit [NeZero p] in
private theorem rawControl_eq_iff (first second : Fin 2 × Fin m)
    (initial final : Fin (Radix.size p)) :
    rawControl p m first.1 first.2 initial = rawControl p m second.1 second.2 final ↔
      first = second ∧ initial = final := by
  change rawNodeEquiv p m (first, initial) = rawNodeEquiv p m (second, final) ↔ _
  rw [(rawNodeEquiv p m).injective.eq_iff, Prod.mk.injEq]

private theorem raw_deterministic : Deterministic (rawTable p m) := by
  intro first second different same
  obtain ⟨⟨owner, first⟩, rfl⟩ := (arcEquiv p m).surjective first
  obtain ⟨⟨other, second⟩, rfl⟩ := (arcEquiv p m).surjective second
  simp only [rawTable_arc, Glue.mapEdge] at same ⊢
  have ports := (rawControl_eq_iff p m owner other _ _).mp same
  rcases ports with ⟨rfl, positions⟩
  exact component_deterministic p owner.1 first second
    (fun equal => different (by subst second; rfl)) positions

private theorem raw_targetCompatible : TargetCompatible (rawTable p m) := by
  intro first second different same
  obtain ⟨⟨owner, first⟩, rfl⟩ := (arcEquiv p m).surjective first
  obtain ⟨⟨other, second⟩, rfl⟩ := (arcEquiv p m).surjective second
  simp only [rawTable_arc, Glue.mapEdge] at same ⊢
  have ports := (rawControl_eq_iff p m owner other _ _).mp same
  rcases ports with ⟨rfl, positions⟩
  exact component_targetCompatible p owner.1 first second
    (fun equal => different (by subst second; rfl)) positions

/-- A finite node address exposes whether it is a radix finish port. -/
def finishQuery (position : Fin (Radix.size p)) : Option (Fin p) :=
  match (Radix.nodeEquiv p).symm position with
  | .inl _ => none
  | .inr (remainder, phase) => if phase = 7 then some remainder else none

omit [NeZero p] in
@[simp] theorem finishQuery_finish (remainder : Fin p) :
    finishQuery p (Radix.finish p remainder) = some remainder := by
  simp [finishQuery, Radix.finish, Radix.block]

omit [NeZero p] in
theorem finishQuery_some {position : Fin (Radix.size p)} {remainder : Fin p}
    (selected : finishQuery p position = some remainder) : position = Radix.finish p remainder := by
  unfold finishQuery at selected
  cases shape : (Radix.nodeEquiv p).symm position with
  | inl global => simp [shape] at selected
  | inr pair =>
    rcases pair with ⟨symbol, phase⟩
    rw [shape] at selected
    dsimp only at selected
    split_ifs at selected with last
    · have symbols := Option.some.inj selected
      subst symbol
      apply (Radix.nodeEquiv p).symm.injective
      simp only [Radix.finish, Radix.block, Equiv.symm_apply_apply, shape, last]

private theorem finishQuery_source (index : Fin (Radix.edges p)) :
    finishQuery p (Radix.table p index).source = none := by
  cases selected : finishQuery p (Radix.table p index).source with
  | none => rfl
  | some remainder =>
    exact (Radix.no_outgoing_finish p remainder ⟨index, finishQuery_some p selected⟩).elim

/-- Only forward finish ports are matched, directly to the corresponding reversed copy. -/
def link (permutation : Fin p → Equiv.Perm (Fin m)) (position : Fin (rawSize p m)) :
    Option (Fin (rawSize p m)) :=
  let node := (rawNodeEquiv p m).symm position
  if node.1.1 = 0 then
    (finishQuery p node.2).map fun remainder => rawControl p m 1 (permutation remainder node.1.2) node.2
  else none

omit [NeZero p] in
@[simp] theorem link_backward (permutation : Fin p → Equiv.Perm (Fin m))
    (row : Fin m) (position : Fin (Radix.size p)) :
    link p m permutation (rawControl p m 1 row position) = none := by
  simp [link, rawControl]

omit [NeZero p] in
@[simp] theorem link_finish (permutation : Fin p → Equiv.Perm (Fin m))
    (row : Fin m) (remainder : Fin p) :
    link p m permutation (rawControl p m 0 row (Radix.finish p remainder)) =
      some (rawControl p m 1 (permutation remainder row) (Radix.finish p remainder)) := by
  simp [link, rawControl]

omit [NeZero p] in
/-- Every link is a finish-port equality; its remainder is an address in a fixed finite table. -/
theorem link_some (permutation : Fin p → Equiv.Perm (Fin m))
    {exit entry : Fin (rawSize p m)} (linked : link p m permutation exit = some entry) :
    ∃ row remainder, exit = rawControl p m 0 row (Radix.finish p remainder) ∧
      entry = rawControl p m 1 (permutation remainder row) (Radix.finish p remainder) := by
  obtain ⟨⟨⟨direction, row⟩, position⟩, rfl⟩ := (rawNodeEquiv p m).surjective exit
  change link p m permutation (rawControl p m direction row position) = some entry at linked
  simp only [link, rawControl, Equiv.symm_apply_apply] at linked
  split_ifs at linked with forward
  · cases selected : finishQuery p position with
    | none => simp [selected] at linked
    | some remainder =>
      simp only [selected, Option.map_some] at linked
      have target : rawControl p m 1 (permutation remainder row) position = entry :=
        Option.some.inj linked
      have position_eq := finishQuery_some p selected
      exact ⟨row, remainder, by simp only [forward, position_eq, rawControl],
        by simpa only [position_eq] using target.symm⟩

/-- Finite wiring is the only new data; the two existing edge families are unchanged. -/
def wiring (permutation : Fin p → Equiv.Perm (Fin m)) : PortNetwork.Wiring (rawTable p m) where
  link := link p m permutation
  terminal := by
    intro exit entry linked
    obtain ⟨row, remainder, rfl, rfl⟩ := link_some p m permutation linked
    exact link_backward p m permutation _ _
  injective := by
    intro first second entry left right
    obtain ⟨row, remainder, rfl, equal_left⟩ := link_some p m permutation left
    obtain ⟨other, symbol, rfl, equal_right⟩ := link_some p m permutation right
    have ports := (rawControl_eq_iff p m (1, permutation remainder row)
      (1, permutation symbol other) _ _).mp (equal_left.symm.trans equal_right)
    have symbols : remainder = symbol := by
      apply Fin.ext
      have raw := (Radix.nodeEquiv p).injective ports.2
      exact congrArg (fun node : Radix.Node p => node.elim (fun _ => 0) (fun pair => pair.1.val)) raw
    subst symbol
    have rows := (permutation remainder).injective (congrArg Prod.snd ports.1)
    rw [rows]
  source_free := by
    intro index
    obtain ⟨⟨⟨direction, row⟩, index⟩, rfl⟩ := (arcEquiv p m).surjective index
    fin_cases direction <;> simp [rawTable_arc, Glue.mapEdge, component, link, rawControl, finishQuery_source]
  target_free := by
    intro index exit linked
    obtain ⟨row, remainder, _, equal⟩ := link_some p m permutation linked
    obtain ⟨⟨⟨direction, other⟩, index⟩, rfl⟩ := (arcEquiv p m).surjective index
    fin_cases direction
    · simp only [rawTable_arc, Glue.mapEdge] at equal
      change rawControl p m 0 other (Radix.table p index).target =
        rawControl p m 1 (permutation remainder row) (Radix.finish p remainder) at equal
      have impossible : ((0 : Fin 2), other) = (1, permutation remainder row) :=
        ((rawControl_eq_iff p m (0, other) (1, permutation remainder row) _ _).mp equal).1
      exact (by simpa using congrArg Prod.fst impossible)
    · simp only [rawTable_arc, Glue.mapEdge] at equal
      change rawControl p m 1 other (Radix.table p index).source =
        rawControl p m 1 (permutation remainder row) (Radix.finish p remainder) at equal
      have ports := (rawControl_eq_iff p m (1, other) (1, permutation remainder row) _ _).mp equal
      exact Radix.no_outgoing_finish p remainder ⟨index, ports.2⟩

def size (permutation : Fin p → Equiv.Perm (Fin m)) : ℕ := PortNetwork.size (wiring p m permutation)

def table (permutation : Fin p → Equiv.Perm (Fin m)) : Table 2 (size p m permutation) (edges p m) :=
  PortNetwork.table (wiring p m permutation)

def front (permutation : Fin p → Equiv.Perm (Fin m)) (row : Fin m)
    (position : Fin (Radix.size p)) : Fin (size p m permutation) :=
  PortNetwork.control (wiring p m permutation) (rawControl p m 0 row position)

def back (permutation : Fin p → Equiv.Perm (Fin m)) (row : Fin m)
    (position : Fin (Radix.size p)) : Fin (size p m permutation) :=
  PortNetwork.control (wiring p m permutation) (rawControl p m 1 row position)

theorem deterministic (permutation : Fin p → Equiv.Perm (Fin m)) : Deterministic (table p m permutation) :=
  PortNetwork.deterministic _ (raw_deterministic p m)

theorem targetCompatible (permutation : Fin p → Equiv.Perm (Fin m)) : TargetCompatible (table p m permutation) :=
  PortNetwork.targetCompatible _ (raw_targetCompatible p m)

theorem front_finish (permutation : Fin p → Equiv.Perm (Fin m)) (row : Fin m) (remainder : Fin p) :
    front p m permutation row (Radix.finish p remainder) =
      back p m permutation (permutation remainder row) (Radix.finish p remainder) :=
  PortNetwork.interface _ (link_finish p m permutation row remainder)

@[simp] theorem table_front (permutation : Fin p → Equiv.Perm (Fin m))
    (row : Fin m) (index : Fin (Radix.edges p)) :
    table p m permutation (arcEquiv p m ((0, row), index)) =
      Glue.mapEdge (front p m permutation row) (Radix.table p index) := by
  change Glue.mapEdge (PortNetwork.control (wiring p m permutation))
    (rawTable p m (arcEquiv p m ((0, row), index))) = _
  rw [rawTable_arc]
  simp only [component, ite_true]
  rfl

@[simp] theorem table_back (permutation : Fin p → Equiv.Perm (Fin m))
    (row : Fin m) (index : Fin (Radix.edges p)) :
    table p m permutation (arcEquiv p m ((1, row), index)) =
      Glue.mapEdge (back p m permutation row) (reverseTable (Radix.table p) index) := by
  change Glue.mapEdge (PortNetwork.control (wiring p m permutation))
    (rawTable p m (arcEquiv p m ((1, row), index))) = _
  rw [rawTable_arc]
  simp only [component, Fin.isValue, Fin.reduceEq, ite_false]
  rfl

def inputPort (permutation : Fin p → Equiv.Perm (Fin m)) (row : Fin m) :
    Fin (size p m permutation) := front p m permutation row (Radix.entry p)

def outputPort (permutation : Fin p → Equiv.Perm (Fin m)) (row : Fin m) :
    Fin (size p m permutation) := back p m permutation row (Radix.entry p)

def point (permutation : Fin p → Equiv.Perm (Fin m)) (position : Fin (size p m permutation))
    (left right : ℤ) : State 2 (size p m permutation) := (position, ![left, right])

instance [NeZero m] (permutation : Fin p → Equiv.Perm (Fin m)) : NeZero (size p m permutation) := by
  change NeZero (Fintype.card (PortNetwork.Node (wiring p m permutation)))
  exact ⟨Nat.ne_of_gt (Fintype.card_pos_iff.mpr
    ⟨PortNetwork.representative (wiring p m permutation) (rawControl p m 1 0 (Radix.entry p))⟩)⟩

/-- Output boundaries retain their absence of outgoing edges after port identification. -/
theorem no_outgoing_output (permutation : Fin p → Equiv.Perm (Fin m)) (row : Fin m) :
    ¬ ∃ index, (table p m permutation index).source = outputPort p m permutation row := by
  rintro ⟨index, same⟩
  have raw_equal := PortNetwork.control_unlinked_injective (wiring p m permutation)
    ((wiring p m permutation).source_free index)
    (link_backward p m permutation row (Radix.entry p)) same
  obtain ⟨⟨owner, index⟩, rfl⟩ := (arcEquiv p m).surjective index
  simp only [rawTable_arc, Glue.mapEdge] at raw_equal
  have ports := (rawControl_eq_iff p m owner (1, row) _ _).mp raw_equal
  rcases ports with ⟨rfl, position⟩
  exact Radix.no_incoming_entry p index
    (by simpa only [component, Fin.isValue, Fin.reduceEq, ite_false, reverseTable, reverseEdge] using position)

/-- The actual remainder port selects a reversed copy, which restores both counter values. -/
theorem reaches_result (permutation : Fin p → Equiv.Perm (Fin m)) (row : Fin m) (value : ℕ) :
    StateTransition.Reaches (step (table p m permutation))
      (point p m permutation (inputPort p m permutation row) value 0)
      (point p m permutation (outputPort p m permutation (permutation (Counter.DivMod.residue p value) row)) value 0) := by
  have forward := Glue.reaches_map_live (Radix.table p) (table p m permutation)
    (front p m permutation row) (fun index => arcEquiv p m ((0, row), index))
    (fun index => table_front p m permutation row index)
    (Radix.deterministic p) (deterministic p m permutation) (Radix.reaches_result p value)
  have backward := Glue.reaches_map_live (reverseTable (Radix.table p)) (table p m permutation)
    (back p m permutation (permutation (Counter.DivMod.residue p value) row))
    (fun index => arcEquiv p m ((1, permutation (Counter.DivMod.residue p value) row), index))
    (fun index => table_back p m permutation _ index)
    (reverseTable_deterministic _ (Radix.targetCompatible p)) (deterministic p m permutation)
    (Radix.reverse_pack p (value / p) (Counter.DivMod.residue p value))
  change StateTransition.Reaches (step (table p m permutation))
    (point p m permutation (inputPort p m permutation row) value 0)
    (point p m permutation (front p m permutation row (Radix.finish p (Counter.DivMod.residue p value)))
      (value / p : ℕ) 0) at forward
  rw [front_finish] at forward
  change StateTransition.Reaches (step (table p m permutation))
    (point p m permutation (back p m permutation (permutation (Counter.DivMod.residue p value) row)
      (Radix.finish p (Counter.DivMod.residue p value))) (value / p : ℕ) 0)
    (point p m permutation (outputPort p m permutation (permutation (Counter.DivMod.residue p value) row))
      (p * (value / p) + (Counter.DivMod.residue p value).val : ℕ) 0) at backward
  have restore : p * (value / p) + (Counter.DivMod.residue p value).val = value := by
    simpa only [Counter.DivMod.residue, Nat.add_comm] using Nat.mod_add_div value p
  rw [restore] at backward
  exact forward.trans backward

theorem halt_output (permutation : Fin p → Equiv.Perm (Fin m)) (row : Fin m)
    (values : Fin 2 → ℤ) : step (table p m permutation) (outputPort p m permutation row, values) = none := by
  rw [step_none_iff]
  rintro ⟨index, enabled⟩
  exact no_outgoing_output p m permutation row ⟨index, enabled.1⟩

/-- Complete execution changes finite control and restores the full two-counter memory. -/
theorem eval_result (permutation : Fin p → Equiv.Perm (Fin m)) (row : Fin m) (value : ℕ) :
    eval (table p m permutation) (point p m permutation (inputPort p m permutation row) value 0) =
      Part.some (point p m permutation
        (outputPort p m permutation (permutation (Counter.DivMod.residue p value) row)) value 0) := by
  apply Part.eq_some_iff.mpr
  exact StateTransition.mem_eval.mpr
    ⟨reaches_result p m permutation row value, halt_output p m permutation _ _⟩

/-- The existing five-gate compiler realizes the same port network on three persistent roots. -/
theorem native_eval [NeZero m] (permutation : Fin p → Equiv.Perm (Fin m))
    (row : Fin m) (value : ℕ) :
    (ReversibleCompilation.haltingProgram (table p m permutation)
      (deterministic p m permutation) (targetCompatible p m permutation)).eval
      (ReversibleCompilation.iota (e := edges p m)
        (point p m permutation (inputPort p m permutation row) value 0)) =
      Part.some (ReversibleCompilation.iota (e := edges p m)
        (point p m permutation
          (outputPort p m permutation (permutation (Counter.DivMod.residue p value) row)) value 0)) := by
  apply ReversibleCompilation.eval_of_reaches
  · exact reaches_result p m permutation row value
  · exact no_outgoing_output p m permutation _

end Monodromy.Counter.Reversible.RadixObservation

end


/-!
## A source specification for reversible transition recording
-/

namespace Monodromy.Counter.Recorded

variable {n m : ℕ}

/-- One nonzero radix digit records a finite transition tag. -/
def push {k : ℕ} (symbol : Fin k) (history : ℕ) : ℕ :=
  (k + 1) * history + symbol.val + 1

theorem push_remainder {k : ℕ} (symbol : Fin k) (history : ℕ) :
    push symbol history % (k + 1) = symbol.val + 1 := by
  have bound : symbol.val + 1 < k + 1 := by omega
  simp only [push, Nat.add_assoc, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt bound]

theorem push_quotient {k : ℕ} (symbol : Fin k) (history : ℕ) :
    push symbol history / (k + 1) = history := by
  have bound : symbol.val + 1 < k + 1 := by omega
  rw [push, Nat.add_assoc, Nat.mul_add_div (Nat.succ_pos k), Nat.div_eq_of_lt bound, add_zero]

theorem push_injective {k : ℕ} :
    Function.Injective (fun pair : Fin k × ℕ => push pair.1 pair.2) := by
  rintro ⟨first, left⟩ ⟨second, right⟩ same
  have digits := congrArg (fun value => value % (k + 1)) same
  rw [push_remainder, push_remainder] at digits
  have histories := congrArg (fun value => value / (k + 1)) same
  rw [push_quotient, push_quotient] at histories
  exact Prod.ext (Fin.ext (by omega)) histories

/-- The tag retains the old address and the zero/nonzero branch of a decrement. -/
def branch (program : Program n m) (state : Configuration n m) : Fin 2 :=
  match program state.pc with
  | .dec register _ _ => if state.counters register = 0 then 0 else 1
  | _ => 0

def tag (program : Program n m) (state : Configuration n m) : Fin (m * 2) :=
  finProdFinEquiv (state.pc, branch program state)

/-- Reconstruction is a proof-side decoder of a recorded source tag. -/
def restore (program : Program n m) (symbol : Fin (m * 2))
    (after : Configuration n m) : Configuration n m :=
  let old := finProdFinEquiv.symm symbol
  let values := match program old.1 with
    | .inc register _ => Function.update after.counters register (after.counters register - 1)
    | .dec register _ _ =>
        if old.2 = 0 then after.counters
        else Function.update after.counters register (after.counters register + 1)
    | .halt => after.counters
  ⟨old.1, values⟩

theorem restore_step (program : Program n m) {before after : Configuration n m}
    (transition : Counter.step program before = some after) :
    restore program (tag program before) after = before := by
  cases instruction : program before.pc with
  | halt => simp [Counter.step, instruction] at transition
  | inc register next =>
      have result := Option.some.inj ((Counter.step_inc program before instruction).symm.trans transition)
      subst after
      unfold restore tag
      rw [Equiv.symm_apply_apply]
      simp only [instruction]
      apply congrArg (Configuration.mk before.pc)
      funext index
      by_cases same : index = register
      · subst index
        simp
      · simp [Function.update_of_ne same]
  | dec register zero nonzero =>
      cases count : before.counters register with
      | zero =>
          have result := Option.some.inj ((Counter.step_dec_zero program before instruction count).symm.trans transition)
          subst after
          simp [restore, tag, branch, instruction, count]
      | succ value =>
          have result := Option.some.inj ((Counter.step_dec_succ program before instruction count).symm.trans transition)
          subst after
          unfold restore tag
          rw [Equiv.symm_apply_apply]
          simp only [instruction, branch, count, Nat.add_eq_zero_iff, Nat.one_ne_zero,
            and_false, ite_false]
          apply congrArg (Configuration.mk before.pc)
          funext index
          by_cases same : index = register
          · subst index
            simpa using count.symm
          · simp [Function.update_of_ne same]

abbrev State (n m : ℕ) := Configuration n m × ℕ

/-- An integer history code is appended to the source specification, not to native state. -/
def step (program : Program n m) (state : State n m) : Option (State n m) :=
  (Counter.step program state.1).map fun next => (next, push (tag program state.1) state.2)

theorem step_defined_injective (program : Program n m) {first second last : State n m}
    (left : step program first = some last) (right : step program second = some last) :
    first = second := by
  obtain ⟨left_next, left_step, left_result⟩ := Option.map_eq_some_iff.mp left
  obtain ⟨right_next, right_step, right_result⟩ := Option.map_eq_some_iff.mp right
  have same := left_result.trans right_result.symm
  have next_same : left_next = right_next := congrArg (fun pair : State n m => pair.1) same
  have records := @push_injective (m * 2) (tag program first.1, first.2)
    (tag program second.1, second.2) (congrArg Prod.snd same)
  have tags : tag program first.1 = tag program second.1 := congrArg Prod.fst records
  have histories : first.2 = second.2 :=
    congrArg (fun pair : Fin (m * 2) × ℕ => pair.2) records
  apply Prod.ext
  · calc
      first.1 = restore program (tag program first.1) left_next := (restore_step program left_step).symm
      _ = restore program (tag program second.1) right_next := by rw [tags, next_same]
      _ = second.1 := restore_step program right_step
  · exact histories

theorem history_lt (program : Program n m) {first last : State n m}
    (transition : step program first = some last) : first.2 < last.2 := by
  obtain ⟨next, _, result⟩ := Option.map_eq_some_iff.mp transition
  rw [← result]
  change first.2 < push (tag program first.1) first.2
  rw [push, Nat.add_mul, Nat.one_mul]
  omega

/-- Every positive finite source run leaves a strictly longer recoverable history. -/
theorem history_lt_of_reaches (program : Program n m) {first last : State n m}
    (run : StateTransition.Reaches₁ (step program) first last) : first.2 < last.2 := by
  induction run with
  | single transition => exact history_lt program transition
  | tail _ transition previous => exact previous.trans (history_lt program transition)

/-- Recording a tag preserves source results, termination, and divergence after projection. -/
theorem eval_projection (program : Program n m) (state : State n m) :
    Counter.eval program state.1 =
      Prod.fst <$> StateTransition.eval (step program) state := by
  apply StateTransition.tr_eval' (step program) (Counter.step program) Prod.fst
  apply StateTransition.fun_respects.mpr
  intro original
  cases transition : Counter.step program original.1 with
  | none =>
      simp only [step, transition, Option.map_none, StateTransition.FRespects]
  | some next =>
      simp only [step, transition, Option.map_some]
      exact Relation.TransGen.single transition

end Monodromy.Counter.Recorded


/-!
## Recoverable execution histories

Finite copies of the reversed radix graph record each instruction branch.
The source registers are protected while the history is packed; the workspace
returns to zero at every dispatch. This is an intermediate reversible source
graph, prior to compression into the two native memory coordinates.
-/

noncomputable section

namespace Monodromy.Counter.Reversible.Recording

variable {n m : ℕ}

def base (m : ℕ) : ℕ := m * 2 + 1

instance base_nonzero (m : ℕ) : NeZero (base m) := ⟨by simp [base]⟩

abbrev Node (m : ℕ) := (Fin m × Fin (Radix.size (base m))) ⊕ Fin m

def size (m : ℕ) : ℕ := m * Radix.size (base m) + m

def nodeEquiv (m : ℕ) : Node m ≃ Fin (size m) :=
  (Equiv.sumCongr finProdFinEquiv (Equiv.refl _)).trans finSumFinEquiv

def copy (row : Fin m) (position : Fin (Radix.size (base m))) : Fin (size m) :=
  nodeEquiv m (.inl (row, position))

def mid (row : Fin m) : Fin (size m) := nodeEquiv m (.inr row)

def dispatch (row : Fin m) : Fin (size m) := copy row (Radix.entry (base m))

def port (row : Fin m) (symbol : Fin (base m)) : Fin (size m) :=
  copy row (Radix.finish (base m) symbol)

/-- The nonzero digit retains the old address and decrement branch. -/
def digit (row : Fin m) (branch : Fin 2) : Fin (base m) :=
  ⟨(finProdFinEquiv (row, branch)).val + 1, by
    have bound := (finProdFinEquiv (row, branch)).isLt
    simp only [base]
    omega⟩

@[simp] theorem digit_eq_iff (row other : Fin m) (branch next : Fin 2) :
    digit row branch = digit other next ↔ row = other ∧ branch = next := by
  constructor
  · intro same
    have values := congrArg Fin.val same
    have tags : finProdFinEquiv (row, branch) = finProdFinEquiv (other, next) := by
      apply Fin.ext
      simp only [digit] at values
      omega
    exact Prod.mk.inj ((finProdFinEquiv).injective tags)
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Precisely the active finite external arcs; halt rows contribute none. -/
def Active (program : Counter.Program n m) (pair : Fin m × Fin 3) : Prop :=
  match program pair.1 with
  | .inc _ _ => pair.2 = 0
  | .dec _ _ _ => True
  | .halt => False

instance active_decidable (program : Counter.Program n m) (pair : Fin m × Fin 3) :
    Decidable (Active program pair) := by
  unfold Active
  cases program pair.1 <;> infer_instance

abbrev Extra (program : Counter.Program n m) := {pair : Fin m × Fin 3 // Active program pair}

def historyRegister (n : ℕ) : Fin 2 → Fin (n + 2) := Fin.natAdd n

theorem historyRegister_injective (n : ℕ) : Function.Injective (historyRegister n) := by
  intro first second same
  apply Fin.ext
  have values := congrArg Fin.val same
  simp only [historyRegister, Fin.val_natAdd] at values
  omega

def packing (n m : ℕ) : Table (n + 2) (Radix.size (base m)) (Radix.edges (base m)) :=
  RegisterRelocation.mapTable (historyRegister n) (reverseTable (Radix.table (base m)))

theorem packing_deterministic (n m : ℕ) : Deterministic (packing n m) :=
  RegisterRelocation.deterministic _ (historyRegister_injective n) _
    (reverseTable_deterministic _ (Radix.targetCompatible (base m)))

theorem packing_targetCompatible (n m : ℕ) : TargetCompatible (packing n m) :=
  RegisterRelocation.targetCompatible _ (historyRegister_injective n) _
    (reverseTable_targetCompatible _ (Radix.deterministic (base m)))

theorem packing_no_outgoing_dispatch (index : Fin (Radix.edges (base m))) :
    (packing n m index).source ≠ Radix.entry (base m) :=
  Radix.no_incoming_entry (base m) index

theorem packing_no_incoming_port (symbol : Fin (base m))
    (index : Fin (Radix.edges (base m))) :
    (packing n m index).target ≠ Radix.finish (base m) symbol :=
  fun incoming => Radix.no_outgoing_finish (base m) symbol ⟨index, incoming⟩

def extraOrigin (program : Counter.Program n m) (arc : Extra program) : Node m :=
  match instruction : program arc.val.1 with
  | .inc _ _ => .inl (arc.val.1, Radix.entry (base m))
  | .dec _ _ _ => if arc.val.2 = 2 then .inr arc.val.1
      else .inl (arc.val.1, Radix.entry (base m))
  | .halt => False.elim (by simpa [Active, instruction] using arc.property)

def extraDestination (program : Counter.Program n m) (arc : Extra program) : Node m :=
  match instruction : program arc.val.1 with
  | .inc _ target => .inl (target, Radix.finish (base m) (digit arc.val.1 0))
  | .dec _ zero nonzero => ![
      Sum.inl (zero, Radix.finish (base m) (digit arc.val.1 0)),
      Sum.inr arc.val.1,
      Sum.inl (nonzero, Radix.finish (base m) (digit arc.val.1 1))] arc.val.2
  | .halt => False.elim (by simpa [Active, instruction] using arc.property)

def extraOperation (program : Counter.Program n m) (arc : Extra program) : Action (n + 2) :=
  match instruction : program arc.val.1 with
  | .inc register _ => .shift (Fin.castAdd 2 register) 1
  | .dec register _ _ => ![
      Action.test (Fin.castAdd 2 register) true,
      Action.test (Fin.castAdd 2 register) false,
      Action.shift (Fin.castAdd 2 register) (-1)] arc.val.2
  | .halt => False.elim (by simpa [Active, instruction] using arc.property)

def extraEdge (program : Counter.Program n m) (arc : Extra program) : Edge (n + 2) (size m) :=
  ⟨nodeEquiv m (extraOrigin program arc), nodeEquiv m (extraDestination program arc),
    extraOperation program arc⟩

abbrev Arc (program : Counter.Program n m) :=
  (Fin m × Fin (Radix.edges (base m))) ⊕ Extra program

def edges (program : Counter.Program n m) : ℕ :=
  m * Radix.edges (base m) + Fintype.card (Extra program)

def arcEquiv (program : Counter.Program n m) : Arc program ≃ Fin (edges program) :=
  (Equiv.sumCongr finProdFinEquiv (Fintype.equivFin (Extra program))).trans finSumFinEquiv

def arcEdge (program : Counter.Program n m) : Arc program → Edge (n + 2) (size m)
  | .inl (row, edge) => Glue.mapEdge (copy row) (packing n m edge)
  | .inr edge => extraEdge program edge

def table (program : Counter.Program n m) : Table (n + 2) (size m) (edges program) :=
  fun index => arcEdge program ((arcEquiv program).symm index)

@[simp] theorem table_arc (program : Counter.Program n m) (arc : Arc program) :
    table program (arcEquiv program arc) = arcEdge program arc := by
  simp [table]

/-- Every copy preserves its own finite radix address and original-row label. -/
@[simp] theorem copy_eq_iff (row other : Fin m)
    (first second : Fin (Radix.size (base m))) :
    copy row first = copy other second ↔ row = other ∧ first = second := by
  unfold copy
  rw [(nodeEquiv m).injective.eq_iff]
  simp

@[simp] theorem copy_ne_mid (row other : Fin m) (position : Fin (Radix.size (base m))) :
    copy row position ≠ mid other := by
  intro same
  have impossible : (Sum.inl (row, position) : Node m) = Sum.inr other :=
    (nodeEquiv m).injective same
  cases impossible

@[simp] theorem mid_eq_iff (row other : Fin m) : mid row = mid other ↔ row = other := by
  unfold mid
  rw [(nodeEquiv m).injective.eq_iff]
  simp

@[simp] theorem finish_eq_iff (first second : Fin (base m)) :
    Radix.finish (base m) first = Radix.finish (base m) second ↔ first = second := by
  unfold Radix.finish Radix.block
  rw [(Radix.nodeEquiv (base m)).injective.eq_iff]
  simp


theorem extraOrigin_inc (program : Counter.Program n m) (arc : Extra program)
    (register : Fin n) (target : Fin m) (instruction : program arc.val.1 = .inc register target) :
    extraOrigin program arc = Sum.inl (arc.val.1, Radix.entry (base m)) := by
  unfold extraOrigin
  split <;> simp_all

theorem extraOrigin_dec (program : Counter.Program n m) (arc : Extra program)
    (register : Fin n) (zero nonzero : Fin m)
    (instruction : program arc.val.1 = .dec register zero nonzero) :
    extraOrigin program arc = if arc.val.2 = 2 then Sum.inr arc.val.1
      else Sum.inl (arc.val.1, Radix.entry (base m)) := by
  unfold extraOrigin
  split <;> simp_all

theorem extraDestination_inc (program : Counter.Program n m) (arc : Extra program)
    (register : Fin n) (target : Fin m) (instruction : program arc.val.1 = .inc register target) :
    extraDestination program arc =
      Sum.inl (target, Radix.finish (base m) (digit arc.val.1 0)) := by
  unfold extraDestination
  split <;> simp_all

theorem extraDestination_dec (program : Counter.Program n m) (arc : Extra program)
    (register : Fin n) (zero nonzero : Fin m)
    (instruction : program arc.val.1 = .dec register zero nonzero) :
    extraDestination program arc = ![
      Sum.inl (zero, Radix.finish (base m) (digit arc.val.1 0)),
      Sum.inr arc.val.1,
      Sum.inl (nonzero, Radix.finish (base m) (digit arc.val.1 1))] arc.val.2 := by
  unfold extraDestination
  split <;> simp_all

theorem extraOperation_inc (program : Counter.Program n m) (arc : Extra program)
    (register : Fin n) (target : Fin m) (instruction : program arc.val.1 = .inc register target) :
    extraOperation program arc = .shift (Fin.castAdd 2 register) 1 := by
  unfold extraOperation
  split <;> simp_all

theorem extraOperation_dec (program : Counter.Program n m) (arc : Extra program)
    (register : Fin n) (zero nonzero : Fin m)
    (instruction : program arc.val.1 = .dec register zero nonzero) :
    extraOperation program arc = ![
      Action.test (Fin.castAdd 2 register) true,
      Action.test (Fin.castAdd 2 register) false,
      Action.shift (Fin.castAdd 2 register) (-1)] arc.val.2 := by
  unfold extraOperation
  split <;> simp_all

private theorem extraOrigin_row (program : Counter.Program n m) (arc : Extra program) :
    (extraOrigin program arc).elim Prod.fst id = arc.val.1 := by
  cases instruction : program arc.val.1 with
  | inc register target =>
      rw [extraOrigin_inc program arc register target instruction]
      rfl
  | dec register zero nonzero =>
      rw [extraOrigin_dec program arc register zero nonzero instruction]
      split_ifs <;> rfl
  | halt =>
      have active := arc.property
      unfold Active at active
      rw [instruction] at active
      exact active.elim

/-- The only external dispatch alternatives are complementary tests on the same old register. -/
theorem extra_deterministic (program : Counter.Program n m) (first second : Extra program)
    (different : first ≠ second) (same : extraOrigin program first = extraOrigin program second) :
    Action.Compatible (extraOperation program first) (extraOperation program second) := by
  have rows : first.val.1 = second.val.1 := by
    have owners := congrArg (fun node : Node m => node.elim Prod.fst id) same
    simpa only [extraOrigin_row] using owners
  rcases first with ⟨⟨row, branch⟩, first_active⟩
  rcases second with ⟨⟨other, next⟩, second_active⟩
  change row = other at rows
  subst other
  cases instruction : program row with
  | inc register target =>
      have first_zero : branch = 0 := by
        have active := first_active
        unfold Active at active
        rw [instruction] at active
        exact active
      have second_zero : next = 0 := by
        have active := second_active
        unfold Active at active
        rw [instruction] at active
        exact active
      subst branch
      subst next
      exact False.elim (different (Subtype.ext rfl))
  | dec register zero nonzero =>
      rw [extraOrigin_dec program ⟨(row, branch), first_active⟩ register zero nonzero instruction,
        extraOrigin_dec program ⟨(row, next), second_active⟩ register zero nonzero instruction] at same
      rw [extraOperation_dec program ⟨(row, branch), first_active⟩ register zero nonzero instruction,
        extraOperation_dec program ⟨(row, next), second_active⟩ register zero nonzero instruction]
      fin_cases branch <;> fin_cases next <;> simp_all [Action.Compatible]
  | halt =>
      have active := first_active
      unfold Active at active
      rw [instruction] at active
      exact active.elim

/-- A nonzero history digit makes every external destination distinct. -/
theorem extraDestination_injective (program : Counter.Program n m) :
    Function.Injective (extraDestination program) := by
  intro first second same
  rcases first with ⟨⟨row, branch⟩, first_active⟩
  rcases second with ⟨⟨other, next⟩, second_active⟩
  apply Subtype.ext
  cases first_instruction : program row <;> cases second_instruction : program other
  all_goals
    have first_valid := first_active
    have second_valid := second_active
    unfold Active at first_valid second_valid
    rw [first_instruction] at first_valid
    rw [second_instruction] at second_valid
  all_goals try contradiction
  all_goals first
    | rw [extraDestination_inc program ⟨(row, branch), first_active⟩ _ _ first_instruction] at same
    | rw [extraDestination_dec program ⟨(row, branch), first_active⟩ _ _ _ first_instruction] at same
  all_goals first
    | rw [extraDestination_inc program ⟨(other, next), second_active⟩ _ _ second_instruction] at same
    | rw [extraDestination_dec program ⟨(other, next), second_active⟩ _ _ _ second_instruction] at same
  all_goals fin_cases branch <;> fin_cases next <;> simp_all

private theorem extraOrigin_shape (program : Counter.Program n m) (arc : Extra program) :
    extraOrigin program arc = Sum.inl (arc.val.1, Radix.entry (base m)) ∨
      extraOrigin program arc = Sum.inr arc.val.1 := by
  cases instruction : program arc.val.1 with
  | inc register target => exact Or.inl (extraOrigin_inc program arc register target instruction)
  | dec register zero nonzero =>
      rw [extraOrigin_dec program arc register zero nonzero instruction]
      by_cases last : arc.val.2 = 2 <;> simp [last]
  | halt =>
      have active := arc.property
      unfold Active at active
      rw [instruction] at active
      exact active.elim

private theorem extraDestination_shape (program : Counter.Program n m) (arc : Extra program) :
    (∃ target symbol, extraDestination program arc =
      Sum.inl (target, Radix.finish (base m) symbol)) ∨
      extraDestination program arc = Sum.inr arc.val.1 := by
  rcases arc with ⟨⟨row, branch⟩, active⟩
  cases instruction : program row with
  | inc register target =>
      exact Or.inl ⟨target, digit row 0, extraDestination_inc program _ register target instruction⟩
  | dec register zero nonzero =>
      rw [extraDestination_dec program _ register zero nonzero instruction]
      fin_cases branch
      · exact Or.inl ⟨zero, digit row 0, rfl⟩
      · exact Or.inr rfl
      · exact Or.inl ⟨nonzero, digit row 1, rfl⟩
  | halt =>
      have impossible := active
      unfold Active at impossible
      rw [instruction] at impossible
      exact impossible.elim

private theorem packing_extra_source_ne (program : Counter.Program n m) (row : Fin m)
    (index : Fin (Radix.edges (base m))) (arc : Extra program) :
    copy row (packing n m index).source ≠ nodeEquiv m (extraOrigin program arc) := by
  intro same
  have raw : Sum.inl (row, (packing n m index).source) = extraOrigin program arc :=
    (nodeEquiv m).injective same
  rcases extraOrigin_shape program arc with dispatch_case | mid_case
  · rw [dispatch_case] at raw
    exact packing_no_outgoing_dispatch (n := n) index (Prod.mk.inj (Sum.inl.inj raw)).2
  · rw [mid_case] at raw
    cases raw

private theorem packing_extra_target_ne (program : Counter.Program n m) (row : Fin m)
    (index : Fin (Radix.edges (base m))) (arc : Extra program) :
    copy row (packing n m index).target ≠ nodeEquiv m (extraDestination program arc) := by
  intro same
  have raw : Sum.inl (row, (packing n m index).target) = extraDestination program arc :=
    (nodeEquiv m).injective same
  rcases extraDestination_shape program arc with ⟨target, symbol, port_case⟩ | mid_case
  · rw [port_case] at raw
    exact packing_no_incoming_port (n := n) symbol index (Prod.mk.inj (Sum.inl.inj raw)).2
  · rw [mid_case] at raw
    cases raw

/-- The compiled graph chooses every enabled edge through its own finite ports. -/
theorem deterministic (program : Counter.Program n m) : Deterministic (table program) := by
  intro first second different same
  obtain ⟨first, rfl⟩ := (arcEquiv program).surjective first
  obtain ⟨second, rfl⟩ := (arcEquiv program).surjective second
  have distinct : first ≠ second := fun identical => different (congrArg (arcEquiv program) identical)
  clear different
  simp only [table_arc] at same ⊢
  rcases first with ⟨row, index⟩ | first <;> rcases second with ⟨other, next⟩ | second
  all_goals simp only [arcEdge, Glue.mapEdge, extraEdge] at same ⊢
  · rcases (copy_eq_iff row other _ _).mp same with ⟨same_rows, same_source⟩
    subst other
    exact packing_deterministic n m index next
      (fun identical => distinct (congrArg Sum.inl (Prod.ext rfl identical))) same_source
  · exact False.elim (packing_extra_source_ne program row index second same)
  · exact False.elim (packing_extra_source_ne program other next first same.symm)
  · exact extra_deterministic program first second
      (fun identical => distinct (congrArg Sum.inr identical)) ((nodeEquiv m).injective same)

/-- A unique recoverable history tag separates every external predecessor. -/
theorem targetCompatible (program : Counter.Program n m) : TargetCompatible (table program) := by
  intro first second different same
  obtain ⟨first, rfl⟩ := (arcEquiv program).surjective first
  obtain ⟨second, rfl⟩ := (arcEquiv program).surjective second
  have distinct : first ≠ second := fun identical => different (congrArg (arcEquiv program) identical)
  clear different
  simp only [table_arc] at same ⊢
  rcases first with ⟨row, index⟩ | first <;> rcases second with ⟨other, next⟩ | second
  all_goals simp only [arcEdge, Glue.mapEdge, extraEdge] at same ⊢
  · rcases (copy_eq_iff row other _ _).mp same with ⟨same_rows, same_target⟩
    subst other
    exact packing_targetCompatible n m index next
      (fun identical => distinct (congrArg Sum.inl (Prod.ext rfl identical))) same_target
  · exact False.elim (packing_extra_target_ne program row index second same)
  · exact False.elim (packing_extra_target_ne program other next first same.symm)
  · exact False.elim (distinct (congrArg Sum.inr
      (extraDestination_injective program ((nodeEquiv m).injective same))))


def frame (values : Fin n → ℕ) (history workspace : ℤ) : Fin (n + 2) → ℤ :=
  Fin.addCases (fun index => (values index : ℤ)) ![history, workspace]

def framed (control : Fin (size m)) (values : Fin n → ℕ) (history workspace : ℤ) :
    State (n + 2) (size m) := (control, frame values history workspace)

def encode (state : Counter.Configuration n m) (history : ℕ) : State (n + 2) (size m) :=
  framed (dispatch state.pc) state.counters history 0

@[simp] theorem frame_old (values : Fin n → ℕ) (history workspace : ℤ) (index : Fin n) :
    frame values history workspace (Fin.castAdd 2 index) = (values index : ℤ) := by
  simp [frame]

@[simp] theorem frame_tail (values : Fin n → ℕ) (history workspace : ℤ) (index : Fin 2) :
    frame values history workspace (historyRegister n index) = ![history, workspace] index := by
  simp [frame, historyRegister]

@[simp] theorem frame_history (values : Fin n → ℕ) (history workspace : ℤ) :
    frame values history workspace (historyRegister n 0) = history := by simp

@[simp] theorem frame_workspace (values : Fin n → ℕ) (history workspace : ℤ) :
    frame values history workspace (historyRegister n 1) = workspace := by simp

private theorem tail_ne_old (index : Fin 2) (old : Fin n) :
    historyRegister n index ≠ Fin.castAdd 2 old := by
  intro same
  have values := congrArg Fin.val same
  simp only [historyRegister, Fin.val_natAdd, Fin.val_castAdd] at values
  omega

theorem frame_extend (values : Fin n → ℕ) (history workspace : ℤ) :
    Function.extend (historyRegister n) ![history, workspace] (frame values 0 0) =
      frame values history workspace := by
  funext index
  induction index using Fin.addCases with
  | left old =>
      rw [Function.extend_apply' _ _ _ (by rintro ⟨tail, same⟩; exact tail_ne_old tail old same)]
      simp
  | right tail =>
      change Function.extend (historyRegister n) ![history, workspace] (frame values 0 0)
        (historyRegister n tail) = frame values history workspace (historyRegister n tail)
      rw [(historyRegister_injective n).extend_apply]
      exact (frame_tail values history workspace tail).symm

theorem framed_embed (control : Fin (size m)) (values : Fin n → ℕ) (history workspace : ℤ) :
    RegisterRelocation.embed (historyRegister n) (frame values 0 0)
      (control, ![history, workspace]) = framed control values history workspace := by
  simp only [RegisterRelocation.embed, framed, frame_extend]

theorem frame_update (values : Fin n → ℕ) (history workspace : ℤ) (index : Fin n) (value : ℕ) :
    Function.update (frame values history workspace) (Fin.castAdd 2 index) (value : ℤ) =
      frame (Function.update values index value) history workspace := by
  funext position
  induction position using Fin.addCases with
  | left old =>
      by_cases same : old = index
      · subst old; simp
      · simp [same]
  | right tail =>
      change Function.update (frame values history workspace) (Fin.castAdd 2 index) (value : ℤ)
        (historyRegister n tail) =
          frame (Function.update values index value) history workspace (historyRegister n tail)
      rw [Function.update_of_ne (tail_ne_old tail index)]
      simp only [frame_tail]

theorem shift_frame (values : Fin n → ℕ) (history workspace amount : ℤ) (index : Fin n)
    (value : ℕ) (updated : (values index : ℤ) + amount = value) :
    Action.apply (.shift (Fin.castAdd 2 index) amount) (frame values history workspace) =
      frame (Function.update values index value) history workspace := by
  simpa only [Action.apply, frame_old, updated] using frame_update values history workspace index value

theorem inc_frame (values : Fin n → ℕ) (history workspace : ℤ) (index : Fin n) :
    Action.apply (.shift (Fin.castAdd 2 index) 1) (frame values history workspace) =
      frame (Function.update values index (values index + 1)) history workspace :=
  shift_frame values history workspace 1 index _ (by simp)

theorem dec_frame (values : Fin n → ℕ) (history workspace : ℤ) (index : Fin n) (value : ℕ)
    (positive : values index = value + 1) :
    Action.apply (.shift (Fin.castAdd 2 index) (-1)) (frame values history workspace) =
      frame (Function.update values index value) history workspace :=
  shift_frame values history workspace (-1) index _ (by simp [positive])


def embed (recorded : Counter.Recorded.State n m) : State (n + 2) (size m) :=
  encode recorded.1 recorded.2

theorem embed_injective : Function.Injective (@embed n m) := by
  rintro ⟨⟨first_pc, first_values⟩, first_history⟩
    ⟨⟨second_pc, second_values⟩, second_history⟩ same
  change framed (dispatch first_pc) first_values first_history 0 =
    framed (dispatch second_pc) second_values second_history 0 at same
  apply Prod.ext
  · apply congrArg₂ Counter.Configuration.mk
    · have controls := congrArg (fun state : State (n + 2) (size m) => state.1) same
      exact ((copy_eq_iff first_pc second_pc _ _).mp controls).1
    · funext index
      have values := congrArg
        (fun state : State (n + 2) (size m) => state.2 (Fin.castAdd 2 index)) same
      exact Int.natCast_inj.mp (by simpa only [framed, frame_old] using values)
  · have histories := congrArg
      (fun state : State (n + 2) (size m) => state.2 (historyRegister n 0)) same
    exact Int.natCast_inj.mp (by simpa only [framed, frame_history] using histories)

theorem halt_no_outgoing (program : Counter.Program n m) (row : Fin m)
    (halted : program row = .halt) (index : Fin (edges program)) :
    (table program index).source ≠ dispatch row := by
  obtain ⟨arc, rfl⟩ := (arcEquiv program).surjective index
  rw [table_arc]
  rcases arc with ⟨other, edge⟩ | arc
  · change copy other (packing n m edge).source ≠ copy row (Radix.entry (base m))
    exact fun same => packing_no_outgoing_dispatch edge ((copy_eq_iff other row _ _).mp same).2
  · intro same
    have raw : extraOrigin program arc = Sum.inl (row, Radix.entry (base m)) :=
      (nodeEquiv m).injective same
    rcases arc with ⟨⟨other, branch⟩, active⟩
    cases instruction : program other with
    | inc register target =>
        rw [extraOrigin_inc program ⟨(other, branch), active⟩ register target instruction] at raw
        have rows := (Prod.mk.inj (Sum.inl.inj raw)).1
        have impossible := instruction.symm.trans ((congrArg program rows).trans halted)
        cases impossible
    | dec register zero nonzero =>
        rw [extraOrigin_dec program ⟨(other, branch), active⟩ register zero nonzero instruction] at raw
        split at raw
        · cases raw
        · have rows := (Prod.mk.inj (Sum.inl.inj raw)).1
          have impossible := instruction.symm.trans ((congrArg program rows).trans halted)
          cases impossible
    | halt =>
        unfold Active at active
        rw [instruction] at active
        exact active.elim

theorem step_encode_none_iff (program : Counter.Program n m)
    (state : Counter.Configuration n m) (history : ℕ) :
    step (table program) (encode state history) = none ↔ Counter.step program state = none := by
  rw [step_none_iff]
  cases instruction : program state.pc with
  | halt =>
      constructor
      · intro _; exact Counter.step_halt program state instruction
      · intro _
        rintro ⟨index, enabled⟩
        exact halt_no_outgoing program state.pc instruction index enabled.1
  | inc register target =>
      simp only [Counter.step, instruction, reduceCtorEq, iff_false, not_not]
      let arc : Extra program := ⟨(state.pc, 0), by simp [Active, instruction]⟩
      refine ⟨arcEquiv program (.inr arc), ?_⟩
      rw [table_arc]
      change (extraEdge program arc).enabled (encode state history)
      simp only [extraEdge, Edge.enabled, encode, framed]
      rw [extraOrigin_inc program arc register target instruction,
        extraOperation_inc program arc register target instruction]
      exact ⟨rfl, trivial⟩
  | dec register zero nonzero =>
      have live : Counter.step program state ≠ none := by
        cases count : state.counters register <;> simp [Counter.step, instruction, count]
      simp only [live, iff_false, not_not]
      by_cases empty : state.counters register = 0
      · let arc : Extra program := ⟨(state.pc, 0), by simp [Active, instruction]⟩
        refine ⟨arcEquiv program (.inr arc), ?_⟩
        rw [table_arc]
        change (extraEdge program arc).enabled (encode state history)
        simp only [extraEdge, Edge.enabled, encode, framed]
        rw [extraOrigin_dec program arc register zero nonzero instruction,
          extraOperation_dec program arc register zero nonzero instruction]
        exact ⟨rfl, by simp [Action.enabled, arc, empty]⟩
      · let arc : Extra program := ⟨(state.pc, 1), by simp [Active, instruction]⟩
        refine ⟨arcEquiv program (.inr arc), ?_⟩
        rw [table_arc]
        change (extraEdge program arc).enabled (encode state history)
        simp only [extraEdge, Edge.enabled, encode, framed]
        rw [extraOrigin_dec program arc register zero nonzero instruction,
          extraOperation_dec program arc register zero nonzero instruction]
        exact ⟨rfl, by simp [Action.enabled, arc, empty]⟩


theorem extraEdge_inc (program : Counter.Program n m) (arc : Extra program)
    (register : Fin n) (target : Fin m) (instruction : program arc.val.1 = .inc register target) :
    extraEdge program arc =
      ⟨dispatch arc.val.1, port target (digit arc.val.1 0), .shift (Fin.castAdd 2 register) 1⟩ := by
  unfold extraEdge
  rw [extraOrigin_inc program arc register target instruction,
    extraDestination_inc program arc register target instruction,
    extraOperation_inc program arc register target instruction]
  rfl

theorem extraEdge_dec (program : Counter.Program n m) (arc : Extra program)
    (register : Fin n) (zero nonzero : Fin m)
    (instruction : program arc.val.1 = .dec register zero nonzero) :
    extraEdge program arc = ![
      ⟨dispatch arc.val.1, port zero (digit arc.val.1 0), .test (Fin.castAdd 2 register) true⟩,
      ⟨dispatch arc.val.1, mid arc.val.1, .test (Fin.castAdd 2 register) false⟩,
      ⟨mid arc.val.1, port nonzero (digit arc.val.1 1), .shift (Fin.castAdd 2 register) (-1)⟩]
      arc.val.2 := by
  unfold extraEdge
  rw [extraOrigin_dec program arc register zero nonzero instruction,
    extraDestination_dec program arc register zero nonzero instruction,
    extraOperation_dec program arc register zero nonzero instruction]
  rcases arc with ⟨⟨row, branch⟩, active⟩
  fin_cases branch <;> rfl


/-! The natural domain is preserved at every intermediate port. -/

def OldNonnegative (values : Fin (n + 2) → ℤ) : Prop :=
  ∀ index : Fin n, 0 ≤ values (Fin.castAdd 2 index)

/-- Copy ports use the existing radix invariant; the decrement middle retains its positive input. -/
def admissible (program : Counter.Program n m) : Node m → (Fin (n + 2) → ℤ) → Prop
  | .inl (_, position), values =>
      Radix.Valid (base m) (position, values ∘ historyRegister n)
  | .inr row, values =>
      0 ≤ values (historyRegister n 0) ∧ values (historyRegister n 1) = 0 ∧
      match program row with
      | .dec register _ _ => 0 < values (Fin.castAdd 2 register)
      | _ => False

def Valid (program : Counter.Program n m) (state : State (n + 2) (size m)) : Prop :=
  OldNonnegative state.2 ∧ admissible program ((nodeEquiv m).symm state.1) state.2

@[simp] theorem valid_copy_iff (program : Counter.Program n m) (row : Fin m)
    (position : Fin (Radix.size (base m))) (values : Fin (n + 2) → ℤ) :
    Valid program (copy row position, values) ↔
      OldNonnegative values ∧ Radix.Valid (base m) (position, values ∘ historyRegister n) := by
  simp only [Valid, copy, Equiv.symm_apply_apply, admissible]

@[simp] theorem valid_mid_iff (program : Counter.Program n m) (row : Fin m)
    (values : Fin (n + 2) → ℤ) :
    Valid program (mid row, values) ↔
      OldNonnegative values ∧ 0 ≤ values (historyRegister n 0) ∧
        values (historyRegister n 1) = 0 ∧
        match program row with
        | .dec register _ _ => 0 < values (Fin.castAdd 2 register)
        | _ => False := by
  simp only [Valid, mid, Equiv.symm_apply_apply, admissible]

@[simp] theorem valid_dispatch_iff (program : Counter.Program n m) (row : Fin m)
    (values : Fin (n + 2) → ℤ) :
    Valid program (dispatch row, values) ↔
      OldNonnegative values ∧ 0 ≤ values (historyRegister n 0) ∧
        values (historyRegister n 1) = 0 := by
  change Valid program (copy row (Radix.entry (base m)), values) ↔ _
  rw [valid_copy_iff]
  simp only [Radix.Valid, Radix.entry, Radix.global, Equiv.symm_apply_apply,
    Radix.admissible, Function.comp_apply, Matrix.cons_val_zero]
  constructor
  · rintro ⟨old, history, _, empty⟩
    exact ⟨old, history, empty⟩
  · rintro ⟨old, history, empty⟩
    exact ⟨old, history, by omega, empty⟩

@[simp] theorem valid_port_iff (program : Counter.Program n m) (row : Fin m)
    (symbol : Fin (base m)) (values : Fin (n + 2) → ℤ) :
    Valid program (port row symbol, values) ↔
      OldNonnegative values ∧ 0 ≤ values (historyRegister n 0) ∧
        0 ≤ values (historyRegister n 1) := by
  change Valid program (copy row (Radix.finish (base m) symbol), values) ↔ _
  rw [valid_copy_iff]
  simp [Radix.Valid, Radix.finish, Radix.block, Radix.admissible]

theorem valid_encode (program : Counter.Program n m) (state : Counter.Configuration n m)
    (history : ℕ) : Valid program (encode state history) := by
  change Valid program (dispatch state.pc, frame state.counters history 0)
  rw [valid_dispatch_iff]
  refine ⟨?_, ?_, ?_⟩
  · intro index
    simpa only [frame_old] using Int.natCast_nonneg (state.counters index)
  · simpa only [frame_history] using Int.natCast_nonneg history
  · exact frame_workspace _ _ _

/-- The invariant certifies every physical source counter, including history and workspace. -/
theorem valid_nonnegative (program : Counter.Program n m) (state : State (n + 2) (size m))
    (valid : Valid program state) (index : Fin (n + 2)) : 0 ≤ state.2 index := by
  induction index using Fin.addCases with
  | left old => exact valid.1 old
  | right tail =>
      change 0 ≤ state.2 (historyRegister n tail)
      rcases state with ⟨position, values⟩
      obtain ⟨node, rfl⟩ := (nodeEquiv m).surjective position
      rcases node with ⟨row, position⟩ | row
      · have tail_valid := ((valid_copy_iff program row position values).mp valid).2
        fin_cases tail
        · exact tail_valid.1
        · exact tail_valid.2.1
      · have tail_valid := (valid_mid_iff program row values).mp valid
        fin_cases tail
        · exact tail_valid.2.1
        · change 0 ≤ values (historyRegister n 1)
          rw [tail_valid.2.2.1]


private theorem old_nonnegative_mapped (action : Action 2) (values : Fin (n + 2) → ℤ)
    (old : OldNonnegative values) :
    OldNonnegative ((RegisterRelocation.mapAction (historyRegister n) action).apply values) := by
  intro index
  rw [RegisterRelocation.apply_outside (historyRegister n) action values (Fin.castAdd 2 index)
    (fun tail => tail_ne_old tail index)]
  exact old index

private theorem old_nonnegative_shift (register : Fin n) (amount : ℤ)
    (values : Fin (n + 2) → ℤ) (old : OldNonnegative values)
    (safe : 0 ≤ values (Fin.castAdd 2 register) + amount) :
    OldNonnegative (Action.apply (.shift (Fin.castAdd 2 register) amount) values) := by
  intro index
  by_cases selected : index = register
  · subst index
    simpa only [Action.apply, Function.update_self] using safe
  · simpa [Action.apply, selected] using old index

private theorem shift_old_tail (register : Fin n) (amount : ℤ)
    (values : Fin (n + 2) → ℤ) (tail : Fin 2) :
    Action.apply (.shift (Fin.castAdd 2 register) amount) values (historyRegister n tail) =
      values (historyRegister n tail) :=
  Function.update_of_ne (tail_ne_old tail register) _ _

private theorem valid_port_shift (program : Counter.Program n m) (row : Fin m)
    (symbol : Fin (base m)) (values : Fin (n + 2) → ℤ) (register : Fin n) (amount : ℤ)
    (old : OldNonnegative values) (safe : 0 ≤ values (Fin.castAdd 2 register) + amount)
    (history : 0 ≤ values (historyRegister n 0)) (workspace : 0 ≤ values (historyRegister n 1)) :
    Valid program (port row symbol, Action.apply (.shift (Fin.castAdd 2 register) amount) values) := by
  rw [valid_port_iff]
  exact ⟨old_nonnegative_shift register amount values old safe,
    by rw [shift_old_tail]; exact history,
    by rw [shift_old_tail]; exact workspace⟩

private theorem packing_valid_edge (program : Counter.Program n m) (row : Fin m)
    (index : Fin (Radix.edges (base m))) (values : Fin (n + 2) → ℤ)
    (valid : Valid program (copy row (packing n m index).source, values))
    (enabled : (packing n m index).action.enabled values) :
    Valid program (copy row (packing n m index).target, (packing n m index).action.apply values) := by
  rcases (valid_copy_iff program row _ values).mp valid with ⟨old, radix_valid⟩
  let original := reverseTable (Radix.table (base m)) index
  have guard : original.action.enabled (values ∘ historyRegister n) :=
    (RegisterRelocation.enabled_project (historyRegister n) original.action values).mp enabled
  have transition : step (reverseTable (Radix.table (base m)))
      (original.source, values ∘ historyRegister n) =
      some (original.target, original.action.apply (values ∘ historyRegister n)) := by
    apply (step_iff _ (reverseTable_deterministic _ (Radix.targetCompatible (base m)))).mpr
    exact ⟨index, ⟨rfl, guard⟩, rfl⟩
  have result := Radix.valid_reverse_step (base m) radix_valid transition
  rw [valid_copy_iff]
  refine ⟨old_nonnegative_mapped original.action values old, ?_⟩
  change Radix.Valid (base m)
    (original.target, (RegisterRelocation.mapAction (historyRegister n) original.action).apply values ∘
      historyRegister n)
  rw [RegisterRelocation.apply_project (historyRegister n) (historyRegister_injective n)]
  exact result

private theorem extra_valid_edge (program : Counter.Program n m) (arc : Extra program)
    (values : Fin (n + 2) → ℤ) (valid : Valid program ((extraEdge program arc).source, values))
    (enabled : (extraEdge program arc).action.enabled values) :
    Valid program ((extraEdge program arc).target, (extraEdge program arc).action.apply values) := by
  cases instruction : program arc.val.1 with
  | inc register target =>
      rw [extraEdge_inc program arc register target instruction] at valid enabled ⊢
      rcases (valid_dispatch_iff program arc.val.1 values).mp valid with ⟨old, history, empty⟩
      apply valid_port_shift program target (digit arc.val.1 0) values register 1 old
      · have nonnegative := old register
        omega
      · exact history
      · omega
  | dec register zero nonzero =>
      rw [extraEdge_dec program arc register zero nonzero instruction] at valid enabled ⊢
      rcases arc with ⟨⟨row, branch⟩, active⟩
      fin_cases branch
      · rcases (valid_dispatch_iff program row values).mp valid with ⟨old, history, empty⟩
        change Valid program (port zero (digit row 0), values)
        rw [valid_port_iff]
        exact ⟨old, history, by omega⟩
      · rcases (valid_dispatch_iff program row values).mp valid with ⟨old, history, empty⟩
        change Valid program (mid row, values)
        rw [valid_mid_iff, instruction]
        refine ⟨old, history, empty, ?_⟩
        change Action.enabled (.test (Fin.castAdd 2 register) false) values at enabled
        have not_zero : values (Fin.castAdd 2 register) ≠ 0 := by
          simpa only [Action.enabled, Bool.false_eq_true, iff_false] using enabled
        have nonnegative := old register
        omega
      · rcases (valid_mid_iff program row values).mp valid with ⟨old, history, empty, selected⟩
        have positive : 0 < values (Fin.castAdd 2 register) := by
          simpa only [instruction] using selected
        apply valid_port_shift program nonzero (digit row 1) values register (-1) old
        · omega
        · exact history
        · omega
  | halt =>
      have active := arc.property
      unfold Active at active
      rw [instruction] at active
      exact active.elim

/-- All actual recording transitions preserve the natural counter domain at intermediate ports. -/
theorem valid_step (program : Counter.Program n m) {first last : State (n + 2) (size m)}
    (valid : Valid program first) (transition : step (table program) first = some last) :
    Valid program last := by
  obtain ⟨index, enabled, rfl⟩ := (step_iff _ (deterministic program)).mp transition
  obtain ⟨arc, rfl⟩ := (arcEquiv program).surjective index
  rcases first with ⟨position, values⟩
  have position_eq : (arcEdge program arc).source = position := by
    simpa only [table_arc] using enabled.1
  subst position
  have action_enabled : (arcEdge program arc).action.enabled values := by
    simpa only [table_arc] using enabled.2
  clear enabled
  simp only [table_arc, Edge.execute]
  rcases arc with ⟨row, index⟩ | arc
  · exact packing_valid_edge program row index values valid action_enabled
  · exact extra_valid_edge program arc values valid action_enabled

theorem stable (program : Counter.Program n m) : Stable (table program) (Valid program) :=
  fun {_ _} valid transition => valid_step program valid transition

theorem valid_reaches (program : Counter.Program n m) {first last : State (n + 2) (size m)}
    (valid : Valid program first) (run : StateTransition.Reaches (step (table program)) first last) :
    Valid program last := by
  induction run with
  | refl => exact valid
  | tail _ transition previous => exact valid_step program previous transition

/-- Every intermediate state of every encoded recording run has only nonnegative counters. -/
theorem encode_reaches_nonnegative (program : Counter.Program n m)
    (initial : Counter.Configuration n m) (history : ℕ) {state : State (n + 2) (size m)}
    (run : StateTransition.Reaches (step (table program)) (encode initial history) state)
    (index : Fin (n + 2)) : 0 ≤ state.2 index :=
  valid_nonnegative program state (valid_reaches program (valid_encode program initial history) run) index

/-- A finite-control observation, independent of every counter value. -/
def Boundary (state : State (n + 2) (size m)) : Prop :=
  ∃ row : Fin m, state.1 = dispatch row

def InternalStep (program : Counter.Program n m)
    (first last : State (n + 2) (size m)) : Prop :=
  step (table program) first = some last ∧ ¬ Boundary first

abbrev InternalReaches (program : Counter.Program n m) :=
  Relation.ReflTransGen (InternalStep program)

/-- A positive run whose intermediate source states avoid all old dispatches. -/
def FirstReturn (program : Counter.Program n m)
    (first last : State (n + 2) (size m)) : Prop :=
  Boundary first ∧ Boundary last ∧
    ∃ next, step (table program) first = some next ∧ InternalReaches program next last

theorem boundary_encode (state : Counter.Configuration n m) (history : ℕ) :
    Boundary (encode state history) := ⟨state.pc, rfl⟩

theorem not_boundary_copy (row : Fin m) (position : Fin (Radix.size (base m)))
    (interior : position ≠ Radix.entry (base m)) (values : Fin (n + 2) → ℤ) :
    ¬ Boundary (copy row position, values) := by
  rintro ⟨other, same⟩
  exact interior ((copy_eq_iff row other _ _).mp same).2

theorem not_boundary_mid (row : Fin m) (values : Fin n → ℕ) (history workspace : ℤ) :
    ¬ Boundary (framed (mid row) values history workspace) := by
  rintro ⟨other, same⟩
  exact copy_ne_mid other row (Radix.entry (base m)) same.symm

private theorem local_step_not_entry {first last : State 2 (Radix.size (base m))}
    (transition : step (reverseTable (Radix.table (base m))) first = some last) :
    first.1 ≠ Radix.entry (base m) := by
  intro at_entry
  obtain ⟨index, enabled, _⟩ := (step_iff _
    (reverseTable_deterministic _ (Radix.targetCompatible (base m)))).mp transition
  exact Radix.no_incoming_entry (base m) index (enabled.1.trans at_entry)

/-- The copied packer cannot visit a dispatch before its terminal return. -/
theorem packing_internal_reaches (program : Counter.Program n m)
    (row : Fin m) (symbol : Fin (base m)) (values : Fin n → ℕ) (history : ℕ) :
    InternalReaches program
      (framed (port row symbol) values history 0)
      (framed (dispatch row) values (base m * history + symbol.val : ℕ) 0) := by
  let source := reverseTable (Radix.table (base m))
  let route : State 2 (Radix.size (base m)) → State (n + 2) (size m) :=
    fun state => Glue.mapState (copy row)
      (RegisterRelocation.embed (historyRegister n) (frame values 0 0) state)
  have mapped : Relation.ReflTransGen (InternalStep program)
      (route (Radix.point (base m) (Radix.finish (base m) symbol) history 0))
      (route (Radix.point (base m) (Radix.entry (base m))
        (base m * history + symbol.val : ℕ) 0)) := by
    apply Relation.ReflTransGen.lift route
      (fun first last transition => ?_) _ _ (Radix.reverse_pack (base m) history symbol)
    have relocated : step (packing n m)
        (RegisterRelocation.embed (historyRegister n) (frame values 0 0) first) =
        some (RegisterRelocation.embed (historyRegister n) (frame values 0 0) last) := by
      change step (RegisterRelocation.mapTable (historyRegister n) source)
        (RegisterRelocation.embed (historyRegister n) (frame values 0 0) first) = _
      rw [RegisterRelocation.step_embed (historyRegister n) (historyRegister_injective n)
        (frame values 0 0) source
        (reverseTable_deterministic _ (Radix.targetCompatible (base m))), transition, Option.map_some]
    constructor
    · exact Glue.step_map_live (packing n m) (table program) (copy row)
        (fun index => arcEquiv program (.inl (row, index)))
        (fun index => by simp only [table_arc, arcEdge])
        (packing_deterministic n m) (deterministic program) relocated
    · exact not_boundary_copy row first.1 (local_step_not_entry transition)
        (RegisterRelocation.embed (historyRegister n) (frame values 0 0) first).2
  simpa only [route, Radix.point, RegisterRelocation.embed, Glue.mapState, framed,
    frame_extend, port, dispatch] using mapped

private theorem extra_step (program : Counter.Program n m) (arc : Extra program)
    (state : State (n + 2) (size m)) (enabled : (extraEdge program arc).enabled state) :
    step (table program) state = some ((extraEdge program arc).execute state) := by
  apply (step_iff _ (deterministic program)).mpr
  refine ⟨arcEquiv program (.inr arc), ?_, ?_⟩
  · simpa only [table_arc, arcEdge] using enabled
  · rw [table_arc]
    rfl

private theorem history_digit (row : Fin m) (branch : Fin 2) (history : ℕ) :
    base m * history + (digit row branch).val =
      Counter.Recorded.push (finProdFinEquiv (row, branch)) history := by
  simp only [base, digit, Counter.Recorded.push, Nat.add_assoc]

private theorem pack_firstReturn (program : Counter.Program n m)
    {initial : State (n + 2) (size m)} {row : Fin m} {symbol : Fin (base m)}
    {values : Fin n → ℕ} {history : ℕ} (marked : Boundary initial)
    (first_step : step (table program) initial =
      some (framed (port row symbol) values history 0)) :
    FirstReturn program initial
      (framed (dispatch row) values (base m * history + symbol.val : ℕ) 0) := by
  exact ⟨marked, ⟨row, rfl⟩, framed (port row symbol) values history 0, first_step,
    packing_internal_reaches program row symbol values history⟩

private theorem inc_firstReturn (program : Counter.Program n m) (before : Counter.Configuration n m)
    (history : ℕ) (register : Fin n) (target : Fin m)
    (instruction : program before.pc = .inc register target) :
    FirstReturn program (encode before history)
      (encode ⟨target, Function.update before.counters register (before.counters register + 1)⟩
        (base m * history + (digit before.pc 0).val)) := by
  let arc : Extra program := ⟨(before.pc, 0), by
    unfold Active
    rw [instruction]⟩
  have fields := extraEdge_inc program arc register target instruction
  have enabled : (extraEdge program arc).enabled (encode before history) := by
    rw [fields]
    exact ⟨rfl, trivial⟩
  have first_step := extra_step program arc (encode before history) enabled
  rw [fields] at first_step
  simp only [Edge.execute, encode, framed, inc_frame] at first_step
  exact pack_firstReturn program (boundary_encode before history) first_step

private theorem zero_firstReturn (program : Counter.Program n m) (before : Counter.Configuration n m)
    (history : ℕ) (register : Fin n) (zero nonzero : Fin m)
    (instruction : program before.pc = .dec register zero nonzero) (empty : before.counters register = 0) :
    FirstReturn program (encode before history)
      (encode ⟨zero, before.counters⟩ (base m * history + (digit before.pc 0).val)) := by
  let arc : Extra program := ⟨(before.pc, 0), by unfold Active; rw [instruction]; trivial⟩
  have fields : extraEdge program arc =
      ⟨dispatch before.pc, port zero (digit before.pc 0), .test (Fin.castAdd 2 register) true⟩ :=
    extraEdge_dec program arc register zero nonzero instruction
  have enabled : (extraEdge program arc).enabled (encode before history) := by
    rw [fields]
    constructor
    · rfl
    · change Action.enabled (.test (Fin.castAdd 2 register) true)
        (frame before.counters history 0)
      simp [Action.enabled, empty]
  have first_step := extra_step program arc (encode before history) enabled
  rw [fields] at first_step
  simp only [Edge.execute, Action.apply, encode, framed] at first_step
  exact pack_firstReturn program (boundary_encode before history) first_step

private theorem positive_firstReturn (program : Counter.Program n m)
    (before : Counter.Configuration n m) (history : ℕ) (register : Fin n) (zero nonzero : Fin m)
    (instruction : program before.pc = .dec register zero nonzero) (value : ℕ)
    (count : before.counters register = value + 1) :
    FirstReturn program (encode before history)
      (encode ⟨nonzero, Function.update before.counters register value⟩
        (base m * history + (digit before.pc 1).val)) := by
  let probe : Extra program := ⟨(before.pc, 1), by unfold Active; rw [instruction]; trivial⟩
  let write : Extra program := ⟨(before.pc, 2), by unfold Active; rw [instruction]; trivial⟩
  have probe_fields : extraEdge program probe =
      ⟨dispatch before.pc, mid before.pc, .test (Fin.castAdd 2 register) false⟩ :=
    extraEdge_dec program probe register zero nonzero instruction
  have write_fields : extraEdge program write =
      ⟨mid before.pc, port nonzero (digit before.pc 1), .shift (Fin.castAdd 2 register) (-1)⟩ :=
    extraEdge_dec program write register zero nonzero instruction
  have probe_enabled : (extraEdge program probe).enabled (encode before history) := by
    rw [probe_fields]
    constructor
    · rfl
    · change Action.enabled (.test (Fin.castAdd 2 register) false)
        (frame before.counters history 0)
      simp [Action.enabled, count]
      omega
  have first_step := extra_step program probe (encode before history) probe_enabled
  rw [probe_fields] at first_step
  simp only [Edge.execute, Action.apply, encode, framed] at first_step
  have write_enabled : (extraEdge program write).enabled
      (framed (mid before.pc) before.counters history 0) := by
    rw [write_fields]
    exact ⟨rfl, trivial⟩
  have second_step := extra_step program write (framed (mid before.pc) before.counters history 0)
    write_enabled
  rw [write_fields] at second_step
  simp only [Edge.execute, framed, dec_frame before.counters history 0 register value count] at second_step
  refine ⟨boundary_encode before history, ⟨nonzero, rfl⟩,
    framed (mid before.pc) before.counters history 0, first_step, ?_⟩
  exact Relation.ReflTransGen.head
    ⟨second_step, not_boundary_mid before.pc before.counters history 0⟩
    (packing_internal_reaches program nonzero (digit before.pc 1)
      (Function.update before.counters register value) history)

/-- Every original counter transition has an actual first return with its complete recoverable log. -/
theorem step_firstReturn (program : Counter.Program n m) {before after : Counter.Configuration n m}
    (transition : Counter.step program before = some after) (history : ℕ) :
    FirstReturn program (encode before history)
      (encode after (Counter.Recorded.push (Counter.Recorded.tag program before) history)) := by
  cases instruction : program before.pc with
  | halt => simp [Counter.step, instruction] at transition
  | inc register target =>
      have result := Option.some.inj ((Counter.step_inc program before instruction).symm.trans transition)
      subst after
      have run := inc_firstReturn program before history register target instruction
      rw [history_digit] at run
      simpa only [Counter.Recorded.tag, Counter.Recorded.branch, instruction] using run
  | dec register zero nonzero =>
      cases count : before.counters register with
      | zero =>
          have result := Option.some.inj
            ((Counter.step_dec_zero program before instruction count).symm.trans transition)
          subst after
          have run := zero_firstReturn program before history register zero nonzero instruction count
          rw [history_digit] at run
          simpa only [Counter.Recorded.tag, Counter.Recorded.branch, instruction, count, ite_true] using run
      | succ value =>
          have result := Option.some.inj
            ((Counter.step_dec_succ program before instruction count).symm.trans transition)
          subst after
          have run := positive_firstReturn program before history register zero nonzero instruction value count
          rw [history_digit] at run
          simpa [Counter.Recorded.tag, Counter.Recorded.branch, instruction, count] using run

/-- Forgetting the internal boundary condition gives a positive actual execution. -/
theorem FirstReturn.reaches {program : Counter.Program n m}
    {first last : State (n + 2) (size m)} (run : FirstReturn program first last) :
    StateTransition.Reaches₁ (step (table program)) first last := by
  obtain ⟨_, _, next, initial, interior⟩ := run
  exact Relation.TransGen.head' initial
    (Relation.ReflTransGen.mono (fun _ _ edge => edge.1) _ _ interior)

/-- A source transition runs the fixed graph and retains its complete recoverable log. -/
theorem step_reaches (program : Counter.Program n m) {before after : Counter.Configuration n m}
    (transition : Counter.step program before = some after) (history : ℕ) :
    StateTransition.Reaches₁ (step (table program)) (encode before history)
      (encode after (Counter.Recorded.push (Counter.Recorded.tag program before) history)) :=
  (step_firstReturn program transition history).reaches

/-- The complete recorded transition system refines to this actual static graph. -/
theorem recorded_respects (program : Counter.Program n m) :
    StateTransition.Respects (Counter.Recorded.step program) (step (table program))
      (fun original compiled => embed original = compiled) := by
  apply StateTransition.fun_respects.mpr
  rintro ⟨before, history⟩
  cases transition : Counter.step program before with
  | none =>
      simp only [Counter.Recorded.step, transition, Option.map_none, StateTransition.FRespects, embed]
      exact (step_encode_none_iff program before history).mpr transition
  | some after =>
      simp only [Counter.Recorded.step, transition, Option.map_some, StateTransition.FRespects, embed]
      exact step_reaches program transition history

/-- Full terminal configurations and undefinedness agree, with the complete history retained. -/
theorem eval_embed (program : Counter.Program n m) (state : Counter.Recorded.State n m) :
    eval (table program) (embed state) =
      embed <$> StateTransition.eval (Counter.Recorded.step program) state :=
  StateTransition.tr_eval' (Counter.Recorded.step program) (step (table program)) embed
    (recorded_respects program) state

/-- The same finite graph in reverse restores the entire source configuration and its prior history. -/
theorem step_reaches_reverse (program : Counter.Program n m)
    {before after : Counter.Configuration n m}
    (transition : Counter.step program before = some after) (history : ℕ) :
    StateTransition.Reaches (step (reverseTable (table program)))
      (encode after (Counter.Recorded.push (Counter.Recorded.tag program before) history))
      (encode before history) :=
  reaches_reverse (table program) (deterministic program) (targetCompatible program)
    (step_reaches program transition history).to_reflTransGen


def Marked (mark : Fin m → Bool) (state : State (n + 2) (size m)) : Prop :=
  ∃ row, state.1 = dispatch row ∧ mark row = true

instance (mark : Fin m → Bool) (state : State (n + 2) (size m)) : Decidable (Marked mark state) :=
  inferInstanceAs (Decidable (∃ row, state.1 = dispatch row ∧ mark row = true))

theorem marked_boundary {mark : Fin m → Bool} {state : State (n + 2) (size m)}
    (marked : Marked mark state) : Boundary state := by
  obtain ⟨row, same, _⟩ := marked
  exact ⟨row, same⟩

theorem marked_encode_iff (mark : Fin m → Bool)
    (state : Counter.Configuration n m) (history : ℕ) :
    Marked mark (encode state history) ↔ mark state.pc = true := by
  constructor
  · rintro ⟨row, same, marked⟩
    have rows := ((copy_eq_iff state.pc row _ _).mp same).1
    exact rows.symm ▸ marked
  · intro marked
    exact ⟨state.pc, rfl, marked⟩

def InternalMarkedStep (program : Counter.Program n m) (mark : Fin m → Bool)
    (first last : State (n + 2) (size m)) : Prop :=
  step (table program) first = some last ∧ ¬ Marked mark first

abbrev InternalMarkedReaches (program : Counter.Program n m) (mark : Fin m → Bool) :=
  Relation.ReflTransGen (InternalMarkedStep program mark)

def MarkedFirstReturn (program : Counter.Program n m) (mark : Fin m → Bool)
    (first last : State (n + 2) (size m)) : Prop :=
  Marked mark first ∧ Marked mark last ∧
    ∃ after, step (table program) first = some after ∧ InternalMarkedReaches program mark after last

private theorem internal_to_marked (program : Counter.Program n m) (mark : Fin m → Bool)
    {first last : State (n + 2) (size m)} (run : InternalReaches program first last) :
    InternalMarkedReaches program mark first last := by
  induction run with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ edge previous =>
      exact previous.tail ⟨edge.1, fun marked => edge.2 (marked_boundary marked)⟩

/-- An unmarked source instruction has no marked geometric return in its execution. -/
theorem counter_internal_step (program : Counter.Program n m) (mark : Fin m → Bool)
    {first last : Counter.Configuration n m} (transition : Counter.step program first = some last)
    (unmarked : mark first.pc = false) (history : ℕ) :
    InternalMarkedReaches program mark (encode first history)
      (encode last (Counter.Recorded.push (Counter.Recorded.tag program first) history)) := by
  obtain ⟨_, _, next, initial, rest⟩ := step_firstReturn program transition history
  apply Relation.ReflTransGen.head (b := next) ?_ (internal_to_marked program mark rest)
  refine ⟨initial, ?_⟩
  rw [marked_encode_iff, unmarked]
  decide

/-- A finite unmarked source run retains its full final configuration and its actual history. -/
theorem counter_internal_reaches (program : Counter.Program n m) (mark : Fin m → Bool)
    {first last : Counter.Configuration n m}
    (run : Relation.ReflTransGen (fun current next : Counter.Configuration n m =>
      Counter.step program current = some next ∧ mark current.pc = false) first last)
    (history : ℕ) :
    ∃ finalHistory, history ≤ finalHistory ∧
      InternalMarkedReaches program mark (encode first history) (encode last finalHistory) := by
  induction run generalizing history with
  | refl => exact ⟨history, le_refl history, Relation.ReflTransGen.refl⟩
  | @tail middle last _ edge previous =>
      obtain ⟨logged, not_smaller, traversed⟩ := previous history
      have growth := Counter.Recorded.history_lt program
        (first := (middle, logged))
        (last := (last, Counter.Recorded.push (Counter.Recorded.tag program middle) logged))
        (by simp only [Counter.Recorded.step, edge.1, Option.map_some])
      exact ⟨Counter.Recorded.push (Counter.Recorded.tag program middle) logged,
        not_smaller.trans (le_of_lt growth),
        traversed.trans (counter_internal_step program mark edge.1 edge.2 logged)⟩

/-- A source first return lifts to the first positive return to the fixed marked ports. -/
theorem marked_firstReturn (program : Counter.Program n m) (mark : Fin m → Bool)
    {first middle last : Counter.Configuration n m}
    (initial : Counter.step program first = some middle)
    (rest : Relation.ReflTransGen (fun current next : Counter.Configuration n m =>
      Counter.step program current = some next ∧ mark current.pc = false) middle last)
    (first_marked : mark first.pc = true) (last_marked : mark last.pc = true) (history : ℕ) :
    ∃ finalHistory, history < finalHistory ∧
      MarkedFirstReturn program mark (encode first history) (encode last finalHistory) := by
  obtain ⟨_, _, next, head, inside⟩ := step_firstReturn program initial history
  obtain ⟨logged, not_smaller, following⟩ := counter_internal_reaches program mark rest
    (Counter.Recorded.push (Counter.Recorded.tag program first) history)
  have growth := Counter.Recorded.history_lt program
    (first := (first, history))
    (last := (middle, Counter.Recorded.push (Counter.Recorded.tag program first) history))
    (by simp only [Counter.Recorded.step, initial, Option.map_some])
  exact ⟨logged, growth.trans_le not_smaller, (marked_encode_iff mark first history).mpr first_marked,
    (marked_encode_iff mark last logged).mpr last_marked, next, head,
    (internal_to_marked program mark inside).trans following⟩

private theorem extra_unitShift (program : Counter.Program n m) (arc : Extra program) :
    Action.UnitShift (extraOperation program arc) := by
  cases instruction : program arc.val.1 with
  | inc register target =>
      rw [extraOperation_inc program arc register target instruction]
      exact Or.inl rfl
  | dec register zero nonzero =>
      rw [extraOperation_dec program arc register zero nonzero instruction]
      rcases arc with ⟨⟨row, branch⟩, active⟩
      fin_cases branch <;> simp [Action.UnitShift]
  | halt =>
      have active := arc.property
      unfold Active at active
      rw [instruction] at active
      exact active.elim

/-- Every shift of the statically compiled recording graph is exactly one unit. -/
theorem unitShift (program : Counter.Program n m) (index : Fin (edges program)) :
    Action.UnitShift (table program index).action := by
  obtain ⟨arc, rfl⟩ := (arcEquiv program).surjective index
  rw [table_arc]
  rcases arc with ⟨row, edge⟩ | arc
  · change Action.UnitShift
      (RegisterRelocation.mapAction (historyRegister n)
        (reverseAction (Radix.table (base m) edge).action))
    rw [RegisterRelocation.unitShift_mapAction, Action.unitShift_reverse]
    exact Radix.unitShift (base m) edge
  · exact extra_unitShift program arc

end Monodromy.Counter.Reversible.Recording

end

/-!
## Reversible prime compression

A finite virtual register vector is encoded in prime exponents. All arithmetic
uses the same two-counter radix graph; shared ports select and restore tests.
Exact first returns preserve the entire source configuration. Ordinary traces
are derived from that stronger execution statement.
-/

noncomputable section

namespace Monodromy.Counter.Reversible.PrimeCompression

variable {n q e : ℕ}

def HasSource (source : Table n q e) (position : Fin q) : Prop :=
  ∃ edge : Fin e, (source edge).source = position

instance (source : Table n q e) (position : Fin q) : Decidable (HasSource source position) :=
  inferInstanceAs (Decidable (∃ edge : Fin e, (source edge).source = position))

def HasRestore (source : Table n q e) (position : Fin q) : Prop :=
  ∃ edge : Fin e, (source edge).target = position ∧
    ∃ register : Fin n, ∃ atZero : Bool, (source edge).action = .test register atZero

instance (source : Table n q e) (position : Fin q) : Decidable (HasRestore source position) :=
  inferInstanceAs (Decidable (∃ edge : Fin e, (source edge).target = position ∧
    ∃ register : Fin n, ∃ atZero : Bool, (source edge).action = .test register atZero))

abbrev SourceSite (source : Table n q e) := {position : Fin q // HasSource source position}
abbrev RestoreSite (source : Table n q e) := {position : Fin q // HasRestore source position}
abbrev HaltSite (source : Table n q e) := {position : Fin q // ¬ HasSource source position}

def sourceEdge (source : Table n q e) (site : SourceSite source) : Fin e :=
  Fin.find (fun edge => (source edge).source = site.val) site.property

theorem sourceEdge_spec (source : Table n q e) (site : SourceSite source) :
    (source (sourceEdge source site)).source = site.val := Fin.find_spec site.property

def restoreEdge (source : Table n q e) (site : RestoreSite source) : Fin e :=
  Fin.find (fun edge => (source edge).target = site.val ∧
    ∃ register : Fin n, ∃ atZero : Bool, (source edge).action = .test register atZero) site.property

theorem restoreEdge_spec (source : Table n q e) (site : RestoreSite source) :
    (source (restoreEdge source site)).target = site.val ∧
      ∃ register : Fin n, ∃ atZero : Bool,
        (source (restoreEdge source site)).action = .test register atZero :=
  Fin.find_spec site.property

def actionRegister : Action n → Fin n
  | .shift register _ => register
  | .test register _ => register

abbrev Module (source : Table n q e) := SourceSite source ⊕ RestoreSite source

def moduleRegister (source : Table n q e) : Module source → Fin n
  | .inl site => actionRegister (source (sourceEdge source site)).action
  | .inr site => actionRegister (source (restoreEdge source site)).action

def modulus (basis : PrimeCode.Basis n) (source : Table n q e) (block : Module source) : ℕ :=
  basis.prime (moduleRegister source block)

instance (basis : PrimeCode.Basis n) (source : Table n q e) (block : Module source) :
    NeZero (modulus basis source block) := ⟨(basis.isPrime _).ne_zero⟩

def reversed (source : Table n q e) : Module source → Bool
  | .inl site => match (source (sourceEdge source site)).action with
      | .shift _ amount => decide (amount = 1)
      | .test _ _ => false
  | .inr _ => true

def componentTable (basis : PrimeCode.Basis n) (source : Table n q e) (block : Module source) :
    Table 2 (Radix.size (modulus basis source block)) (Radix.edges (modulus basis source block)) :=
  if reversed source block then reverseTable (Radix.table (modulus basis source block))
  else Radix.table (modulus basis source block)

theorem component_deterministic (basis : PrimeCode.Basis n) (source : Table n q e)
    (block : Module source) : Deterministic (componentTable basis source block) := by
  unfold componentTable
  split
  · exact reverseTable_deterministic _ (Radix.targetCompatible _)
  · exact Radix.deterministic _

theorem component_targetCompatible (basis : PrimeCode.Basis n) (source : Table n q e)
    (block : Module source) : TargetCompatible (componentTable basis source block) := by
  unfold componentTable
  split
  · exact reverseTable_targetCompatible _ (Radix.deterministic _)
  · exact Radix.targetCompatible _

abbrev RawPart (basis : PrimeCode.Basis n) (source : Table n q e) :=
  Σ block : Module source, Fin (Radix.size (modulus basis source block))

abbrev RawNode (basis : PrimeCode.Basis n) (source : Table n q e) :=
  HaltSite source ⊕ RawPart basis source

abbrev RawArc (basis : PrimeCode.Basis n) (source : Table n q e) :=
  Σ block : Module source, Fin (Radix.edges (modulus basis source block))

def rawSize (basis : PrimeCode.Basis n) (source : Table n q e) : ℕ :=
  Fintype.card (RawNode basis source)

def rawEdges (basis : PrimeCode.Basis n) (source : Table n q e) : ℕ :=
  Fintype.card (RawArc basis source)

def rawNodeEquiv (basis : PrimeCode.Basis n) (source : Table n q e) :
    RawNode basis source ≃ Fin (rawSize basis source) := Fintype.equivFin _

def rawArcEquiv (basis : PrimeCode.Basis n) (source : Table n q e) :
    RawArc basis source ≃ Fin (rawEdges basis source) := Fintype.equivFin _

def moduleNode (basis : PrimeCode.Basis n) (source : Table n q e) (block : Module source)
    (position : Fin (Radix.size (modulus basis source block))) : Fin (rawSize basis source) :=
  rawNodeEquiv basis source (.inr ⟨block, position⟩)

def haltNode (basis : PrimeCode.Basis n) (source : Table n q e) (site : HaltSite source) :
    Fin (rawSize basis source) := rawNodeEquiv basis source (.inl site)

theorem moduleNode_injective (basis : PrimeCode.Basis n) (source : Table n q e) :
    Function.Injective (fun point : RawPart basis source => moduleNode basis source point.1 point.2) :=
  (rawNodeEquiv basis source).injective.comp Sum.inr_injective

theorem haltNode_injective (basis : PrimeCode.Basis n) (source : Table n q e) :
    Function.Injective (haltNode basis source) :=
  (rawNodeEquiv basis source).injective.comp Sum.inl_injective

theorem haltNode_ne_moduleNode (basis : PrimeCode.Basis n) (source : Table n q e)
    (site : HaltSite source) (block : Module source)
    (position : Fin (Radix.size (modulus basis source block))) :
    haltNode basis source site ≠ moduleNode basis source block position := by
  intro same
  have impossible := (rawNodeEquiv basis source).injective same
  cases impossible

def rawEdge (basis : PrimeCode.Basis n) (source : Table n q e) (arc : RawArc basis source) :
    Edge 2 (rawSize basis source) :=
  Glue.mapEdge (moduleNode basis source arc.1) (componentTable basis source arc.1 arc.2)

def rawTable (basis : PrimeCode.Basis n) (source : Table n q e) :
    Table 2 (rawSize basis source) (rawEdges basis source) :=
  fun index => rawEdge basis source ((rawArcEquiv basis source).symm index)

@[simp] theorem rawTable_arc (basis : PrimeCode.Basis n) (source : Table n q e)
    (arc : RawArc basis source) :
    rawTable basis source (rawArcEquiv basis source arc) = rawEdge basis source arc := by
  simp [rawTable]

theorem raw_deterministic (basis : PrimeCode.Basis n) (source : Table n q e) :
    Deterministic (rawTable basis source) := by
  intro first second different same
  obtain ⟨⟨left, first⟩, rfl⟩ := (rawArcEquiv basis source).surjective first
  obtain ⟨⟨right, second⟩, rfl⟩ := (rawArcEquiv basis source).surjective second
  simp only [rawTable_arc, rawEdge, Glue.mapEdge] at same ⊢
  have pairs : (⟨left, (componentTable basis source left first).source⟩ : RawPart basis source) =
      ⟨right, (componentTable basis source right second).source⟩ :=
    moduleNode_injective basis source same
  have blocks : left = right := congrArg Sigma.fst pairs
  subst right
  have positions : (componentTable basis source left first).source =
      (componentTable basis source left second).source := by
    simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using pairs
  exact component_deterministic basis source left first second
    (fun equal => different (by subst second; rfl)) positions

theorem raw_targetCompatible (basis : PrimeCode.Basis n) (source : Table n q e) :
    TargetCompatible (rawTable basis source) := by
  intro first second different same
  obtain ⟨⟨left, first⟩, rfl⟩ := (rawArcEquiv basis source).surjective first
  obtain ⟨⟨right, second⟩, rfl⟩ := (rawArcEquiv basis source).surjective second
  simp only [rawTable_arc, rawEdge, Glue.mapEdge] at same ⊢
  have pairs : (⟨left, (componentTable basis source left first).target⟩ : RawPart basis source) =
      ⟨right, (componentTable basis source right second).target⟩ :=
    moduleNode_injective basis source same
  have blocks : left = right := congrArg Sigma.fst pairs
  subst right
  have positions : (componentTable basis source left first).target =
      (componentTable basis source left second).target := by
    simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using pairs
  exact component_targetCompatible basis source left first second
    (fun equal => different (by subst second; rfl)) positions

/-- A live source address is the actual input port of its sole source module. -/
def sourceInputPosition (basis : PrimeCode.Basis n) (source : Table n q e)
    (site : SourceSite source) : Fin (Radix.size (modulus basis source (.inl site))) :=
  if reversed source (.inl site) then Radix.finish _ 0 else Radix.entry _

def sourceInput (basis : PrimeCode.Basis n) (source : Table n q e) (site : SourceSite source) :
    Fin (rawSize basis source) :=
  moduleNode basis source (.inl site) (sourceInputPosition basis source site)

/-- Only shift modules use this single output; test modules use their actual remainder port. -/
def sourceShiftOutput (basis : PrimeCode.Basis n) (source : Table n q e)
    (site : SourceSite source) : Fin (rawSize basis source) :=
  moduleNode basis source (.inl site)
    (if reversed source (.inl site) then Radix.entry _ else Radix.finish _ 0)

def restoreInput (basis : PrimeCode.Basis n) (source : Table n q e) (site : RestoreSite source)
    (remainder : Fin (modulus basis source (.inr site))) : Fin (rawSize basis source) :=
  moduleNode basis source (.inr site) (Radix.finish _ remainder)

def restoreOutput (basis : PrimeCode.Basis n) (source : Table n q e) (site : RestoreSite source) :
    Fin (rawSize basis source) :=
  moduleNode basis source (.inr site) (Radix.entry _)

/-- Source boundaries are existing input ports; a stopped address is a bare vertex. -/
def boundary (basis : PrimeCode.Basis n) (source : Table n q e) (position : Fin q) :
    Fin (rawSize basis source) :=
  if active : HasSource source position then sourceInput basis source ⟨position, active⟩
  else haltNode basis source ⟨position, active⟩

@[simp] theorem boundary_source (basis : PrimeCode.Basis n) (source : Table n q e)
    (site : SourceSite source) : boundary basis source site.val = sourceInput basis source site := by
  simp only [boundary, dite_eq_left site.property]

@[simp] theorem boundary_halt (basis : PrimeCode.Basis n) (source : Table n q e)
    (site : HaltSite source) : boundary basis source site.val = haltNode basis source site := by
  simp only [boundary, dite_eq_right site.property]

theorem sourceInput_injective (basis : PrimeCode.Basis n) (source : Table n q e) :
    Function.Injective (sourceInput basis source) := by
  intro first second same
  have pairs : (⟨Sum.inl first, sourceInputPosition basis source first⟩ : RawPart basis source) =
      ⟨Sum.inl second, sourceInputPosition basis source second⟩ :=
    moduleNode_injective basis source same
  have modules : Sum.inl first = (Sum.inl second : Module source) := congrArg Sigma.fst pairs
  exact Sum.inl.inj modules

theorem boundary_injective (basis : PrimeCode.Basis n) (source : Table n q e) :
    Function.Injective (boundary basis source) := by
  intro first second same
  by_cases left : HasSource source first
  · by_cases right : HasSource source second
    · simp only [boundary, dite_eq_left left, dite_eq_left right] at same
      exact congrArg Subtype.val (sourceInput_injective basis source same)
    · simp only [boundary, dite_eq_left left, dite_eq_right right, sourceInput] at same
      exact False.elim (haltNode_ne_moduleNode basis source ⟨second, right⟩ _ _ same.symm)
  · by_cases right : HasSource source second
    · simp only [boundary, dite_eq_right left, dite_eq_left right, sourceInput] at same
      exact False.elim (haltNode_ne_moduleNode basis source ⟨first, left⟩ _ _ same)
    · simp only [boundary, dite_eq_right left, dite_eq_right right] at same
      exact congrArg Subtype.val (haltNode_injective basis source same)

theorem component_no_incoming_sourceInput (basis : PrimeCode.Basis n) (source : Table n q e)
    (site : SourceSite source) (index : Fin (Radix.edges (modulus basis source (.inl site)))) :
    (componentTable basis source (.inl site) index).target ≠ sourceInputPosition basis source site := by
  unfold componentTable sourceInputPosition
  split_ifs
  · exact fun same => Radix.no_outgoing_finish _ 0 ⟨index, same⟩
  · exact Radix.no_incoming_entry _ index

/-- No original edge enters a source boundary; only static port identification can enter it. -/
theorem raw_no_incoming_boundary (basis : PrimeCode.Basis n) (source : Table n q e)
    (position : Fin q) (index : Fin (rawEdges basis source)) :
    (rawTable basis source index).target ≠ boundary basis source position := by
  intro same
  obtain ⟨⟨block, index⟩, rfl⟩ := (rawArcEquiv basis source).surjective index
  simp only [rawTable_arc, rawEdge, Glue.mapEdge] at same
  by_cases active : HasSource source position
  · simp only [boundary, dite_eq_left active, sourceInput] at same
    have pairs : (⟨block, (componentTable basis source block index).target⟩ : RawPart basis source) =
        ⟨Sum.inl ⟨position, active⟩, sourceInputPosition basis source ⟨position, active⟩⟩ :=
      moduleNode_injective basis source same
    have blocks : block = Sum.inl ⟨position, active⟩ := congrArg Sigma.fst pairs
    subst block
    have ports : (componentTable basis source (.inl ⟨position, active⟩) index).target =
        sourceInputPosition basis source ⟨position, active⟩ := by
      simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using pairs
    exact component_no_incoming_sourceInput basis source ⟨position, active⟩ index ports
  · simp only [boundary, dite_eq_right active] at same
    exact haltNode_ne_moduleNode basis source ⟨position, active⟩ _ _ same.symm

/-- Module labels are preserved before the ports are identified. -/
theorem moduleNode_module (basis : PrimeCode.Basis n) (source : Table n q e)
    {first last : Module source}
    {initial : Fin (Radix.size (modulus basis source first))}
    {final : Fin (Radix.size (modulus basis source last))}
    (same : moduleNode basis source first initial = moduleNode basis source last final) :
    first = last := by
  have pairs : (⟨first, initial⟩ : RawPart basis source) = ⟨last, final⟩ :=
    moduleNode_injective basis source same
  exact congrArg Sigma.fst pairs

/-- Positions in one disjoint module retain their ordinary finite equality. -/
theorem moduleNode_position (basis : PrimeCode.Basis n) (source : Table n q e)
    (block : Module source)
    {first last : Fin (Radix.size (modulus basis source block))}
    (same : moduleNode basis source block first = moduleNode basis source block last) :
    first = last := by
  have pairs : (⟨block, first⟩ : RawPart basis source) = ⟨block, last⟩ :=
    moduleNode_injective basis source same
  simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using pairs

/-- A local exit has no outgoing edge in the entire disjoint family. -/
theorem raw_no_outgoing_moduleNode (basis : PrimeCode.Basis n) (source : Table n q e)
    (block : Module source) (position : Fin (Radix.size (modulus basis source block)))
    (no_outgoing : ∀ index, (componentTable basis source block index).source ≠ position)
    (index : Fin (rawEdges basis source)) :
    (rawTable basis source index).source ≠ moduleNode basis source block position := by
  intro same
  obtain ⟨⟨other, index⟩, rfl⟩ := (rawArcEquiv basis source).surjective index
  simp only [rawTable_arc, rawEdge, Glue.mapEdge] at same
  have blocks := moduleNode_module basis source same
  subst other
  exact no_outgoing index (moduleNode_position basis source block same)

/-- A local input has no incoming edge in the entire disjoint family. -/
theorem raw_no_incoming_moduleNode (basis : PrimeCode.Basis n) (source : Table n q e)
    (block : Module source) (position : Fin (Radix.size (modulus basis source block)))
    (no_incoming : ∀ index, (componentTable basis source block index).target ≠ position)
    (index : Fin (rawEdges basis source)) :
    (rawTable basis source index).target ≠ moduleNode basis source block position := by
  intro same
  obtain ⟨⟨other, index⟩, rfl⟩ := (rawArcEquiv basis source).surjective index
  simp only [rawTable_arc, rawEdge, Glue.mapEdge] at same
  have blocks := moduleNode_module basis source same
  subst other
  exact no_incoming index (moduleNode_position basis source block same)

/-- The source shift's selected exit is an exit in either orientation. -/
theorem raw_no_outgoing_sourceShiftOutput (basis : PrimeCode.Basis n) (source : Table n q e)
    (site : SourceSite source) (index : Fin (rawEdges basis source)) :
    (rawTable basis source index).source ≠ sourceShiftOutput basis source site := by
  apply raw_no_outgoing_moduleNode
  intro localIndex
  unfold componentTable
  split_ifs with backwards
  · simpa only [sourceShiftOutput, backwards, reduceIte, reverseTable, reverseEdge] using
      Radix.no_incoming_entry (modulus basis source (.inl site)) localIndex
  · simpa only [sourceShiftOutput, backwards, reduceIte] using
      (fun same => Radix.no_outgoing_finish (modulus basis source (.inl site)) 0 ⟨localIndex, same⟩)

/-- A forward query's actual remainder exits have no outgoing edge. -/
theorem raw_no_outgoing_sourceFinish (basis : PrimeCode.Basis n) (source : Table n q e)
    (site : SourceSite source) (remainder : Fin (modulus basis source (.inl site)))
    (forward : reversed source (.inl site) = false) (index : Fin (rawEdges basis source)) :
    (rawTable basis source index).source ≠
      moduleNode basis source (.inl site) (Radix.finish _ remainder) := by
  apply raw_no_outgoing_moduleNode
  intro localIndex
  simpa only [componentTable, forward, Bool.false_eq_true, reduceIte] using
    (fun same => Radix.no_outgoing_finish (modulus basis source (.inl site)) remainder ⟨localIndex, same⟩)

theorem raw_no_outgoing_restoreOutput (basis : PrimeCode.Basis n) (source : Table n q e)
    (site : RestoreSite source) (index : Fin (rawEdges basis source)) :
    (rawTable basis source index).source ≠ restoreOutput basis source site := by
  apply raw_no_outgoing_moduleNode
  intro localIndex
  exact Radix.no_incoming_entry (modulus basis source (.inr site)) localIndex

theorem raw_no_incoming_restoreInput (basis : PrimeCode.Basis n) (source : Table n q e)
    (site : RestoreSite source) (remainder : Fin (modulus basis source (.inr site)))
    (index : Fin (rawEdges basis source)) :
    (rawTable basis source index).target ≠ restoreInput basis source site remainder := by
  apply raw_no_incoming_moduleNode
  intro localIndex
  exact fun same => Radix.no_outgoing_finish (modulus basis source (.inr site)) remainder
    ⟨localIndex, same⟩

theorem radix_entry_ne_finish (p : ℕ) (remainder : Fin p) :
    Radix.entry p ≠ Radix.finish p remainder := by
  intro same
  cases (Radix.nodeEquiv p).injective same

/-- A source-module point can meet a boundary only at its own source input. -/
theorem sourceNode_ne_boundary (basis : PrimeCode.Basis n) (source : Table n q e)
    (site : SourceSite source) (position : Fin (Radix.size (modulus basis source (.inl site))))
    (different : position ≠ sourceInputPosition basis source site) (target : Fin q) :
    moduleNode basis source (.inl site) position ≠ boundary basis source target := by
  intro same
  by_cases active : HasSource source target
  · simp only [boundary, dite_eq_left active] at same
    have sites : site = (⟨target, active⟩ : SourceSite source) :=
      Sum.inl.inj (moduleNode_module basis source same)
    have aligned := same.trans (congrArg (sourceInput basis source) sites).symm
    exact different (moduleNode_position basis source (.inl site) aligned)
  · simp only [boundary, dite_eq_right active] at same
    exact haltNode_ne_moduleNode basis source ⟨target, active⟩ _ _ same.symm

theorem sourceShiftOutput_ne_boundary (basis : PrimeCode.Basis n) (source : Table n q e)
    (site : SourceSite source) (target : Fin q) :
    sourceShiftOutput basis source site ≠ boundary basis source target := by
  apply sourceNode_ne_boundary
  intro same
  unfold sourceInputPosition at same
  split_ifs at same
  · exact radix_entry_ne_finish _ 0 same
  · exact radix_entry_ne_finish _ 0 same.symm

theorem sourceFinish_ne_boundary (basis : PrimeCode.Basis n) (source : Table n q e)
    (site : SourceSite source) (remainder : Fin (modulus basis source (.inl site)))
    (forward : reversed source (.inl site) = false) (target : Fin q) :
    moduleNode basis source (.inl site) (Radix.finish _ remainder) ≠ boundary basis source target := by
  apply sourceNode_ne_boundary
  intro same
  simp only [sourceInputPosition, forward, Bool.false_eq_true, reduceIte] at same
  exact radix_entry_ne_finish _ remainder same.symm

theorem restoreOutput_ne_boundary (basis : PrimeCode.Basis n) (source : Table n q e)
    (site : RestoreSite source) (target : Fin q) :
    restoreOutput basis source site ≠ boundary basis source target := by
  intro same
  by_cases active : HasSource source target
  · simp only [boundary, dite_eq_left active] at same
    cases moduleNode_module basis source same
  · simp only [boundary, dite_eq_right active] at same
    exact haltNode_ne_moduleNode basis source ⟨target, active⟩ _ _ same.symm

theorem sourceNode_ne_restoreInput (basis : PrimeCode.Basis n) (source : Table n q e)
    (first : SourceSite source) (position : Fin (Radix.size (modulus basis source (.inl first))))
    (last : RestoreSite source) (remainder : Fin (modulus basis source (.inr last))) :
    moduleNode basis source (.inl first) position ≠ restoreInput basis source last remainder := by
  intro same
  cases moduleNode_module basis source same

theorem sourceShiftOutput_ne_restoreInput (basis : PrimeCode.Basis n) (source : Table n q e)
    (first : SourceSite source) (last : RestoreSite source)
    (remainder : Fin (modulus basis source (.inr last))) :
    sourceShiftOutput basis source first ≠ restoreInput basis source last remainder :=
  sourceNode_ne_restoreInput basis source first _ last remainder

theorem sourceFinish_ne_restoreInput (basis : PrimeCode.Basis n) (source : Table n q e)
    (first : SourceSite source) (initial : Fin (modulus basis source (.inl first)))
    (last : RestoreSite source) (remainder : Fin (modulus basis source (.inr last))) :
    moduleNode basis source (.inl first) (Radix.finish _ initial) ≠ restoreInput basis source last remainder :=
  sourceNode_ne_restoreInput basis source first _ last remainder

theorem restoreOutput_ne_restoreInput (basis : PrimeCode.Basis n) (source : Table n q e)
    (first last : RestoreSite source) (remainder : Fin (modulus basis source (.inr last))) :
    restoreOutput basis source first ≠ restoreInput basis source last remainder := by
  intro same
  have sites : first = last := Sum.inr.inj (moduleNode_module basis source same)
  subst first
  exact radix_entry_ne_finish _ remainder (moduleNode_position basis source (.inr last) same)

/-- An unconditional edge has no different edge at the same compatible owner. -/
theorem shift_owner_unique (table : Table n q e) (owner : Fin e → Fin q)
    (compatible : ∀ first second, first ≠ second → owner first = owner second →
      Action.Compatible (table first).action (table second).action)
    {first second : Fin e} {register : Fin n} {amount : ℤ}
    (shift : (table first).action = .shift register amount)
    (same : owner first = owner second) : first = second := by
  by_contra different
  have impossible := compatible first second different same
  rw [shift] at impossible
  cases (table second).action <;> exact impossible

/-- Different tests at a common compatible owner use the same register and opposite guards. -/
theorem test_owner_alternative (table : Table n q e) (owner : Fin e → Fin q)
    (compatible : ∀ first second, first ≠ second → owner first = owner second →
      Action.Compatible (table first).action (table second).action)
    {first second : Fin e} {register : Fin n} {atZero : Bool}
    (test : (table first).action = .test register atZero)
    (different : first ≠ second) (same : owner first = owner second) :
    (table second).action = .test register (!atZero) := by
  have alternatives := compatible first second different same
  rw [test] at alternatives
  cases result : (table second).action with
  | shift => simp [result, Action.Compatible] at alternatives
  | test other flag =>
      rw [result] at alternatives
      rcases alternatives with ⟨rfl, different_flags⟩
      cases atZero <;> cases flag <;> simp_all

/-- One test fixes the register of every edge at the same compatible owner. -/
theorem test_owner_form (table : Table n q e) (owner : Fin e → Fin q)
    (compatible : ∀ first second, first ≠ second → owner first = owner second →
      Action.Compatible (table first).action (table second).action)
    {first second : Fin e} {register : Fin n} {atZero : Bool}
    (test : (table first).action = .test register atZero)
    (same : owner first = owner second) :
    ∃ flag, (table second).action = .test register flag := by
  by_cases equal : first = second
  · subst second
    exact ⟨atZero, test⟩
  · exact ⟨!atZero, test_owner_alternative table owner compatible test equal same⟩

/-- Shared test modules have an unambiguous virtual register on either side. -/
theorem test_owner_register_unique (table : Table n q e) (owner : Fin e → Fin q)
    (compatible : ∀ first second, first ≠ second → owner first = owner second →
      Action.Compatible (table first).action (table second).action)
    {first second : Fin e} {register other : Fin n} {atZero otherZero : Bool}
    (first_test : (table first).action = .test register atZero)
    (second_test : (table second).action = .test other otherZero)
    (same : owner first = owner second) : register = other := by
  obtain ⟨flag, form⟩ := test_owner_form table owner compatible first_test same
  exact (Action.test.inj (form.symm.trans second_test)).1

/-- The residue port selects zero exactly when the represented exponent is zero. -/
def testSelected (table : Table n q e) (register : Fin n) (remainder : ℕ) (edge : Fin e) : Bool :=
  decide ((table edge).action = .test register (decide (remainder ≠ 0)))

@[simp] theorem testSelected_iff (table : Table n q e) (register : Fin n) (remainder : ℕ)
    (edge : Fin e) :
    testSelected table register remainder edge = true ↔
      (table edge).action = .test register (decide (remainder ≠ 0)) := by
  simp [testSelected]

/-- One reached residue chooses at most one test at each compatible owner. -/
theorem test_matching (table : Table n q e) (owner : Fin e → Fin q)
    (compatible : ∀ first second, first ≠ second → owner first = owner second →
      Action.Compatible (table first).action (table second).action)
    (register : Fin n) (remainder : ℕ) :
    ReversiblePorts.Matching owner (testSelected table register remainder) := by
  intro first second first_selected second_selected same
  by_contra different
  have alternatives := compatible first second different same
  rw [(testSelected_iff table register remainder first).mp first_selected,
    (testSelected_iff table register remainder second).mp second_selected] at alternatives
  exact alternatives.2 rfl

theorem source_test_matching (table : Table n q e) (deterministic : Deterministic table)
    (register : Fin n) (remainder : ℕ) :
    ReversiblePorts.Matching (fun edge => (table edge).source)
      (testSelected table register remainder) :=
  test_matching table (fun edge => (table edge).source) deterministic register remainder

theorem target_test_matching (table : Table n q e) (compatible : TargetCompatible table)
    (register : Fin n) (remainder : ℕ) :
    ReversiblePorts.Matching (fun edge => (table edge).target)
      (testSelected table register remainder) :=
  test_matching table (fun edge => (table edge).target) compatible register remainder

/-- A shared residue port therefore defines a partial one-to-one source-to-target connection. -/
theorem test_ports_partial_matching (table : Table n q e)
    (deterministic : Deterministic table) (compatible : TargetCompatible table)
    (register : Fin n) (remainder : ℕ) :
    ReversiblePorts.Matching (fun edge => (table edge).source)
        (testSelected table register remainder) ∧
      ReversiblePorts.Matching (fun edge => (table edge).target)
        (testSelected table register remainder) :=
  ⟨source_test_matching table deterministic register remainder,
    target_test_matching table compatible register remainder⟩

/-- Divisibility of the prime code reads the complementary zero/nonzero source test. -/
theorem residue_zero_flag (basis : Monodromy.PrimeCode.Basis n)
    (values : Fin n → ℕ) (register : Fin n) :
    decide (basis.encode values % basis.prime register ≠ 0) = decide (values register = 0) := by
  apply decide_eq_decide.mpr
  exact (not_congr (basis.remainder_zero_iff values register)).trans not_not

/-- Test-port selection agrees with the unchanged source guard on the encoded natural domain. -/
theorem testSelected_encoded_iff (table : Table n q e)
    (basis : Monodromy.PrimeCode.Basis n) (values : Fin n → ℕ)
    (register : Fin n) (edge : Fin e) (atZero : Bool)
    (test : (table edge).action = .test register atZero) :
    testSelected table register (basis.encode values % basis.prime register) edge = true ↔
      (table edge).action.enabled (fun index => (values index : ℤ)) := by
  rw [testSelected_iff, test, residue_zero_flag]
  cases atZero <;> simp [Action.enabled]

/-- A unit shift leaves its radix module at the original target address. -/
def ShiftConnection (basis : PrimeCode.Basis n) (source : Table n q e)
    (exit entry : Fin (rawSize basis source)) : Prop :=
  ∃ site : SourceSite source,
    (source (sourceEdge source site)).action.IsShift ∧
    exit = sourceShiftOutput basis source site ∧
    entry = boundary basis source (source (sourceEdge source site)).target

/-- Restoring a tested code ends at the target's existing execution boundary. -/
def RestoreConnection (basis : PrimeCode.Basis n) (source : Table n q e)
    (exit entry : Fin (rawSize basis source)) : Prop :=
  ∃ site : RestoreSite source,
    exit = restoreOutput basis source site ∧ entry = boundary basis source site.val

/-- A reached remainder port chooses a static source edge and its restoration port. -/
def TestConnection (basis : PrimeCode.Basis n) (source : Table n q e)
    (exit entry : Fin (rawSize basis source)) : Prop :=
  ∃ first : SourceSite source, ∃ last : RestoreSite source,
    ∃ remainder : Fin (modulus basis source (.inl first)),
    ∃ restored : Fin (modulus basis source (.inr last)), ∃ edge : Fin e,
      (source edge).source = first.val ∧ (source edge).target = last.val ∧
      testSelected source (moduleRegister source (.inl first)) remainder.val edge = true ∧
      moduleRegister source (.inl first) = moduleRegister source (.inr last) ∧
      remainder.val = restored.val ∧
      exit = moduleNode basis source (.inl first) (Radix.finish _ remainder) ∧
      entry = restoreInput basis source last restored

/-- The entire connection relation is finite program data. -/
def Connection (basis : PrimeCode.Basis n) (source : Table n q e)
    (exit entry : Fin (rawSize basis source)) : Prop :=
  ShiftConnection basis source exit entry ∨
    RestoreConnection basis source exit entry ∨ TestConnection basis source exit entry

instance (basis : PrimeCode.Basis n) (source : Table n q e) :
    DecidableRel (Connection basis source) := by
  intro exit entry
  unfold Connection ShiftConnection RestoreConnection TestConnection
  infer_instance

private theorem sourceShiftOutput_injective (basis : PrimeCode.Basis n) (source : Table n q e) :
    Function.Injective (sourceShiftOutput basis source) := by
  intro first last same
  exact Sum.inl.inj (moduleNode_module basis source same)

private theorem restoreOutput_injective (basis : PrimeCode.Basis n) (source : Table n q e) :
    Function.Injective (restoreOutput basis source) := by
  intro first last same
  exact Sum.inr.inj (moduleNode_module basis source same)

private theorem source_restore_disjoint (basis : PrimeCode.Basis n) (source : Table n q e)
    (first : SourceSite source) (last : RestoreSite source)
    (initial : Fin (Radix.size (modulus basis source (.inl first))))
    (final : Fin (Radix.size (modulus basis source (.inr last)))) :
    moduleNode basis source (.inl first) initial ≠ moduleNode basis source (.inr last) final := by
  intro same
  cases moduleNode_module basis source same

private theorem selected_source_form (source : Table n q e) (deterministic : Deterministic source)
    (site : SourceSite source) (remainder : ℕ) (edge : Fin e)
    (same : (source edge).source = site.val)
    (chosen : testSelected source (moduleRegister source (.inl site)) remainder edge = true) :
    ∃ flag, (source (sourceEdge source site)).action =
      .test (moduleRegister source (.inl site)) flag := by
  exact test_owner_form source (fun index => (source index).source) deterministic
    ((testSelected_iff source _ _ edge).mp chosen)
    (same.trans (sourceEdge_spec source site).symm)

private theorem shift_test_disjoint (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) {exit first last : Fin (rawSize basis source)}
    (shift : ShiftConnection basis source exit first)
    (test : TestConnection basis source exit last) : False := by
  obtain ⟨site, is_shift, exit_shift, _⟩ := shift
  obtain ⟨start, finish, remainder, restored, edge, same_source, _, selected, _, _, exit_test, _⟩ := test
  have modules : (Sum.inl site : Module source) = Sum.inl start :=
    moduleNode_module basis source (exit_shift.symm.trans exit_test)
  have sites : site = start := Sum.inl.inj modules
  subst start
  obtain ⟨flag, form⟩ := selected_source_form source deterministic site remainder.val edge same_source selected
  rw [form] at is_shift
  exact is_shift

private theorem test_connection_functional (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) {exit first last : Fin (rawSize basis source)}
    (left : TestConnection basis source exit first)
    (right : TestConnection basis source exit last) : first = last := by
  obtain ⟨left_site, left_target, left_r, left_s, left_edge, left_src, left_dst,
    left_selected, _, left_values, left_exit, left_entry⟩ := left
  obtain ⟨right_site, right_target, right_r, right_s, right_edge, right_src, right_dst,
    right_selected, _, right_values, right_exit, right_entry⟩ := right
  have sites : left_site = right_site := Sum.inl.inj
    (moduleNode_module basis source (left_exit.symm.trans right_exit))
  subst right_site
  have finishes := moduleNode_position basis source (.inl left_site)
    (left_exit.symm.trans right_exit)
  have residues : left_r = right_r := by
    have pair := (Radix.nodeEquiv _).injective finishes
    simpa only [Sum.inr.injEq, Prod.mk.injEq, and_true] using pair
  subst right_r
  have edges : left_edge = right_edge := source_test_matching source deterministic
    (moduleRegister source (.inl left_site)) left_r.val
    left_edge right_edge left_selected right_selected (left_src.trans right_src.symm)
  subst right_edge
  have targets : left_target = right_target := Subtype.ext (left_dst.symm.trans right_dst)
  subst right_target
  have restored : left_s = right_s := Fin.ext (left_values.symm.trans right_values)
  subst right_s
  exact left_entry.trans right_entry.symm

/-- Each existing exit is identified with at most one existing entry. -/
theorem connection_functional (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) {exit first last : Fin (rawSize basis source)}
    (left : Connection basis source exit first)
    (right : Connection basis source exit last) : first = last := by
  rcases left with left | left | left <;> rcases right with right | right | right
  · obtain ⟨left_site, _, left_exit, left_entry⟩ := left
    obtain ⟨right_site, _, right_exit, right_entry⟩ := right
    have same := sourceShiftOutput_injective basis source (left_exit.symm.trans right_exit)
    subst right_site
    exact left_entry.trans right_entry.symm
  · obtain ⟨left_site, _, left_exit, _⟩ := left
    obtain ⟨right_site, right_exit, _⟩ := right
    exact False.elim (source_restore_disjoint basis source left_site right_site _ _
      (left_exit.symm.trans right_exit))
  · exact False.elim (shift_test_disjoint basis source deterministic left right)
  · obtain ⟨left_site, left_exit, _⟩ := left
    obtain ⟨right_site, _, right_exit, _⟩ := right
    exact False.elim (source_restore_disjoint basis source right_site left_site _ _
      (right_exit.symm.trans left_exit))
  · obtain ⟨left_site, left_exit, left_entry⟩ := left
    obtain ⟨right_site, right_exit, right_entry⟩ := right
    have same := restoreOutput_injective basis source (left_exit.symm.trans right_exit)
    subst right_site
    exact left_entry.trans right_entry.symm
  · obtain ⟨left_site, left_exit, _⟩ := left
    obtain ⟨right_site, _, right_r, _, _, _, _, _, _, _, right_exit, _⟩ := right
    exact False.elim (source_restore_disjoint basis source right_site left_site _ _
      (right_exit.symm.trans left_exit))
  · exact False.elim (shift_test_disjoint basis source deterministic right left)
  · obtain ⟨left_site, _, left_r, _, _, _, _, _, _, _, left_exit, _⟩ := left
    obtain ⟨right_site, right_exit, _⟩ := right
    exact False.elim (source_restore_disjoint basis source left_site right_site _ _
      (left_exit.symm.trans right_exit))
  · exact test_connection_functional basis source deterministic left right

private theorem boundary_ne_restoreInput (basis : PrimeCode.Basis n) (source : Table n q e)
    (position : Fin q) (site : RestoreSite source)
    (remainder : Fin (modulus basis source (.inr site))) :
    boundary basis source position ≠ restoreInput basis source site remainder := by
  intro same
  by_cases active : HasSource source position
  · simp only [boundary, dite_eq_left active, sourceInput, restoreInput] at same
    cases moduleNode_module basis source same
  · simp only [boundary, dite_eq_right active] at same
    exact haltNode_ne_moduleNode basis source ⟨position, active⟩ _ _ same

private theorem shift_connection_backward (basis : PrimeCode.Basis n) (source : Table n q e)
    (compatible : TargetCompatible source) {first last entry : Fin (rawSize basis source)}
    (left : ShiftConnection basis source first entry)
    (right : ShiftConnection basis source last entry) : first = last := by
  obtain ⟨left_site, left_shift, left_exit, left_entry⟩ := left
  obtain ⟨right_site, _, right_exit, right_entry⟩ := right
  have targets := boundary_injective basis source (left_entry.symm.trans right_entry)
  have edges : sourceEdge source left_site = sourceEdge source right_site := by
    cases action : (source (sourceEdge source left_site)).action with
    | test => simp [action, Action.IsShift] at left_shift
    | shift register amount =>
        exact shift_owner_unique source (fun edge => (source edge).target) compatible action targets
  have sites : left_site = right_site := Subtype.ext (by
    calc
      left_site.val = (source (sourceEdge source left_site)).source :=
        (sourceEdge_spec source left_site).symm
      _ = (source (sourceEdge source right_site)).source := congrArg (fun edge => (source edge).source) edges
      _ = right_site.val := sourceEdge_spec source right_site)
  subst right_site
  exact left_exit.trans right_exit.symm

private theorem shift_restore_disjoint (basis : PrimeCode.Basis n) (source : Table n q e)
    (compatible : TargetCompatible source) {first last entry : Fin (rawSize basis source)}
    (shift : ShiftConnection basis source first entry)
    (restore : RestoreConnection basis source last entry) : False := by
  obtain ⟨left, is_shift, _, left_entry⟩ := shift
  obtain ⟨right, _, right_entry⟩ := restore
  have targets := boundary_injective basis source (left_entry.symm.trans right_entry)
  obtain ⟨register, atZero, test⟩ := (restoreEdge_spec source right).2
  obtain ⟨flag, form⟩ := test_owner_form source (fun edge => (source edge).target) compatible test
    ((restoreEdge_spec source right).1.trans targets.symm)
  rw [form] at is_shift
  exact is_shift

private theorem test_connection_backward (basis : PrimeCode.Basis n) (source : Table n q e)
    (compatible : TargetCompatible source) {first last entry : Fin (rawSize basis source)}
    (left : TestConnection basis source first entry)
    (right : TestConnection basis source last entry) : first = last := by
  obtain ⟨left_site, left_target, left_r, left_s, left_edge, left_src, left_dst,
    left_selected, left_registers, left_values, left_exit, left_entry⟩ := left
  obtain ⟨right_site, right_target, right_r, right_s, right_edge, right_src, right_dst,
    right_selected, right_registers, right_values, right_exit, right_entry⟩ := right
  have targets : left_target = right_target := Sum.inr.inj
    (moduleNode_module basis source (left_entry.symm.trans right_entry))
  subst right_target
  have finishes := moduleNode_position basis source (.inr left_target)
    (left_entry.symm.trans right_entry)
  have restored : left_s = right_s := by
    have pair := (Radix.nodeEquiv _).injective finishes
    simpa only [Sum.inr.injEq, Prod.mk.injEq, and_true] using pair
  subst right_s
  have residues : left_r.val = right_r.val := left_values.trans right_values.symm
  have registers : moduleRegister source (.inl left_site) = moduleRegister source (.inl right_site) :=
    left_registers.trans right_registers.symm
  have right_chosen : testSelected source (moduleRegister source (.inl left_site)) left_r.val
      right_edge = true := by
    rw [registers, residues]
    exact right_selected
  have edges : left_edge = right_edge := target_test_matching source compatible
    (moduleRegister source (.inl left_site)) left_r.val left_edge right_edge
    left_selected right_chosen (left_dst.trans right_dst.symm)
  subst right_edge
  have sources : left_site = right_site := Subtype.ext (left_src.symm.trans right_src)
  subst right_site
  have residue : left_r = right_r := Fin.ext residues
  subst right_r
  exact left_exit.trans right_exit.symm

/-- Static port wiring is injective toward each entry, including all three connection forms. -/
theorem connection_backward (basis : PrimeCode.Basis n) (source : Table n q e)
    (compatible : TargetCompatible source) {first last entry : Fin (rawSize basis source)}
    (left : Connection basis source first entry)
    (right : Connection basis source last entry) : first = last := by
  rcases left with left | left | left <;> rcases right with right | right | right
  · exact shift_connection_backward basis source compatible left right
  · exact False.elim (shift_restore_disjoint basis source compatible left right)
  · obtain ⟨site, _, _, entered⟩ := left
    obtain ⟨_, target, _, residue, _, _, _, _, _, _, _, restored⟩ := right
    exact False.elim (boundary_ne_restoreInput basis source _ target residue
      (entered.symm.trans restored))
  · exact False.elim (shift_restore_disjoint basis source compatible right left)
  · obtain ⟨left_site, left_exit, left_entry⟩ := left
    obtain ⟨right_site, right_exit, right_entry⟩ := right
    have sites : left_site = right_site := Subtype.ext
      (boundary_injective basis source (left_entry.symm.trans right_entry))
    subst right_site
    exact left_exit.trans right_exit.symm
  · obtain ⟨site, _, entered⟩ := left
    obtain ⟨_, target, _, residue, _, _, _, _, _, _, _, restored⟩ := right
    exact False.elim (boundary_ne_restoreInput basis source site.val target residue
      (entered.symm.trans restored))
  · obtain ⟨_, target, _, residue, _, _, _, _, _, _, _, restored⟩ := left
    obtain ⟨site, _, _, entered⟩ := right
    exact False.elim (boundary_ne_restoreInput basis source _ target residue
      (entered.symm.trans restored))
  · obtain ⟨_, target, _, residue, _, _, _, _, _, _, _, restored⟩ := left
    obtain ⟨site, _, entered⟩ := right
    exact False.elim (boundary_ne_restoreInput basis source site.val target residue
      (entered.symm.trans restored))
  · exact test_connection_backward basis source compatible left right

private theorem selected_forward (source : Table n q e) (deterministic : Deterministic source)
    (site : SourceSite source) (remainder : ℕ) (edge : Fin e)
    (same : (source edge).source = site.val)
    (chosen : testSelected source (moduleRegister source (.inl site)) remainder edge = true) :
    reversed source (.inl site) = false := by
  obtain ⟨flag, form⟩ := test_owner_form source (fun index => (source index).source) deterministic
    ((testSelected_iff source _ _ edge).mp chosen)
    (same.trans (sourceEdge_spec source site).symm)
  simp only [reversed, form]

/-- Only true module exits are connected; no original source is removed. -/
theorem connection_source_free (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (index : Fin (rawEdges basis source))
    (entry : Fin (rawSize basis source)) :
    ¬ Connection basis source (rawTable basis source index).source entry := by
  rintro (shift | restore | test)
  · obtain ⟨site, _, same, _⟩ := shift
    exact raw_no_outgoing_sourceShiftOutput basis source site index same
  · obtain ⟨site, same, _⟩ := restore
    exact raw_no_outgoing_restoreOutput basis source site index same
  · obtain ⟨site, _, remainder, _, edge, same_source, _, selected, _, _, same, _⟩ := test
    exact raw_no_outgoing_sourceFinish basis source site remainder
      (selected_forward source deterministic site remainder.val edge same_source selected) index same

/-- Every selected destination is an original input with no incoming edge. -/
theorem connection_target_free (basis : PrimeCode.Basis n) (source : Table n q e)
    (index : Fin (rawEdges basis source)) (exit : Fin (rawSize basis source)) :
    ¬ Connection basis source exit (rawTable basis source index).target := by
  rintro (shift | restore | test)
  · obtain ⟨site, _, _, same⟩ := shift
    exact raw_no_incoming_boundary basis source _ index same
  · obtain ⟨site, _, same⟩ := restore
    exact raw_no_incoming_boundary basis source site.val index same
  · obtain ⟨_, site, _, remainder, _, _, _, _, _, _, _, same⟩ := test
    exact raw_no_incoming_restoreInput basis source site remainder index same

/-- Original execution boundaries are retained vertices of the compressed graph. -/
theorem boundary_unconnected (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (position : Fin q)
    (entry : Fin (rawSize basis source)) :
    ¬ Connection basis source (boundary basis source position) entry := by
  rintro (shift | restore | test)
  · obtain ⟨site, _, same, _⟩ := shift
    exact sourceShiftOutput_ne_boundary basis source site position same.symm
  · obtain ⟨site, same, _⟩ := restore
    exact restoreOutput_ne_boundary basis source site position same.symm
  · obtain ⟨site, _, remainder, _, edge, same_source, _, selected, _, _, same, _⟩ := test
    exact sourceFinish_ne_boundary basis source site remainder
      (selected_forward source deterministic site remainder.val edge same_source selected)
      position same.symm

/-- Restoration entries are retained vertices, including their selected remainder. -/
theorem restoreInput_unconnected (basis : PrimeCode.Basis n) (source : Table n q e)
    (site : RestoreSite source) (remainder : Fin (modulus basis source (.inr site)))
    (entry : Fin (rawSize basis source)) :
    ¬ Connection basis source (restoreInput basis source site remainder) entry := by
  rintro (shift | restore | test)
  · obtain ⟨first, _, same, _⟩ := shift
    exact sourceShiftOutput_ne_restoreInput basis source first site remainder same.symm
  · obtain ⟨first, same, _⟩ := restore
    exact restoreOutput_ne_restoreInput basis source first site remainder same.symm
  · obtain ⟨first, _, selected, _, _, _, _, _, _, _, same, _⟩ := test
    exact sourceFinish_ne_restoreInput basis source first selected site remainder same.symm

/-- Identification has depth one: its entry is already a retained control position. -/
theorem connection_terminal (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) {exit entry : Fin (rawSize basis source)}
    (connected : Connection basis source exit entry) (next : Fin (rawSize basis source)) :
    ¬ Connection basis source entry next := by
  rcases connected with shift | restore | test
  · obtain ⟨site, _, _, rfl⟩ := shift
    exact boundary_unconnected basis source deterministic _ next
  · obtain ⟨site, _, rfl⟩ := restore
    exact boundary_unconnected basis source deterministic site.val next
  · obtain ⟨_, site, _, remainder, _, _, _, _, _, _, _, rfl⟩ := test
    exact restoreInput_unconnected basis source site remainder next

/-- Finite port identification supplies the complete compressed execution table. -/
def wiring (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source) :
    PortNetwork.Wiring (rawTable basis source) :=
  PortNetwork.Wiring.ofRelation (rawTable basis source) (Connection basis source)
    (connection_functional basis source deterministic)
    (connection_backward basis source compatible)
    (connection_terminal basis source deterministic)
    (connection_source_free basis source deterministic)
    (connection_target_free basis source)

def size (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source) : ℕ :=
  PortNetwork.size (wiring basis source deterministic compatible)

/-- Every edge is an existing radix edge on the same two physical counters. -/
def table (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source) :
    Table 2 (size basis source deterministic compatible) (rawEdges basis source) :=
  PortNetwork.table (wiring basis source deterministic compatible)

theorem deterministic (basis : PrimeCode.Basis n) (source : Table n q e)
    (source_deterministic : Deterministic source) (compatible : TargetCompatible source) :
    Deterministic (table basis source source_deterministic compatible) :=
  PortNetwork.deterministic _ (raw_deterministic basis source)

theorem targetCompatible (basis : PrimeCode.Basis n) (source : Table n q e)
    (source_deterministic : Deterministic source) (compatible : TargetCompatible source) :
    TargetCompatible (table basis source source_deterministic compatible) :=
  PortNetwork.targetCompatible _ (raw_targetCompatible basis source)

/-- A retained source boundary is never removed by the static port matching. -/
theorem boundary_link_none (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source) (position : Fin q) :
    (wiring basis source deterministic compatible).link (boundary basis source position) = none := by
  change PortNetwork.relationLink (Connection basis source) (boundary basis source position) = none
  exact (PortNetwork.relationLink_none_iff (Connection basis source) _).mpr
    (boundary_unconnected basis source deterministic position)

/-- The complete natural source configuration occupies two integer counters. -/
def encode (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source)
    (state : Counter.Configuration n q) : State 2 (size basis source deterministic compatible) :=
  (PortNetwork.control (wiring basis source deterministic compatible)
    (boundary basis source state.pc), ![(basis.encode state.counters : ℤ), 0])

/-- No information about the finite address or the complete source register vector is lost. -/
theorem encode_injective (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source) :
    Function.Injective (encode basis source deterministic compatible) := by
  intro first second same
  have controls := congrArg Prod.fst same
  have raw_controls := PortNetwork.control_unlinked_injective
    (wiring basis source deterministic compatible)
    (boundary_link_none basis source deterministic compatible first.pc)
    (boundary_link_none basis source deterministic compatible second.pc) controls
  have addresses := boundary_injective basis source raw_controls
  have integer_codes := congrArg
    (fun state : State 2 (size basis source deterministic compatible) => state.2 0) same
  have codes : basis.encode first.counters = basis.encode second.counters := by
    apply Int.natCast_inj.mp
    simpa only [encode, Matrix.cons_val_zero] using integer_codes
  have registers := basis.encode_injective codes
  exact congrArg₂ Counter.Configuration.mk addresses registers

/-- A connection is a control-position equality, with no intermediate transition. -/
theorem connection_controls (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source)
    {exit entry : Fin (rawSize basis source)} (connected : Connection basis source exit entry) :
    PortNetwork.control (wiring basis source deterministic compatible) exit =
      PortNetwork.control (wiring basis source deterministic compatible) entry := by
  apply PortNetwork.interface
  change PortNetwork.relationLink (Connection basis source) exit = some entry
  exact (PortNetwork.relationLink_some_iff (Connection basis source)
    (connection_functional basis source deterministic) exit entry).mpr connected

/-- A source address without outgoing edges is represented by an isolated raw vertex. -/
theorem raw_no_outgoing_halt (basis : PrimeCode.Basis n) (source : Table n q e)
    (position : Fin q) (halted : ¬ HasSource source position) (index : Fin (rawEdges basis source)) :
    (rawTable basis source index).source ≠ boundary basis source position := by
  intro same
  obtain ⟨⟨block, index⟩, rfl⟩ := (rawArcEquiv basis source).surjective index
  simp only [rawTable_arc, rawEdge, Glue.mapEdge, boundary, dite_eq_right halted] at same
  exact haltNode_ne_moduleNode basis source ⟨position, halted⟩ _ _ same.symm

/-- Static halts retain their absence of outgoing edges in the actual compressed table. -/
theorem no_outgoing_boundary (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source)
    (position : Fin q) (halted : ¬ HasSource source position) :
    ¬ ∃ index, (table basis source deterministic compatible index).source =
      PortNetwork.control (wiring basis source deterministic compatible)
        (boundary basis source position) := by
  rintro ⟨index, same⟩
  have raw_controls := PortNetwork.control_unlinked_injective
    (wiring basis source deterministic compatible)
    ((wiring basis source deterministic compatible).source_free index)
    (boundary_link_none basis source deterministic compatible position) same
  exact raw_no_outgoing_halt basis source position halted index raw_controls

/-- At a statically halted source address the compressed graph stops for every source value. -/
theorem step_encode_none_of_no_source (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source)
    (state : Counter.Configuration n q) (halted : ¬ HasSource source state.pc) :
    step (table basis source deterministic compatible)
      (encode basis source deterministic compatible state) = none := by
  rw [step_none_iff]
  rintro ⟨index, enabled⟩
  exact no_outgoing_boundary basis source deterministic compatible state.pc halted ⟨index, enabled.1⟩

def siteOfEdge (source : Table n q e) (edge : Fin e) : SourceSite source :=
  ⟨(source edge).source, edge, rfl⟩

def restoreOfTest (source : Table n q e) (edge : Fin e) (register : Fin n) (flag : Bool)
    (test : (source edge).action = .test register flag) : RestoreSite source :=
  ⟨(source edge).target, edge, rfl, register, flag, test⟩

theorem sourceEdge_of_shift (source : Table n q e) (deterministic : Deterministic source)
    (edge : Fin e) (register : Fin n) (amount : ℤ)
    (shift : (source edge).action = .shift register amount) :
    sourceEdge source (siteOfEdge source edge) = edge := by
  apply Eq.symm
  exact shift_owner_unique source (fun index => (source index).source) deterministic shift
    (sourceEdge_spec source (siteOfEdge source edge)).symm

theorem sourceRegister_of_shift (source : Table n q e) (deterministic : Deterministic source)
    (edge : Fin e) (register : Fin n) (amount : ℤ)
    (shift : (source edge).action = .shift register amount) :
    moduleRegister source (.inl (siteOfEdge source edge)) = register := by
  simp only [moduleRegister, sourceEdge_of_shift source deterministic edge register amount shift,
    shift, actionRegister]

theorem sourceForm_of_test (source : Table n q e) (deterministic : Deterministic source)
    (edge : Fin e) (register : Fin n) (flag : Bool)
    (test : (source edge).action = .test register flag) :
    ∃ chosen, (source (sourceEdge source (siteOfEdge source edge))).action = .test register chosen :=
  test_owner_form source (fun index => (source index).source) deterministic test
    (sourceEdge_spec source (siteOfEdge source edge)).symm

theorem sourceRegister_of_test (source : Table n q e) (deterministic : Deterministic source)
    (edge : Fin e) (register : Fin n) (flag : Bool)
    (test : (source edge).action = .test register flag) :
    moduleRegister source (.inl (siteOfEdge source edge)) = register := by
  obtain ⟨chosen, form⟩ := sourceForm_of_test source deterministic edge register flag test
  simp only [moduleRegister, form, actionRegister]

theorem restoreRegister_of_test (source : Table n q e) (compatible : TargetCompatible source)
    (edge : Fin e) (register : Fin n) (flag : Bool)
    (test : (source edge).action = .test register flag) :
    moduleRegister source (.inr (restoreOfTest source edge register flag test)) = register := by
  obtain ⟨chosen, form⟩ := test_owner_form source (fun index => (source index).target) compatible test
    (restoreEdge_spec source (restoreOfTest source edge register flag test)).1.symm
  simp only [moduleRegister, form, actionRegister]

/-- The end of a shift is joined directly to its statically specified target. -/
theorem shift_connected (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (edge : Fin e) (register : Fin n) (amount : ℤ)
    (shift : (source edge).action = .shift register amount) :
    Connection basis source (sourceShiftOutput basis source (siteOfEdge source edge))
      (boundary basis source (source edge).target) := by
  refine Or.inl ⟨siteOfEdge source edge, ?_, rfl, ?_⟩
  · simp only [sourceEdge_of_shift source deterministic edge register amount shift, shift, Action.IsShift]
  · rw [sourceEdge_of_shift source deterministic edge register amount shift]

/-- Restoration returns directly to the target execution boundary. -/
theorem restore_connected (basis : PrimeCode.Basis n) (source : Table n q e)
    (site : RestoreSite source) :
    Connection basis source (restoreOutput basis source site) (boundary basis source site.val) :=
  Or.inr (Or.inl ⟨site, rfl, rfl⟩)

/-- A selected test edge identifies exactly the actually reached remainder ports. -/
theorem test_connected (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source)
    (edge : Fin e) (register : Fin n) (flag : Bool)
    (test : (source edge).action = .test register flag)
    (remainder : Fin (modulus basis source (.inl (siteOfEdge source edge))))
    (restored : Fin (modulus basis source (.inr (restoreOfTest source edge register flag test))))
    (same : remainder.val = restored.val) (selected : decide (remainder.val ≠ 0) = flag) :
    Connection basis source
      (moduleNode basis source (.inl (siteOfEdge source edge)) (Radix.finish _ remainder))
      (restoreInput basis source (restoreOfTest source edge register flag test) restored) := by
  refine Or.inr (Or.inr ⟨siteOfEdge source edge, restoreOfTest source edge register flag test,
    remainder, restored, edge, rfl, rfl, ?_, ?_, same, rfl, rfl⟩)
  · rw [testSelected_iff, sourceRegister_of_test source deterministic edge register flag test, selected]
    exact test
  · exact (sourceRegister_of_test source deterministic edge register flag test).trans
      (restoreRegister_of_test source compatible edge register flag test).symm

theorem component_step_map (basis : PrimeCode.Basis n) (source : Table n q e)
    (block : Module source)
    {first last : State 2 (Radix.size (modulus basis source block))}
    (transition : step (componentTable basis source block) first = some last) :
    step (rawTable basis source) (Glue.mapState (moduleNode basis source block) first) =
      some (Glue.mapState (moduleNode basis source block) last) := by
  exact Glue.step_map_live (componentTable basis source block) (rawTable basis source)
    (moduleNode basis source block) (fun index => rawArcEquiv basis source ⟨block, index⟩)
    (fun index => by rw [rawTable_arc]; rfl)
    (component_deterministic basis source block) (raw_deterministic basis source) transition

theorem component_reaches_map (basis : PrimeCode.Basis n) (source : Table n q e)
    (block : Module source)
    {first last : State 2 (Radix.size (modulus basis source block))}
    (run : StateTransition.Reaches (step (componentTable basis source block)) first last) :
    StateTransition.Reaches (step (rawTable basis source))
      (Glue.mapState (moduleNode basis source block) first)
      (Glue.mapState (moduleNode basis source block) last) := by
  exact Glue.reaches_map_live (componentTable basis source block) (rawTable basis source)
    (moduleNode basis source block) (fun index => rawArcEquiv basis source ⟨block, index⟩)
    (fun index => by rw [rawTable_arc]; rfl)
    (component_deterministic basis source block) (raw_deterministic basis source) run

theorem component_reaches1_map (basis : PrimeCode.Basis n) (source : Table n q e)
    (block : Module source)
    {first last : State 2 (Radix.size (modulus basis source block))}
    (run : StateTransition.Reaches₁ (step (componentTable basis source block)) first last) :
    StateTransition.Reaches₁ (step (rawTable basis source))
      (Glue.mapState (moduleNode basis source block) first)
      (Glue.mapState (moduleNode basis source block) last) := by
  induction run with
  | single transition => exact Relation.TransGen.single (component_step_map basis source block transition)
  | tail _ transition previous => exact previous.tail (component_step_map basis source block transition)

private theorem positive_of_control_ne {d f : ℕ} (table : Table 2 d f)
    {first last : State 2 d} (run : StateTransition.Reaches (step table) first last)
    (different : first.1 ≠ last.1) : StateTransition.Reaches₁ (step table) first last := by
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp run with same | positive
  · exact False.elim (different (congrArg Prod.fst same.symm))
  · exact positive

/-- The forward radix module has a positive execution to its actual quotient and remainder. -/
theorem forward_query_local_positive (basis : PrimeCode.Basis n) (source : Table n q e)
    (site : SourceSite source) (forward : reversed source (.inl site) = false) (value : ℕ) :
    let p := modulus basis source (.inl site)
    StateTransition.Reaches₁ (step (componentTable basis source (.inl site)))
      (Radix.point p (Radix.entry p) value 0)
      (Radix.point p (Radix.finish p (Counter.DivMod.residue p value)) (value / p : ℕ) 0) := by
  dsimp only
  apply positive_of_control_ne
  · simpa only [componentTable, forward, Bool.false_eq_true, reduceIte] using
      Radix.reaches_result (modulus basis source (.inl site)) value
  · exact radix_entry_ne_finish _ _

/-- The reversed radix module packs a zero remainder by actual positive execution. -/
theorem source_multiply_local_positive (basis : PrimeCode.Basis n) (source : Table n q e)
    (site : SourceSite source) (backwards : reversed source (.inl site) = true) (value : ℕ) :
    let p := modulus basis source (.inl site)
    StateTransition.Reaches₁ (step (componentTable basis source (.inl site)))
      (Radix.point p (Radix.finish p 0) value 0)
      (Radix.point p (Radix.entry p) (p * value : ℕ) 0) := by
  dsimp only
  apply positive_of_control_ne
  · simpa only [componentTable, backwards, reduceIte, Fin.val_zero, Nat.add_zero] using
      Radix.reverse_pack (modulus basis source (.inl site)) value 0
  · exact (radix_entry_ne_finish _ 0).symm

/-- The restoration module positively packs its quotient and reached remainder. -/
theorem restore_pack_local_positive (basis : PrimeCode.Basis n) (source : Table n q e)
    (site : RestoreSite source) (remainder : Fin (modulus basis source (.inr site))) (quotient : ℕ) :
    let p := modulus basis source (.inr site)
    StateTransition.Reaches₁ (step (componentTable basis source (.inr site)))
      (Radix.point p (Radix.finish p remainder) quotient 0)
      (Radix.point p (Radix.entry p) (p * quotient + remainder.val : ℕ) 0) := by
  dsimp only
  apply positive_of_control_ne
  · exact Radix.reverse_pack _ quotient remainder
  · exact (radix_entry_ne_finish _ remainder).symm

/-- A forward source module actually reaches its remainder port with the quotient. -/
theorem forward_query_positive (basis : PrimeCode.Basis n) (source : Table n q e)
    (site : SourceSite source) (forward : reversed source (.inl site) = false) (value : ℕ) :
    StateTransition.Reaches₁ (step (rawTable basis source))
      (sourceInput basis source site, ![(value : ℤ), 0])
      (moduleNode basis source (.inl site)
        (Radix.finish _ (Counter.DivMod.residue (modulus basis source (.inl site)) value)),
        ![((value / modulus basis source (.inl site) : ℕ) : ℤ), 0]) := by
  simpa only [Glue.mapState, Radix.point, sourceInput, sourceInputPosition, forward,
    Bool.false_eq_true, reduceIte] using component_reaches1_map basis source (.inl site)
      (forward_query_local_positive basis source site forward value)

/-- A reversed source module multiplies by its fixed prime through the same radix graph. -/
theorem source_multiply_positive (basis : PrimeCode.Basis n) (source : Table n q e)
    (site : SourceSite source) (backwards : reversed source (.inl site) = true) (value : ℕ) :
    StateTransition.Reaches₁ (step (rawTable basis source))
      (sourceInput basis source site, ![(value : ℤ), 0])
      (sourceShiftOutput basis source site,
        ![((modulus basis source (.inl site) * value : ℕ) : ℤ), 0]) := by
  simpa only [Glue.mapState, Radix.point, sourceInput, sourceInputPosition, sourceShiftOutput,
    backwards, reduceIte] using component_reaches1_map basis source (.inl site)
      (source_multiply_local_positive basis source site backwards value)

/-- A restoration module packs its actual quotient and reached remainder. -/
theorem restore_pack_positive (basis : PrimeCode.Basis n) (source : Table n q e)
    (site : RestoreSite source) (remainder : Fin (modulus basis source (.inr site))) (quotient : ℕ) :
    StateTransition.Reaches₁ (step (rawTable basis source))
      (restoreInput basis source site remainder, ![(quotient : ℤ), 0])
      (restoreOutput basis source site,
        ![((modulus basis source (.inr site) * quotient + remainder.val : ℕ) : ℤ), 0]) := by
  simpa only [Glue.mapState, Radix.point, restoreInput, restoreOutput] using
    component_reaches1_map basis source (.inr site)
      (restore_pack_local_positive basis source site remainder quotient)

/-- Exactly the retained finite source execution boundaries. -/
def Boundary (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source)
    (state : State 2 (size basis source deterministic compatible)) : Prop :=
  ∃ position : Fin q, state.1 = PortNetwork.control (wiring basis source deterministic compatible)
    (boundary basis source position)

/-- State relocation changes only the finite control address. -/
def MappedState (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source) (block : Module source)
    (state : State 2 (Radix.size (modulus basis source block))) :
    State 2 (size basis source deterministic compatible) :=
  Glue.mapState (PortNetwork.control (wiring basis source deterministic compatible))
    (Glue.mapState (moduleNode basis source block) state)

/-- The actual compiled step with an observation on its source, not a new execution rule. -/
def InternalStep (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source)
    (first last : State 2 (size basis source deterministic compatible)) : Prop :=
  step (table basis source deterministic compatible) first = some last ∧
    ¬ Boundary basis source deterministic compatible first

abbrev InternalReaches (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source) :=
  Relation.ReflTransGen (InternalStep basis source deterministic compatible)

/-- A positive compiled run, with no earlier return to a source execution boundary. -/
def FirstReturn (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source)
    (first last : State 2 (size basis source deterministic compatible)) : Prop :=
  Boundary basis source deterministic compatible first ∧
  Boundary basis source deterministic compatible last ∧
  ∃ next, step (table basis source deterministic compatible) first = some next ∧
    InternalReaches basis source deterministic compatible next last

theorem boundary_encode (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source)
    (state : Counter.Configuration n q) :
    Boundary basis source deterministic compatible (encode basis source deterministic compatible state) :=
  ⟨state.pc, rfl⟩

/-- A local step is executed by precisely the retained compressed table. -/
theorem mapped_step (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source) (block : Module source)
    {first last : State 2 (Radix.size (modulus basis source block))}
    (transition : step (componentTable basis source block) first = some last) :
    step (table basis source deterministic compatible)
      (MappedState basis source deterministic compatible block first) =
      some (MappedState basis source deterministic compatible block last) :=
  PortNetwork.step_map_live (wiring basis source deterministic compatible)
    (raw_deterministic basis source) (component_step_map basis source block transition)

/-- A local state's control is retained whenever it is the source of an actual edge. -/
theorem module_source_unlinked (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source) (block : Module source)
    {first last : State 2 (Radix.size (modulus basis source block))}
    (transition : step (componentTable basis source block) first = some last) :
    (wiring basis source deterministic compatible).link (moduleNode basis source block first.1) = none := by
  obtain ⟨index, enabled, _⟩ := (step_iff (rawTable basis source) (raw_deterministic basis source)).mp
    (component_step_map basis source block transition)
  have source_eq : (rawTable basis source index).source = moduleNode basis source block first.1 := enabled.1
  rw [← source_eq]
  exact (wiring basis source deterministic compatible).source_free index

/-- No step of a source module targets its own input port. -/
theorem source_target_ne_input (basis : PrimeCode.Basis n) (source : Table n q e)
    (site : SourceSite source)
    {first last : State 2 (Radix.size (modulus basis source (.inl site)))}
    (transition : step (componentTable basis source (.inl site)) first = some last) :
    last.1 ≠ sourceInputPosition basis source site := by
  obtain ⟨index, _, result⟩ := (step_iff _ (component_deterministic basis source (.inl site))).mp transition
  intro equal
  exact component_no_incoming_sourceInput basis source site index
    ((congrArg Prod.fst result).trans equal)

private theorem source_internal_step (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source) (site : SourceSite source)
    {first last : State 2 (Radix.size (modulus basis source (.inl site)))}
    (interior : first.1 ≠ sourceInputPosition basis source site)
    (transition : step (componentTable basis source (.inl site)) first = some last) :
    InternalStep basis source deterministic compatible
      (MappedState basis source deterministic compatible (.inl site) first)
      (MappedState basis source deterministic compatible (.inl site) last) := by
  refine ⟨mapped_step basis source deterministic compatible (.inl site) transition, ?_⟩
  rintro ⟨position, equal⟩
  have raw_equal := PortNetwork.control_unlinked_injective (wiring basis source deterministic compatible)
    (module_source_unlinked basis source deterministic compatible (.inl site) transition)
    (boundary_link_none basis source deterministic compatible position) equal
  exact sourceNode_ne_boundary basis source site first.1 interior position raw_equal

/-- A source-module run beginning past its input has only interior compiled sources. -/
theorem source_internal_reaches (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source) (site : SourceSite source)
    {first last : State 2 (Radix.size (modulus basis source (.inl site)))}
    (run : StateTransition.Reaches (step (componentTable basis source (.inl site))) first last)
    (interior : first.1 ≠ sourceInputPosition basis source site) :
    InternalReaches basis source deterministic compatible
      (MappedState basis source deterministic compatible (.inl site) first)
      (MappedState basis source deterministic compatible (.inl site) last) := by
  have lifted : InternalReaches basis source deterministic compatible
      (MappedState basis source deterministic compatible (.inl site) first)
      (MappedState basis source deterministic compatible (.inl site) last) ∧
      last.1 ≠ sourceInputPosition basis source site := by
    induction run with
    | refl => exact ⟨Relation.ReflTransGen.refl, interior⟩
    | tail _ transition previous =>
        exact ⟨previous.1.tail (source_internal_step basis source deterministic compatible site previous.2 transition),
          source_target_ne_input basis source site transition⟩
  exact lifted.1

/-- After its first actual step, every positive source-module run is interior
until its terminal port. No extra transition is inserted at departure. -/
theorem source_departure (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source) (site : SourceSite source)
    {first last : State 2 (Radix.size (modulus basis source (.inl site)))}
    (run : StateTransition.Reaches₁ (step (componentTable basis source (.inl site))) first last) :
    ∃ next, step (table basis source deterministic compatible)
      (MappedState basis source deterministic compatible (.inl site) first) = some next ∧
      InternalReaches basis source deterministic compatible next
        (MappedState basis source deterministic compatible (.inl site) last) := by
  obtain ⟨middle, initial, rest⟩ := Relation.TransGen.head'_iff.mp run
  exact ⟨MappedState basis source deterministic compatible (.inl site) middle,
    mapped_step basis source deterministic compatible (.inl site) initial,
    source_internal_reaches basis source deterministic compatible site rest
      (source_target_ne_input basis source site initial)⟩

private theorem restoreNode_ne_boundary (basis : PrimeCode.Basis n) (source : Table n q e)
    (site : RestoreSite source) (position : Fin (Radix.size (modulus basis source (.inr site))))
    (target : Fin q) : moduleNode basis source (.inr site) position ≠ boundary basis source target := by
  intro same
  by_cases active : HasSource source target
  · simp only [boundary, dite_eq_left active, sourceInput] at same
    cases moduleNode_module basis source same
  · simp only [boundary, dite_eq_right active] at same
    exact haltNode_ne_moduleNode basis source ⟨target, active⟩ _ _ same.symm

private theorem restore_internal_step (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source) (site : RestoreSite source)
    {first last : State 2 (Radix.size (modulus basis source (.inr site)))}
    (transition : step (componentTable basis source (.inr site)) first = some last) :
    InternalStep basis source deterministic compatible
      (MappedState basis source deterministic compatible (.inr site) first)
      (MappedState basis source deterministic compatible (.inr site) last) := by
  refine ⟨mapped_step basis source deterministic compatible (.inr site) transition, ?_⟩
  rintro ⟨position, equal⟩
  have raw_equal := PortNetwork.control_unlinked_injective (wiring basis source deterministic compatible)
    (module_source_unlinked basis source deterministic compatible (.inr site) transition)
    (boundary_link_none basis source deterministic compatible position) equal
  exact restoreNode_ne_boundary basis source site first.1 position raw_equal

/-- Restoration has no source boundary until its terminal output is identified with one. -/
theorem restore_internal_reaches (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source) (site : RestoreSite source)
    {first last : State 2 (Radix.size (modulus basis source (.inr site)))}
    (run : StateTransition.Reaches (step (componentTable basis source (.inr site))) first last) :
    InternalReaches basis source deterministic compatible
      (MappedState basis source deterministic compatible (.inr site) first)
      (MappedState basis source deterministic compatible (.inr site) last) := by
  exact Relation.ReflTransGen.lift (MappedState basis source deterministic compatible (.inr site))
    (fun _ _ transition => restore_internal_step basis source deterministic compatible site transition) _ _ run

theorem increment_firstReturn (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source)
    (before : Counter.Configuration n q) (edge : Fin e) (register : Fin n)
    (at_source : (source edge).source = before.pc)
    (instruction : (source edge).action = .shift register 1) :
    FirstReturn basis source deterministic compatible
      (encode basis source deterministic compatible before)
      (encode basis source deterministic compatible
        ⟨(source edge).target, Function.update before.counters register (before.counters register + 1)⟩) := by
  let site := siteOfEdge source edge
  let p := modulus basis source (.inl site)
  let value := basis.encode before.counters
  have backwards : reversed source (.inl site) = true := by
    simp only [site, reversed,
      sourceEdge_of_shift source deterministic edge register 1 instruction, instruction,
      decide_true]
  have prime : p = basis.prime register := by
    exact congrArg basis.prime
      (sourceRegister_of_shift source deterministic edge register 1 instruction)
  have initial : boundary basis source before.pc = sourceInput basis source site := by
    rw [← at_source]
    exact boundary_source basis source site
  have input : moduleNode basis source (.inl site) (Radix.finish p 0) =
      sourceInput basis source site := by
    simp [sourceInput, sourceInputPosition, backwards, p]
  have output : moduleNode basis source (.inl site) (Radix.entry p) =
      sourceShiftOutput basis source site := by
    simp [sourceShiftOutput, backwards, p]
  have final := connection_controls basis source deterministic compatible
    (shift_connected basis source deterministic edge register 1 instruction)
  have code : p * value =
      basis.encode (Function.update before.counters register (before.counters register + 1)) := by
    rw [prime]
    exact (basis.encode_increment before.counters register).symm
  have departure := source_departure basis source deterministic compatible site
    (source_multiply_local_positive basis source site backwards value)
  simp only [MappedState, Glue.mapState, Radix.point] at departure
  rw [input, ← initial, output, final, code] at departure
  exact ⟨boundary_encode basis source deterministic compatible before,
    boundary_encode basis source deterministic compatible _, departure⟩

theorem decrement_firstReturn (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source)
    (before : Counter.Configuration n q) (edge : Fin e) (register : Fin n)
    (at_source : (source edge).source = before.pc)
    (instruction : (source edge).action = .shift register (-1))
    (positive : before.counters register ≠ 0) :
    FirstReturn basis source deterministic compatible
      (encode basis source deterministic compatible before)
      (encode basis source deterministic compatible
        ⟨(source edge).target, Function.update before.counters register (before.counters register - 1)⟩) := by
  let site := siteOfEdge source edge
  let p := modulus basis source (.inl site)
  let value := basis.encode before.counters
  have forward : reversed source (.inl site) = false := by
    dsimp only [site, reversed]
    rw [sourceEdge_of_shift source deterministic edge register (-1) instruction, instruction]
    change decide ((-1 : ℤ) = 1) = false
    decide
  have prime : p = basis.prime register := by
    dsimp only [p, modulus, site]
    rw [sourceRegister_of_shift source deterministic edge register (-1) instruction]
  have divisible : p ∣ value := by
    rw [prime]
    exact (basis.prime_dvd_encode_iff before.counters register).mpr positive
  have remainder_zero : Counter.DivMod.residue p value = 0 := by
    apply Fin.ext
    change value % p = 0
    exact Nat.mod_eq_zero_of_dvd divisible
  have initial : sourceInput basis source site = boundary basis source before.pc := by
    rw [← boundary_source basis source site]
    exact congrArg (boundary basis source) at_source
  have input : moduleNode basis source (.inl site) (Radix.entry p) =
      sourceInput basis source site := by
    simp [sourceInput, sourceInputPosition, forward, p]
  have output : moduleNode basis source (.inl site) (Radix.finish p 0) =
      sourceShiftOutput basis source site := by
    simp [sourceShiftOutput, forward, p]
  have final := connection_controls basis source deterministic compatible
    (shift_connected basis source deterministic edge register (-1) instruction)
  have code : basis.encode (Function.update before.counters register (before.counters register - 1)) =
      value / p := by
    rw [prime]
    exact basis.encode_decrement before.counters register positive
  have local_run := forward_query_local_positive basis source site forward value
  change StateTransition.Reaches₁ (step (componentTable basis source (.inl site)))
    (Radix.point p (Radix.entry p) value 0)
    (Radix.point p (Radix.finish p (Counter.DivMod.residue p value)) (value / p : ℕ) 0) at local_run
  rw [remainder_zero] at local_run
  have departure := source_departure basis source deterministic compatible site local_run
  simp only [MappedState, Glue.mapState, Radix.point] at departure
  rw [input, initial, output, final, ← code] at departure
  exact ⟨boundary_encode basis source deterministic compatible before,
    boundary_encode basis source deterministic compatible _, departure⟩

theorem test_firstReturn (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source)
    (before : Counter.Configuration n q) (edge : Fin e) (register : Fin n) (flag : Bool)
    (at_source : (source edge).source = before.pc)
    (test : (source edge).action = .test register flag)
    (enabled : (source edge).action.enabled (fun index => (before.counters index : ℤ))) :
    FirstReturn basis source deterministic compatible
      (encode basis source deterministic compatible before)
      (encode basis source deterministic compatible ⟨(source edge).target, before.counters⟩) := by
  let first := siteOfEdge source edge
  let last := restoreOfTest source edge register flag test
  let value := basis.encode before.counters
  let p := modulus basis source (.inl first)
  let remainder := Counter.DivMod.residue p value
  have first_register : moduleRegister source (.inl first) = register :=
    sourceRegister_of_test source deterministic edge register flag test
  have last_register : moduleRegister source (.inr last) = register :=
    restoreRegister_of_test source compatible edge register flag test
  have same_modulus : p = modulus basis source (.inr last) :=
    congrArg basis.prime (first_register.trans last_register.symm)
  let restored : Fin (modulus basis source (.inr last)) :=
    ⟨remainder.val, by rw [← same_modulus]; exact remainder.isLt⟩
  have forward : reversed source (.inl first) = false := by
    obtain ⟨chosen, form⟩ := sourceForm_of_test source deterministic edge register flag test
    simp only [reversed, first, form]
  have zero_flag : decide (before.counters register = 0) = flag := by
    cases flag <;> simp_all [Action.enabled]
  have selected : decide (remainder.val ≠ 0) = flag := by
    change decide (value % p ≠ 0) = flag
    have prime : p = basis.prime register := congrArg basis.prime first_register
    rw [prime, residue_zero_flag, zero_flag]
  obtain ⟨next, initial_step, inside⟩ := source_departure basis source deterministic compatible first
    (forward_query_local_positive basis source first forward value)
  have restore := restore_internal_reaches basis source deterministic compatible last
    (restore_pack_local_positive basis source last restored (value / p)).to_reflTransGen
  simp only [MappedState, Glue.mapState, Radix.point] at initial_step inside restore
  have ports := connection_controls basis source deterministic compatible
    (test_connected basis source deterministic compatible edge register flag test remainder restored rfl selected)
  rw [ports] at inside
  change InternalReaches basis source deterministic compatible
    (PortNetwork.control (wiring basis source deterministic compatible)
      (restoreInput basis source last restored), ![((value / p : ℕ) : ℤ), 0])
    (PortNetwork.control (wiring basis source deterministic compatible)
      (restoreOutput basis source last),
      ![((modulus basis source (.inr last) * (value / p) + restored.val : ℕ) : ℤ), 0]) at restore
  have final_port := connection_controls basis source deterministic compatible (restore_connected basis source last)
  rw [final_port] at restore
  have arithmetic : modulus basis source (.inr last) * (value / p) + restored.val = value := by
    change modulus basis source (.inr last) * (value / p) + remainder.val = value
    rw [← same_modulus]
    change p * (value / p) + value % p = value
    have division := Nat.mod_add_div value p
    omega
  rw [arithmetic] at restore
  have initial : boundary basis source before.pc = sourceInput basis source first := by
    rw [← at_source]
    exact boundary_source basis source first
  have input : moduleNode basis source (.inl first) (Radix.entry p) =
      sourceInput basis source first := by
    simp only [sourceInput, sourceInputPosition, forward, Bool.false_eq_true, reduceIte]
    rfl
  rw [input, ← initial] at initial_step
  exact ⟨boundary_encode basis source deterministic compatible before,
    boundary_encode basis source deterministic compatible ⟨(source edge).target, before.counters⟩,
    next, initial_step, inside.trans restore⟩

/-- Natural configurations are viewed inside the integer source state space. -/
def naturalState (state : Counter.Configuration n q) : State n q :=
  (state.pc, fun index => (state.counters index : ℤ))

theorem naturalState_injective : Function.Injective (@naturalState n q) := by
  intro first second same
  apply congrArg₂ Counter.Configuration.mk
  · exact congrArg Prod.fst same
  · funext index
    exact Int.natCast_inj.mp (congrArg (fun state : State n q => state.2 index) same)

private theorem naturalState_shift (before : Counter.Configuration n q) (target : Fin q)
    (register : Fin n) (amount : ℤ) (value : ℕ)
    (arithmetic : (before.counters register : ℤ) + amount = value) :
    (target, Action.apply (.shift register amount) (naturalState before).2) =
      naturalState ⟨target, Function.update before.counters register value⟩ := by
  apply Prod.ext
  · rfl
  · funext index
    by_cases selected : index = register
    · subst index
      simpa only [naturalState, Action.apply, Function.update_self] using arithmetic
    · simp [naturalState, Action.apply, selected]

/-- Compression preserves a complete live source transition on the natural domain. -/
theorem step_firstReturn (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source)
    (unit : ∀ edge, Action.UnitShift (source edge).action)
    {before after : Counter.Configuration n q}
    (transition : step source (naturalState before) = some (naturalState after)) :
    FirstReturn basis source deterministic compatible
      (encode basis source deterministic compatible before)
      (encode basis source deterministic compatible after) := by
  obtain ⟨edge, enabled, result⟩ := (step_iff source deterministic).mp transition
  have at_source : (source edge).source = before.pc := enabled.1
  cases operation : (source edge).action with
  | shift register amount =>
      have elementary : amount = 1 ∨ amount = -1 := by
        simpa only [operation, Action.UnitShift] using unit edge
      simp only [Edge.execute, operation] at result
      rcases elementary with forward | backward
      · subst amount
        have shape :
            ⟨(source edge).target,
              Function.update before.counters register (before.counters register + 1)⟩ = after := by
          apply naturalState_injective
          exact (naturalState_shift before (source edge).target register 1
            (before.counters register + 1) (by simp)).symm.trans result
        subst after
        exact increment_firstReturn basis source deterministic compatible before edge register at_source operation
      · subst amount
        have selected : (before.counters register : ℤ) + (-1) = after.counters register := by
          simpa only [Action.apply, naturalState, Function.update_self] using
            congrArg (fun state : State n q => state.2 register) result
        have positive : before.counters register ≠ 0 := by
          have nonnegative := Int.natCast_nonneg (after.counters register)
          omega
        have arithmetic : (before.counters register : ℤ) + (-1) =
            (before.counters register - 1 : ℕ) := by omega
        have shape :
            ⟨(source edge).target,
              Function.update before.counters register (before.counters register - 1)⟩ = after := by
          apply naturalState_injective
          exact (naturalState_shift before (source edge).target register (-1)
            (before.counters register - 1) arithmetic).symm.trans result
        subst after
        exact decrement_firstReturn basis source deterministic compatible before edge register at_source operation positive
  | test register flag =>
      simp only [Edge.execute, operation, Action.apply] at result
      have shape : ⟨(source edge).target, before.counters⟩ = after := by
        apply naturalState_injective
        exact result
      subst after
      exact test_firstReturn basis source deterministic compatible before edge register flag
        at_source operation enabled.2

/-- The actual first-return run is positive when its observation is forgotten. -/
theorem FirstReturn.reaches {basis : PrimeCode.Basis n} {source : Table n q e}
    {deterministic : Deterministic source} {compatible : TargetCompatible source}
    {first last : State 2 (size basis source deterministic compatible)}
    (run : FirstReturn basis source deterministic compatible first last) :
    StateTransition.Reaches₁ (step (table basis source deterministic compatible)) first last := by
  obtain ⟨_, _, next, initial, interior⟩ := run
  exact Relation.TransGen.head' initial
    (Relation.ReflTransGen.mono (fun _ _ edge => edge.1) _ _ interior)

/-- Ordinary execution is derived from the same exact first return. -/
theorem step_reaches (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source)
    (unit : ∀ edge, Action.UnitShift (source edge).action)
    {before after : Counter.Configuration n q}
    (transition : step source (naturalState before) = some (naturalState after)) :
    StateTransition.Reaches₁ (step (table basis source deterministic compatible))
      (encode basis source deterministic compatible before)
      (encode basis source deterministic compatible after) :=
  (step_firstReturn basis source deterministic compatible unit transition).reaches

def toNatural (state : State n q) : Counter.Configuration n q :=
  ⟨state.1, fun index => (state.2 index).toNat⟩

theorem naturalState_toNatural (state : State n q) (nonnegative : ∀ index, 0 ≤ state.2 index) :
    naturalState (toNatural state) = state := by
  apply Prod.ext
  · rfl
  · funext index
    exact Int.toNat_of_nonneg (nonnegative index)

/-- Every live step whose endpoints lie on the natural lattice has an actual positive compression. -/
theorem integer_step_reaches (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source)
    (unit : ∀ edge, Action.UnitShift (source edge).action)
    {first last : State n q} (transition : step source first = some last)
    (first_natural : ∀ index, 0 ≤ first.2 index) (last_natural : ∀ index, 0 ≤ last.2 index) :
    StateTransition.Reaches₁ (step (table basis source deterministic compatible))
      (encode basis source deterministic compatible (toNatural first))
      (encode basis source deterministic compatible (toNatural last)) := by
  apply step_reaches basis source deterministic compatible unit
  rw [naturalState_toNatural first first_natural, naturalState_toNatural last last_natural]
  exact transition

/-- A source invariant covers every intermediate step, not only the two encoded endpoints. -/
theorem integer_reaches1 (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source)
    (unit : ∀ edge, Action.UnitShift (source edge).action)
    {first last : State n q} (run : StateTransition.Reaches₁ (step source) first last)
    (natural : ∀ state, StateTransition.Reaches (step source) first state → ∀ index, 0 ≤ state.2 index) :
    StateTransition.Reaches₁ (step (table basis source deterministic compatible))
      (encode basis source deterministic compatible (toNatural first))
      (encode basis source deterministic compatible (toNatural last)) := by
  induction run with
  | single transition =>
      exact integer_step_reaches basis source deterministic compatible unit transition
        (natural _ Relation.ReflTransGen.refl) (natural _ (Relation.ReflTransGen.single transition))
  | @tail middle last earlier transition previous =>
      exact previous.trans (integer_step_reaches basis source deterministic compatible unit transition
        (natural middle earlier.to_reflTransGen)
        (natural last (earlier.to_reflTransGen.tail transition)))

/-- Integer source endpoints on the natural lattice retain the exact compiled first return. -/
theorem integer_step_firstReturn (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source)
    (unit : ∀ edge, Action.UnitShift (source edge).action)
    {first last : State n q} (transition : step source first = some last)
    (first_natural : ∀ index, 0 ≤ first.2 index) (last_natural : ∀ index, 0 ≤ last.2 index) :
    FirstReturn basis source deterministic compatible
      (encode basis source deterministic compatible (toNatural first))
      (encode basis source deterministic compatible (toNatural last)) := by
  apply step_firstReturn basis source deterministic compatible unit
  rw [naturalState_toNatural first first_natural, naturalState_toNatural last last_natural]
  exact transition

/-- A finite marked subset of the retained source-control positions. -/
def Marked (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source)
    (mark : Fin q → Bool) (state : State 2 (size basis source deterministic compatible)) : Prop :=
  ∃ position : Fin q, state.1 = PortNetwork.control (wiring basis source deterministic compatible)
    (boundary basis source position) ∧ mark position = true

theorem marked_boundary (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source)
    {mark : Fin q → Bool} {state : State 2 (size basis source deterministic compatible)}
    (marked : Marked basis source deterministic compatible mark state) :
    Boundary basis source deterministic compatible state := by
  obtain ⟨position, equal, _⟩ := marked
  exact ⟨position, equal⟩

theorem marked_encode_iff (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source)
    (mark : Fin q → Bool) (state : Counter.Configuration n q) :
    Marked basis source deterministic compatible mark
      (encode basis source deterministic compatible state) ↔ mark state.pc = true := by
  constructor
  · rintro ⟨position, equal, marked⟩
    have addresses := boundary_injective basis source
      (PortNetwork.control_unlinked_injective (wiring basis source deterministic compatible)
        (boundary_link_none basis source deterministic compatible state.pc)
        (boundary_link_none basis source deterministic compatible position) equal)
    rw [addresses]
    exact marked
  · exact fun marked => ⟨state.pc, rfl, marked⟩

def InternalMarkedStep (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source) (mark : Fin q → Bool)
    (first last : State 2 (size basis source deterministic compatible)) : Prop :=
  step (table basis source deterministic compatible) first = some last ∧
    ¬ Marked basis source deterministic compatible mark first

abbrev InternalMarkedReaches (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source) (mark : Fin q → Bool) :=
  Relation.ReflTransGen (InternalMarkedStep basis source deterministic compatible mark)

def MarkedFirstReturn (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source) (mark : Fin q → Bool)
    (first last : State 2 (size basis source deterministic compatible)) : Prop :=
  Marked basis source deterministic compatible mark first ∧
  Marked basis source deterministic compatible mark last ∧
  ∃ next, step (table basis source deterministic compatible) first = some next ∧
    InternalMarkedReaches basis source deterministic compatible mark next last

private theorem internal_to_marked (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source) (mark : Fin q → Bool)
    {first last : State 2 (size basis source deterministic compatible)}
    (run : InternalReaches basis source deterministic compatible first last) :
    InternalMarkedReaches basis source deterministic compatible mark first last := by
  exact Relation.ReflTransGen.mono
    (fun _ _ edge => ⟨edge.1, fun marked => edge.2 (marked_boundary basis source deterministic compatible marked)⟩)
    _ _ run

/-- An unmarked source step remains unmarked throughout its entire compiled execution. -/
theorem integer_unmarked_step (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source)
    (unit : ∀ edge, Action.UnitShift (source edge).action) (mark : Fin q → Bool)
    {first last : State n q} (transition : step source first = some last)
    (unmarked : mark first.1 = false)
    (first_natural : ∀ index, 0 ≤ first.2 index) (last_natural : ∀ index, 0 ≤ last.2 index) :
    InternalMarkedReaches basis source deterministic compatible mark
      (encode basis source deterministic compatible (toNatural first))
      (encode basis source deterministic compatible (toNatural last)) := by
  obtain ⟨_, _, next, initial, inside⟩ :=
    integer_step_firstReturn basis source deterministic compatible unit transition first_natural last_natural
  apply Relation.ReflTransGen.head (b := next) ?_
    (internal_to_marked basis source deterministic compatible mark inside)
  refine ⟨initial, ?_⟩
  rw [marked_encode_iff]
  change ¬ mark first.1 = true
  rw [unmarked]
  decide

/-- A preserved source invariant covers every intermediate unmarked source step. -/
theorem integer_internal_reaches (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source)
    (unit : ∀ edge, Action.UnitShift (source edge).action) (mark : Fin q → Bool)
    (valid : State n q → Prop) (stable : Stable source valid)
    (nonnegative : ∀ state, valid state → ∀ index, 0 ≤ state.2 index)
    {first last : State n q}
    (run : Relation.ReflTransGen (fun current next : State n q =>
      step source current = some next ∧ mark current.1 = false) first last)
    (first_valid : valid first) :
    InternalMarkedReaches basis source deterministic compatible mark
      (encode basis source deterministic compatible (toNatural first))
      (encode basis source deterministic compatible (toNatural last)) := by
  have lifted : valid last ∧ InternalMarkedReaches basis source deterministic compatible mark
      (encode basis source deterministic compatible (toNatural first))
      (encode basis source deterministic compatible (toNatural last)) := by
    induction run with
    | refl => exact ⟨first_valid, Relation.ReflTransGen.refl⟩
    | tail _ edge previous =>
        have last_valid := stable previous.1 edge.1
        exact ⟨last_valid, previous.2.trans
          (integer_unmarked_step basis source deterministic compatible unit mark edge.1 edge.2
            (nonnegative _ previous.1) (nonnegative _ last_valid))⟩
  exact lifted.2

/-- A marked source first return has exactly the same complete compressed endpoints. -/
theorem marked_firstReturn (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source)
    (unit : ∀ edge, Action.UnitShift (source edge).action) (mark : Fin q → Bool)
    (valid : State n q → Prop) (stable : Stable source valid)
    (nonnegative : ∀ state, valid state → ∀ index, 0 ≤ state.2 index)
    {first middle last : State n q} (initial : step source first = some middle)
    (rest : Relation.ReflTransGen (fun current next : State n q =>
      step source current = some next ∧ mark current.1 = false) middle last)
    (first_marked : mark first.1 = true) (last_marked : mark last.1 = true) (first_valid : valid first) :
    MarkedFirstReturn basis source deterministic compatible mark
      (encode basis source deterministic compatible (toNatural first))
      (encode basis source deterministic compatible (toNatural last)) := by
  have middle_valid := stable first_valid initial
  obtain ⟨_, _, next, head, inside⟩ := integer_step_firstReturn basis source deterministic compatible unit
    initial (nonnegative _ first_valid) (nonnegative _ middle_valid)
  refine ⟨(marked_encode_iff basis source deterministic compatible mark _).mpr first_marked,
    (marked_encode_iff basis source deterministic compatible mark _).mpr last_marked,
    next, head, ?_⟩
  exact (internal_to_marked basis source deterministic compatible mark inside).trans
    (integer_internal_reaches basis source deterministic compatible unit mark valid stable nonnegative rest middle_valid)

end Monodromy.Counter.Reversible.PrimeCompression

end


/-! Finite source marks on the same native geometric word table. -/

noncomputable section

namespace Monodromy.ReversibleCompilation

open Counter.Reversible CoupledContinuation

variable {q e : ℕ} [NeZero q]

/-- Only source vertices are observed; edge ports carry no source mark. -/
def markSource (mark : Fin q → Bool) (address : Fin (q + e)) : Bool :=
  match finSumFinEquiv.symm address with
  | .inl position => mark position
  | .inr _ => false

omit [NeZero q] in
@[simp] theorem markSource_source (mark : Fin q → Bool) (position : Fin q) :
    markSource (e := e) mark (Fin.castAdd e position) = mark position := by
  simp [markSource]

/-- The existing native words with a different finite stop table. -/
def markedProgram (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) (mark : Fin q → Bool) : Program (11 * (q + e)) :=
  StagedProgram.markedCompile 11 (q + e) (stages table deterministic compatible) (markSource mark)

@[simp] theorem markedProgram_advance (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) (mark : Fin q → Bool) :
    (markedProgram table deterministic compatible mark).advance =
      (haltingProgram table deterministic compatible).advance := rfl

/-- A source return is detected by the actual finite root observation. -/
def MarkedBoundary (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) (mark : Fin q → Bool) (state : Memory) : Prop :=
  (markedProgram table deterministic compatible mark).haltSignal state = 1

theorem markedBoundary_iota_iff (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) (mark : Fin q → Bool) (state : State 2 q) :
    MarkedBoundary table deterministic compatible mark (iota (e := e) state) ↔ mark state.1 = true := by
  have observed := StagedProgram.halt_embed_iff 11 (q + e)
    (stages table deterministic compatible) (markSource mark)
    (state.2 0) (state.2 1) 0 (Fin.castAdd e state.1) 0
  simpa only [MarkedBoundary, markedProgram, iota, sourcePoint, point, mul_zero, zero_add,
    true_and, markSource_source] using observed

private theorem stopped_phase (stages : Fin 11 → Program (q + e)) (bits : Fin (q + e) → Bool)
    (state : Memory) (stopped : (StagedProgram.markedCompile 11 (q + e) stages bits).haltSignal state = 1) :
    StagedProgram.PhaseBoundary 11 state := by
  obtain ⟨⟨base, phase⟩, rfl⟩ := (StagedProgram.packedEquiv 11).surjective state
  apply (StagedProgram.phaseBoundary_embed_iff 11 phase base).mpr
  by_contra nonzero
  have inactive : (StagedProgram.markedCompile 11 (q + e) stages bits).step
      (StagedProgram.embed 11 phase base) = none := by
    exact ite_eq_left stopped
  have active := StagedProgram.interior_step 11 (q + e) stages bits phase nonzero base
  rw [inactive] at active
  cases active

theorem markedBoundary_phase (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) (mark : Fin q → Bool) {state : Memory}
    (marked : MarkedBoundary table deterministic compatible mark state) :
    StagedProgram.PhaseBoundary 11 state :=
  stopped_phase (stages table deterministic compatible) (markSource mark) state marked

def NativeInternalStep (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) (mark : Fin q → Bool) (first last : Memory) : Prop :=
  (haltingProgram table deterministic compatible).step first = some last ∧
    ¬ MarkedBoundary table deterministic compatible mark first

abbrev NativeInternalReaches (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) (mark : Fin q → Bool) :=
  Relation.ReflTransGen (NativeInternalStep table deterministic compatible mark)

def NativeFirstReturn (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) (mark : Fin q → Bool) (first last : Memory) : Prop :=
  MarkedBoundary table deterministic compatible mark first ∧
  MarkedBoundary table deterministic compatible mark last ∧
  ∃ next, (haltingProgram table deterministic compatible).step first = some next ∧
    NativeInternalReaches table deterministic compatible mark next last

/-- After departure, one source edge visits no earlier packed phase-zero boundary. -/
theorem counter_departure (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) (mark : Fin q → Bool) {first last : State 2 q}
    (transition : Counter.Reversible.step table first = some last) :
    ∃ next, (haltingProgram table deterministic compatible).step (iota (e := e) first) = some next ∧
      NativeInternalReaches table deterministic compatible mark next (iota (e := e) last) := by
  let P := haltingProgram table deterministic compatible
  let initial := iota (e := e) first
  obtain ⟨cycle, _, _, interior, _⟩ := step_firstReturn table deterministic compatible transition
  obtain ⟨edge, enabled, _⟩ := (Counter.Reversible.step_iff table deterministic).mp transition
  have initial_active : P.haltSignal initial ≠ 1 := by
    intro stopped
    exact ((haltSignal_iota_iff table deterministic compatible first).mp stopped) ⟨edge, enabled.1⟩
  have active (round : ℕ) (before : round < 11) :
      P.step (P.advance^[round] initial) = some (P.advance^[round + 1] initial) := by
    rw [Function.iterate_succ_apply']
    apply ite_eq_right
    by_cases zero : round = 0
    · subst round
      exact initial_active
    · intro stopped
      exact interior round (by omega) before
        (stopped_phase (stages table deterministic compatible) (haltMark table)
          (P.advance^[round] initial) stopped)
  have unmarked (round : ℕ) (positive : 0 < round) (before : round < 11) :
      ¬ MarkedBoundary table deterministic compatible mark (P.advance^[round] initial) := by
    intro marked
    exact interior round positive before (markedBoundary_phase table deterministic compatible mark marked)
  have middle (round : ℕ) (bound : round ≤ 10) :
      NativeInternalReaches table deterministic compatible mark (P.advance initial)
        (P.advance^[round + 1] initial) := by
    induction round with
    | zero => exact Relation.ReflTransGen.refl
    | succ round previous =>
        exact (previous (by omega)).tail ⟨active (round + 1) (by omega),
          unmarked (round + 1) (by omega) (by omega)⟩
  refine ⟨P.advance initial, ?_, ?_⟩
  · simpa only [Nat.zero_add, Function.iterate_zero_apply, Function.iterate_one] using active 0 (by decide)
  · have inside := middle 10 (by decide)
    rw [cycle] at inside
    exact inside

/-- An unmarked source instruction executes entirely inside the native marked boundary. -/
theorem counter_internal_step (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) (mark : Fin q → Bool) {first last : State 2 q}
    (transition : Counter.Reversible.step table first = some last) (unmarked : mark first.1 = false) :
    NativeInternalReaches table deterministic compatible mark (iota (e := e) first) (iota (e := e) last) := by
  obtain ⟨next, initial, rest⟩ := counter_departure table deterministic compatible mark transition
  apply Relation.ReflTransGen.head (b := next) ?_ rest
  refine ⟨initial, ?_⟩
  rw [markedBoundary_iota_iff, unmarked]
  decide

theorem counter_internal_reaches (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) (mark : Fin q → Bool) {first last : State 2 q}
    (run : Relation.ReflTransGen (fun first last : State 2 q =>
      Counter.Reversible.step table first = some last ∧ mark first.1 = false) first last) :
    NativeInternalReaches table deterministic compatible mark (iota (e := e) first) (iota (e := e) last) := by
  induction run with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ edge previous =>
      exact previous.trans (counter_internal_step table deterministic compatible mark edge.1 edge.2)

/-- A finite marked counter return is the corresponding first native marked return. -/
theorem marked_firstReturn (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) (mark : Fin q → Bool) {first middle last : State 2 q}
    (initial : Counter.Reversible.step table first = some middle)
    (rest : Relation.ReflTransGen (fun first last : State 2 q =>
      Counter.Reversible.step table first = some last ∧ mark first.1 = false) middle last)
    (first_marked : mark first.1 = true) (last_marked : mark last.1 = true) :
    NativeFirstReturn table deterministic compatible mark (iota (e := e) first) (iota (e := e) last) := by
  obtain ⟨next, head, inside⟩ := counter_departure table deterministic compatible mark initial
  exact ⟨(markedBoundary_iota_iff table deterministic compatible mark first).mpr first_marked,
    (markedBoundary_iota_iff table deterministic compatible mark last).mpr last_marked,
    next, head, inside.trans (counter_internal_reaches table deterministic compatible mark rest)⟩

/-- The marked evaluator retains the original words on every unmarked original step. -/
theorem marked_step_of_original (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) (mark : Fin q → Bool) {first last : Memory}
    (transition : (haltingProgram table deterministic compatible).step first = some last)
    (unmarked : ¬ MarkedBoundary table deterministic compatible mark first) :
    (markedProgram table deterministic compatible mark).step first = some last := by
  change (if (markedProgram table deterministic compatible mark).haltSignal first = 1 then none
    else some ((markedProgram table deterministic compatible mark).advance first)) = some last
  change (markedProgram table deterministic compatible mark).haltSignal first ≠ 1 at unmarked
  rw [ite_eq_right unmarked, markedProgram_advance]
  unfold Program.step at transition
  split_ifs at transition
  exact transition

theorem internal_marked_reaches (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) (mark : Fin q → Bool) {first last : Memory}
    (run : NativeInternalReaches table deterministic compatible mark first last) :
    StateTransition.Reaches (markedProgram table deterministic compatible mark).step first last := by
  induction run with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ edge previous =>
      exact previous.tail (marked_step_of_original table deterministic compatible mark edge.1 edge.2)

/-- Execute the original native table once, then the same words until the next finite root mark. -/
def nativeMacro (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) (mark : Fin q → Bool) (state : Memory) : Part (Option Memory) :=
  match (haltingProgram table deterministic compatible).step state with
  | none => Part.some none
  | some next => ((markedProgram table deterministic compatible mark).eval next).map some

theorem nativeMacro_of_halt (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) (mark : Fin q → Bool) (state : Memory)
    (halted : (haltingProgram table deterministic compatible).step state = none) :
    nativeMacro table deterministic compatible mark state = Part.some none := by
  rw [nativeMacro, halted]

theorem nativeMacro_of_firstReturn (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) (mark : Fin q → Bool) {first last : Memory}
    (run : NativeFirstReturn table deterministic compatible mark first last) :
    nativeMacro table deterministic compatible mark first = Part.some (some last) := by
  obtain ⟨_, marked, next, head, rest⟩ := run
  have completed : (markedProgram table deterministic compatible mark).eval next = Part.some last := by
    apply Part.eq_some_iff.mpr
    exact StateTransition.mem_eval.mpr ⟨internal_marked_reaches table deterministic compatible mark rest,
      ite_eq_left marked⟩
  simp only [nativeMacro, head, completed, Part.map_some]

end Monodromy.ReversibleCompilation

end
