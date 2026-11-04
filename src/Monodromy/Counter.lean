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

end Monodromy.Counter.Reversible.Glue

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
## Finite traces inside larger control graphs
-/

namespace Monodromy.Counter.Reversible.Glue

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

end Monodromy.Counter.Reversible.Glue
