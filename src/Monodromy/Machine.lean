module

public import Monodromy.Radix
public import Monodromy.TwoStacks
public import Monodromy.Control
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Native finite-table machines

Two radix word branches retain the tape. A logarithmic branch retains the
finite control state and current symbol. Finite coefficient tables read these
branches and generate the next state; TM0 supplies the reference semantics.
-/

@[expose] public section

namespace Monodromy.Machine.Scheme

open Turing

variable {a q : ℕ} [NeZero a] [NeZero q]

abbrev State := Control.State 2

noncomputable def pcAngle (label : Fin q) (symbol : Fin a) : ℝ :=
  Control.angle (finProdFinEquiv (label, symbol)).val

noncomputable def encode (wordAngle : List (Fin a) → ℝ)
    (configuration : TwoStacks.Configuration (Fin a) (Fin q)) : State :=
  (pcAngle configuration.q configuration.head,
   ![wordAngle configuration.left, wordAngle configuration.right])

noncomputable def readHead (read : (Fin (a + 1) → ℝ) → ℝ → ℝ)
    (values : Fin a → ℝ) (x : ℝ) : ℝ :=
  read (fun digit => values (Fin.cases (default : Fin a) id digit)) x

/-- Each row is compiled from a fixed table entry, before the real-valued state is read. -/
noncomputable def rowTarget
    (push : Fin a → ℝ → ℝ) (pop : ℝ → ℝ)
    (read : (Fin (a + 1) → ℝ) → ℝ → ℝ)
    (machine : TM0.Machine (Fin a) (Fin q)) (row : Fin (q * a)) (point : State) : State :=
  let (label, symbol) := finProdFinEquiv.symm row
  match machine label symbol with
  | none => point
  | some (target, .write value) => (pcAngle target value, point.2)
  | some (target, .move .left) =>
      (readHead read (pcAngle target) (point.2 0),
       ![pop (point.2 0), push symbol (point.2 1)])
  | some (target, .move .right) =>
      (readHead read (pcAngle target) (point.2 1),
       ![push symbol (point.2 0), pop (point.2 1)])

/-- A finite analytic coefficient sum reads PC; no real-valued PC is decoded into a label. -/
noncomputable def next
    (push : Fin a → ℝ → ℝ) (pop : ℝ → ℝ)
    (read : (Fin (a + 1) → ℝ) → ℝ → ℝ)
    (machine : TM0.Machine (Fin a) (Fin q)) (point : State) : State :=
  (point.1 + ProgramCounter.choose
      (fun row => (rowTarget push pop read machine row point).1 - point.1) point.1,
   fun register => point.2 register + ProgramCounter.choose
      (fun row => (rowTarget push pop read machine row point).2 register - point.2 register) point.1)

noncomputable def haltSignal (machine : TM0.Machine (Fin a) (Fin q)) (point : State) : ℝ :=
  ProgramCounter.choose (fun row : Fin (q * a) =>
    let (label, symbol) := finProdFinEquiv.symm row
    match machine label symbol with | none => 1 | some _ => 0) point.1

theorem next_at_encode
    (wordAngle : List (Fin a) → ℝ) (push : Fin a → ℝ → ℝ) (pop : ℝ → ℝ)
    (read : (Fin (a + 1) → ℝ) → ℝ → ℝ)
    (machine : TM0.Machine (Fin a) (Fin q))
    (configuration : TwoStacks.Configuration (Fin a) (Fin q)) :
    next push pop read machine (encode wordAngle configuration) =
      rowTarget push pop read machine (finProdFinEquiv (configuration.q, configuration.head))
        (encode wordAngle configuration) := by
  apply Prod.ext
  · dsimp only [next, encode, pcAngle, Control.angle]
    rw [ProgramCounter.choose_at_j]
    ring
  · funext register
    dsimp only [next, encode, pcAngle, Control.angle]
    rw [ProgramCounter.choose_at_j]
    ring

/-- Primitive geometric laws suffice for exact full-state TM0 refinement. -/
theorem next_encode
    (wordAngle : List (Fin a) → ℝ) (push : Fin a → ℝ → ℝ) (pop : ℝ → ℝ)
    (read : (Fin (a + 1) → ℝ) → ℝ → ℝ)
    (push_correct : ∀ symbol stack, push symbol (wordAngle stack) = wordAngle (symbol :: stack))
    (pop_correct : ∀ stack, pop (wordAngle stack) = wordAngle stack.tail)
    (read_correct : ∀ values stack, readHead read values (wordAngle stack) = values stack.headI)
    (machine : TM0.Machine (Fin a) (Fin q))
    (configuration : TwoStacks.Configuration (Fin a) (Fin q)) :
    next push pop read machine (encode wordAngle configuration) =
      encode wordAngle ((TwoStacks.step machine configuration).getD configuration) := by
  rw [next_at_encode]
  simp only [rowTarget, Equiv.symm_apply_apply]
  cases transition : machine configuration.q configuration.head with
  | none => simp [TwoStacks.step, transition]
  | some instruction =>
      rcases instruction with ⟨label, instruction⟩
      cases instruction with
      | write symbol => simp [TwoStacks.step, transition, TwoStacks.write, encode]
      | move direction =>
          cases direction <;>
            simp [TwoStacks.step, transition, TwoStacks.move, encode,
              push_correct, pop_correct, read_correct]

theorem haltSignal_encode
    (wordAngle : List (Fin a) → ℝ) (machine : TM0.Machine (Fin a) (Fin q))
    (configuration : TwoStacks.Configuration (Fin a) (Fin q)) :
    haltSignal machine (encode wordAngle configuration) = 1 ↔
      TwoStacks.step machine configuration = none := by
  unfold haltSignal encode pcAngle Control.angle
  rw [ProgramCounter.choose_at_j]
  simp only [Equiv.symm_apply_apply]
  cases transition : machine configuration.q configuration.head <;>
    simp [TwoStacks.step, transition]

end Monodromy.Machine.Scheme

namespace Monodromy.Machine

open Turing
open scoped Classical

variable {a q : ℕ}

abbrev State := Control.State 2

noncomputable def encode (configuration : TwoStacks.Configuration (Fin a) (Fin q)) : State :=
  Scheme.encode Radix.Stack.wordAngle configuration

theorem wordAngle_injective : Function.Injective (Radix.Stack.wordAngle (a := a)) := by
  intro first second same
  apply Radix.Words.encode_injective
  unfold Radix.Stack.wordAngle at same
  exact Nat.cast_injective (mul_left_cancel₀ (mul_ne_zero two_ne_zero Real.pi_ne_zero) same)

theorem encode_injective : Function.Injective (@encode a q) := by
  intro first second same
  have positions : (first.q, first.head) = (second.q, second.head) :=
    finProdFinEquiv.injective (Fin.ext (Control.angle_injective (congrArg Prod.fst same)))
  have left : first.left = second.left := wordAngle_injective (congrFun (congrArg Prod.snd same) 0)
  have right : first.right = second.right := wordAngle_injective (congrFun (congrArg Prod.snd same) 1)
  have labels := congrArg Prod.fst positions
  have heads := congrArg Prod.snd positions
  cases first
  cases second
  cases labels
  cases left
  cases heads
  cases right
  rfl

def Valid (a q : ℕ) (point : State) : Prop :=
  ∃ configuration : TwoStacks.Configuration (Fin a) (Fin q), encode configuration = point

abbrev Memory (a q : ℕ) := {point : State // Valid a q point}

noncomputable def init (configuration : TwoStacks.Configuration (Fin a) (Fin q)) : Memory a q :=
  ⟨encode configuration, configuration, rfl⟩

theorem init_injective : Function.Injective (@init a q) := by
  intro first second same
  exact encode_injective (congrArg Subtype.val same)

theorem encode_grid (configuration : TwoStacks.Configuration (Fin a) (Fin q)) :
    Control.Paths.Grid (encode configuration) := by
  have angles (value : ℕ) : Circle.exp (Control.angle value) = 1 := by
    simpa only [Control.angle, Int.cast_natCast] using
      Circle.exp_int_mul_two_pi (value : ℤ)
  have words (word : List (Fin a)) : Circle.exp (Radix.Stack.wordAngle word) = 1 := by
    unfold Radix.Stack.wordAngle
    rw [mul_comm]
    exact angles (Radix.Words.encode word)
  intro index
  cases index with
  | none => exact angles (finProdFinEquiv (configuration.q, configuration.head)).val
  | some register =>
      fin_cases register
      · exact words configuration.left
      · exact words configuration.right

theorem valid_grid (memory : Memory a q) : Control.Paths.Grid memory.val := by
  obtain ⟨configuration, same⟩ := memory.property
  rw [← same]
  exact encode_grid configuration

variable [NeZero a] [NeZero q]

/-- The finite power cover supplies the stack operations and the head observation. -/
noncomputable def next (machine : TM0.Machine (Fin a) (Fin q)) (point : State) : State :=
  Scheme.next Radix.Stack.push (Radix.Stack.pop a) (Radix.choose (a + 1)) machine point

noncomputable def haltSignal (machine : TM0.Machine (Fin a) (Fin q)) (point : State) : ℝ :=
  Scheme.haltSignal machine point

theorem next_encode (machine : TM0.Machine (Fin a) (Fin q))
    (configuration : TwoStacks.Configuration (Fin a) (Fin q)) :
    next machine (encode configuration) =
      encode ((TwoStacks.step machine configuration).getD configuration) := by
  have reads (values : Fin a → ℝ) (word : List (Fin a)) :
      Scheme.readHead (Radix.choose (a + 1)) values (Radix.Stack.wordAngle word) =
        values word.headI := by
    unfold Scheme.readHead
    rw [Radix.Stack.choose_word]
    cases word <;> rfl
  exact Scheme.next_encode Radix.Stack.wordAngle Radix.Stack.push (Radix.Stack.pop a)
    (Radix.choose (a + 1)) Radix.Stack.push_word Radix.Stack.pop_word reads machine configuration

theorem haltSignal_encode (machine : TM0.Machine (Fin a) (Fin q))
    (configuration : TwoStacks.Configuration (Fin a) (Fin q)) :
    haltSignal machine (encode configuration) = 1 ↔ TwoStacks.step machine configuration = none :=
  Scheme.haltSignal_encode Radix.Stack.wordAngle machine configuration

theorem next_valid (machine : TM0.Machine (Fin a) (Fin q))
    {point : State} (valid : Valid a q point) : Valid a q (next machine point) := by
  obtain ⟨configuration, rfl⟩ := valid
  exact ⟨(TwoStacks.step machine configuration).getD configuration, (next_encode machine configuration).symm⟩

noncomputable def advance (machine : TM0.Machine (Fin a) (Fin q))
    (memory : Memory a q) : Memory a q :=
  ⟨next machine memory.val, next_valid machine memory.property⟩

theorem advance_init (machine : TM0.Machine (Fin a) (Fin q))
    (configuration : TwoStacks.Configuration (Fin a) (Fin q)) :
    advance machine (init configuration) =
      init ((TwoStacks.step machine configuration).getD configuration) :=
  Subtype.ext (next_encode machine configuration)

/-- Stopping is decided by the model's own finite analytic observation. -/
noncomputable def step (machine : TM0.Machine (Fin a) (Fin q))
    (memory : Memory a q) : Option (Memory a q) :=
  if haltSignal machine memory.val = 1 then none else some (advance machine memory)

theorem step_init (machine : TM0.Machine (Fin a) (Fin q))
    (configuration : TwoStacks.Configuration (Fin a) (Fin q)) :
    step machine (init configuration) = (TwoStacks.step machine configuration).map init := by
  unfold step
  split_ifs with signal
  · have stopped := (haltSignal_encode machine configuration).mp signal
    simp [stopped]
  · cases result : TwoStacks.step machine configuration with
    | none => exact (signal ((haltSignal_encode machine configuration).mpr result)).elim
    | some successor =>
        apply congrArg some
        apply Subtype.ext
        change next machine (encode configuration) = encode successor
        rw [next_encode]
        simp [result]

noncomputable def eval (machine : TM0.Machine (Fin a) (Fin q)) : Memory a q → Part (Memory a q) :=
  StateTransition.eval (step machine)

theorem eval_init (machine : TM0.Machine (Fin a) (Fin q))
    (configuration : TwoStacks.Configuration (Fin a) (Fin q)) :
    eval machine (init configuration) =
      init <$> StateTransition.eval (TwoStacks.step machine) configuration := by
  have refinement : StateTransition.Respects (TwoStacks.step machine) (step machine)
      (fun first second => init first = second) := by
    apply StateTransition.fun_respects.mpr
    intro source
    cases result : TwoStacks.step machine source with
    | none =>
        change step machine (init source) = none
        simp [step_init, result]
    | some successor =>
        change StateTransition.Reaches₁ (step machine) (init source) (init successor)
        apply Relation.TransGen.single
        simp [step_init, result]
  exact StateTransition.tr_eval' (TwoStacks.step machine) (step machine) init refinement configuration

/-- A native memory represents an entire source configuration, modulo trailing blank padding. -/
def Represents (source : TM0.Cfg (Fin a) (Fin q)) (memory : Memory a q) : Prop :=
  ∃ configuration : TwoStacks.Configuration (Fin a) (Fin q),
    TwoStacks.decode configuration = source ∧ init configuration = memory

omit [NeZero q] in
theorem source_covered (source : TM0.Cfg (Fin a) (Fin q)) :
    ∃ memory : Memory a q, Represents source memory := by
  obtain ⟨configuration, same⟩ := TwoStacks.decode_surjective source
  exact ⟨init configuration, configuration, same, rfl⟩

/-- Every source transition is performed by the native branch-controlled dynamics. -/
theorem simulatesTM0 (machine : TM0.Machine (Fin a) (Fin q)) :
    StateTransition.Respects (TM0.step machine) (step machine) Represents := by
  intro source memory related
  obtain ⟨configuration, rfl, rfl⟩ := related
  cases result : TwoStacks.step machine configuration with
  | none =>
      rw [← TwoStacks.decode_step, result]
      simp [step_init, result]
  | some successor =>
      rw [← TwoStacks.decode_step, result]
      refine ⟨init successor, ⟨successor, rfl, rfl⟩, Relation.TransGen.single ?_⟩
      simp [step_init, result]

/-- Native transitions also reflect the complete source state and halt behavior. -/
theorem reflectsTM0 (machine : TM0.Machine (Fin a) (Fin q)) :
    StateTransition.Respects (step machine) (TM0.step machine)
      (fun memory source => Represents source memory) := by
  intro memory source related
  obtain ⟨configuration, rfl, rfl⟩ := related
  rw [step_init]
  cases result : TwoStacks.step machine configuration with
  | none =>
      simp only [Option.map_none]
      rw [← TwoStacks.decode_step, result]
      rfl
  | some successor =>
      refine ⟨TwoStacks.decode successor, ⟨successor, rfl, rfl⟩, Relation.TransGen.single ?_⟩
      simp [← TwoStacks.decode_step machine configuration, result]

theorem halting_iff (machine : TM0.Machine (Fin a) (Fin q))
    {source : TM0.Cfg (Fin a) (Fin q)} {memory : Memory a q} (related : Represents source memory) :
    (eval machine memory).Dom ↔ (StateTransition.eval (TM0.step machine) source).Dom :=
  StateTransition.tr_eval_dom (simulatesTM0 machine) related

omit [NeZero q] in
theorem memory_covered (memory : Memory a q) :
    ∃ source : TM0.Cfg (Fin a) (Fin q), Represents source memory := by
  obtain ⟨configuration, same⟩ := memory.property
  exact ⟨TwoStacks.decode configuration, configuration, rfl, Subtype.ext same⟩

/-- The native final memory represents the entire final source state and tape. -/
theorem eval_represents (machine : TM0.Machine (Fin a) (Fin q))
    {source : TM0.Cfg (Fin a) (Fin q)} {memory result : Memory a q}
    (related : Represents source memory) (finished : result ∈ eval machine memory) :
    ∃ target, Represents target result ∧ target ∈ StateTransition.eval (TM0.step machine) source :=
  StateTransition.tr_eval_rev (simulatesTM0 machine) related finished

noncomputable def coordinate (memory : Memory a q) (i : Option (Fin 2)) : Logarithm.Memory :=
  Lattice.Return.coordinate (fun memory : Memory a q => Control.Paths.coords memory.val)
    valid_grid memory i

/-- The native branch state and analytic successor determine their own next path. -/
noncomputable def stepPath (machine : TM0.Machine (Fin a) (Fin q))
    (memory : Memory a q) (i : Option (Fin 2)) : Path (1 : Circle) 1 :=
  Lattice.Return.stepPath (fun memory : Memory a q => Control.Paths.coords memory.val)
    valid_grid (advance machine) memory i

theorem step_transport (machine : TM0.Machine (Fin a) (Fin q))
    (memory : Memory a q) (i : Option (Fin 2)) :
    Transport.transport Circle.isCoveringMap_exp (stepPath machine memory i)
      (coordinate memory i) = coordinate (advance machine memory) i :=
  Lattice.Return.step_transport _ _ _ memory i

noncomputable def runPath (machine : TM0.Machine (Fin a) (Fin q))
    (rounds : ℕ) (memory : Memory a q) (i : Option (Fin 2)) : Path (1 : Circle) 1 :=
  Lattice.Return.runPath (fun memory : Memory a q => Control.Paths.coords memory.val)
    valid_grid (advance machine) rounds memory i

/-- Every finite run is actual transport along the complete internally generated paths. -/
theorem run_transport (machine : TM0.Machine (Fin a) (Fin q))
    (rounds : ℕ) (memory : Memory a q) (i : Option (Fin 2)) :
    Transport.transport Circle.isCoveringMap_exp (runPath machine rounds memory i)
      (coordinate memory i) = coordinate (((advance machine)^[rounds]) memory) i :=
  Lattice.Return.run_transport _ _ _ rounds memory i

end Monodromy.Machine

namespace Monodromy.Machine

open Turing

variable {a q : ℕ} [NeZero a] [NeZero q]

theorem advance_represents (machine : TM0.Machine (Fin a) (Fin q))
    {source : TM0.Cfg (Fin a) (Fin q)} {memory : Memory a q}
    (related : Represents source memory) :
    Represents ((TM0.step machine source).getD source) (advance machine memory) := by
  obtain ⟨configuration, rfl, rfl⟩ := related
  rw [advance_init]
  refine ⟨_, ?_, rfl⟩
  rw [← TwoStacks.decode_step]
  cases TwoStacks.step machine configuration <;> simp

omit [NeZero q] in
/-- Each native memory has a unique source configuration, despite blank padding. -/
theorem represents_unique {first second : TM0.Cfg (Fin a) (Fin q)}
    {memory : Memory a q} (one : Represents first memory) (two : Represents second memory) :
    first = second := by
  obtain ⟨left, decoded_left, native_left⟩ := one
  obtain ⟨right, decoded_right, native_right⟩ := two
  have same := init_injective (native_left.trans native_right.symm)
  exact decoded_left.symm.trans ((congrArg TwoStacks.decode same).trans decoded_right)

end Monodromy.Machine

namespace Monodromy.Machine.Scheme

theorem analyticAt_registerRead (register : Fin 2) (point : State) :
    AnalyticAt ℝ (fun p : State => p.2 register) point :=
  ((ContinuousLinearMap.proj (R := ℝ) register).comp
    (ContinuousLinearMap.snd ℝ ℝ (Fin 2 → ℝ))).analyticAt point

variable {a q : ℕ} [NeZero a] [NeZero q]

theorem analyticAt_rowTarget
    (push : Fin a → ℝ → ℝ) (pop : ℝ → ℝ)
    (read : (Fin (a + 1) → ℝ) → ℝ → ℝ)
    (push_analytic : ∀ symbol x, AnalyticAt ℝ (push symbol) x)
    (pop_analytic : ∀ x, AnalyticAt ℝ pop x)
    (read_analytic : ∀ values x, AnalyticAt ℝ (read values) x)
    (machine : Turing.TM0.Machine (Fin a) (Fin q)) (row : Fin (q * a)) (point : State) :
    AnalyticAt ℝ (rowTarget push pop read machine row) point := by
  have heads (values : Fin a → ℝ) (x : ℝ) : AnalyticAt ℝ (readHead read values) x :=
    read_analytic _ x
  rcases row_spec : finProdFinEquiv.symm row with ⟨label, symbol⟩
  unfold rowTarget
  rw [row_spec]
  dsimp only
  cases transition : machine label symbol with
  | none => exact analyticAt_id
  | some instruction =>
    rcases instruction with ⟨target, instruction⟩
    cases instruction with
    | write value => exact analyticAt_const.prod analyticAt_snd
    | move direction =>
      cases direction with
      | left =>
        apply AnalyticAt.prod
        · exact (heads (pcAngle target) (point.2 0)).comp
            (f := fun p : State => p.2 0) (analyticAt_registerRead 0 point)
        · apply AnalyticAt.pi
          intro register
          fin_cases register
          · exact (pop_analytic (point.2 0)).comp
              (f := fun p : State => p.2 0) (analyticAt_registerRead 0 point)
          · exact (push_analytic symbol (point.2 1)).comp
              (f := fun p : State => p.2 1) (analyticAt_registerRead 1 point)
      | right =>
        apply AnalyticAt.prod
        · exact (heads (pcAngle target) (point.2 1)).comp
            (f := fun p : State => p.2 1) (analyticAt_registerRead 1 point)
        · apply AnalyticAt.pi
          intro register
          fin_cases register
          · exact (push_analytic symbol (point.2 0)).comp
              (f := fun p : State => p.2 0) (analyticAt_registerRead 0 point)
          · exact (pop_analytic (point.2 1)).comp
              (f := fun p : State => p.2 1) (analyticAt_registerRead 1 point)

theorem analyticAt_next
    (push : Fin a → ℝ → ℝ) (pop : ℝ → ℝ)
    (read : (Fin (a + 1) → ℝ) → ℝ → ℝ)
    (push_analytic : ∀ symbol x, AnalyticAt ℝ (push symbol) x)
    (pop_analytic : ∀ x, AnalyticAt ℝ pop x)
    (read_analytic : ∀ values x, AnalyticAt ℝ (read values) x)
    (machine : Turing.TM0.Machine (Fin a) (Fin q)) (point : State) :
    AnalyticAt ℝ (next push pop read machine) point := by
  have rows (row : Fin (q * a)) :
      AnalyticAt ℝ (rowTarget push pop read machine row) point :=
    analyticAt_rowTarget push pop read push_analytic pop_analytic read_analytic machine row point
  have weights (row : Fin (q * a)) :
      AnalyticAt ℝ (fun p : State => ProgramCounter.pcWeight row p.1) point :=
    (ProgramCounter.analyticAt_pcWeight row point.1).comp
      (f := fun p : State => p.1) analyticAt_fst
  unfold next ProgramCounter.choose
  apply AnalyticAt.prod
  · exact analyticAt_fst.add (Finset.analyticAt_fun_sum Finset.univ
      (fun row _ => (weights row).mul ((analyticAt_fst.comp (rows row)).sub analyticAt_fst)))
  · apply AnalyticAt.pi
    intro register
    exact (analyticAt_registerRead register point).add
      (Finset.analyticAt_fun_sum Finset.univ (fun row _ => (weights row).mul
        (((analyticAt_registerRead register (rowTarget push pop read machine row point)).comp
          (rows row)).sub (analyticAt_registerRead register point))))

omit [NeZero a] in
theorem analyticAt_haltSignal (machine : Turing.TM0.Machine (Fin a) (Fin q)) (point : State) :
    AnalyticAt ℝ (haltSignal machine) point := by
  unfold haltSignal
  exact (ProgramCounter.analyticAt_choose _ point.1).comp
    (f := fun p : State => p.1) analyticAt_fst

end Monodromy.Machine.Scheme

namespace Monodromy.Machine

variable {a q : ℕ} [NeZero a] [NeZero q]

/-- The full native TM successor is jointly real analytic throughout its real state space. -/
theorem analyticAt_next (machine : Turing.TM0.Machine (Fin a) (Fin q)) (point : State) :
    AnalyticAt ℝ (next machine) point :=
  Scheme.analyticAt_next Radix.Stack.push (Radix.Stack.pop a) (Radix.choose (a + 1))
    Radix.Stack.analyticAt_push (Radix.Stack.analyticAt_pop a)
    (Radix.analyticAt_choose (a + 1)) machine point

omit [NeZero a] in
theorem analyticAt_haltSignal (machine : Turing.TM0.Machine (Fin a) (Fin q)) (point : State) :
    AnalyticAt ℝ (haltSignal machine) point :=
  Scheme.analyticAt_haltSignal machine point

end Monodromy.Machine
