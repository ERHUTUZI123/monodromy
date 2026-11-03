module

public import Monodromy.Counter
public import Monodromy.ProgramCounter
public import Monodromy.Lattice
public import Mathlib.Analysis.Analytic.Linear

/-!
# Internal program control

Program position is another logarithmic branch. A fixed finite analytic sum
reads that position and the counter branches. The counter machine is the
integer specification of this rule, rather than an external dispatcher.
-/

@[expose] public section

namespace Monodromy.Control

abbrev State (n : ℕ) := ℝ × (Fin n → ℝ)

noncomputable def angle (value : ℕ) : ℝ := (value : ℝ) * (2 * Real.pi)

noncomputable def encode {n m : ℕ} (configuration : Counter.Configuration n m) : State n :=
  (angle configuration.pc.val, fun register => angle (configuration.counters register))

theorem zeroWeight_angle (value : ℕ) :
    Logarithm.zeroWeight (angle value) = if value = 0 then 1 else 0 := by
  simpa [angle] using Logarithm.zeroWeight_sheet (value : ℤ)

noncomputable def pcEffect {n m : ℕ} (instruction : Counter.Instruction n m)
    (source : Fin m) (point : State n) : ℝ :=
  match instruction with
  | .inc _ target => angle target.val - angle source.val
  | .dec register zero nonzero =>
      let weight := Logarithm.zeroWeight (point.2 register)
      weight * (angle zero.val - angle source.val) +
        (1 - weight) * (angle nonzero.val - angle source.val)
  | .halt => 0

noncomputable def registerEffect {n m : ℕ} (instruction : Counter.Instruction n m)
    (point : State n) (register : Fin n) : ℝ :=
  match instruction with
  | .inc target _ => if register = target then 2 * Real.pi else 0
  | .dec target _ _ =>
      if register = target then -2 * Real.pi * (1 - Logarithm.zeroWeight (point.2 target)) else 0
  | .halt => 0

noncomputable def pcDisplacement {n m : ℕ} (program : Counter.Program n m)
    (point : State n) : ℝ :=
  ProgramCounter.choose (fun position => pcEffect (program position) position point) point.1

noncomputable def registerDisplacement {n m : ℕ} (program : Counter.Program n m)
    (point : State n) (register : Fin n) : ℝ :=
  ProgramCounter.choose (fun position => registerEffect (program position) point register) point.1

/-- All state-dependent selection occurs inside the fixed analytic coefficient rule. -/
noncomputable def next {n m : ℕ} (program : Counter.Program n m) (point : State n) : State n :=
  (point.1 + pcDisplacement program point,
   fun register => point.2 register + registerDisplacement program point register)

noncomputable def haltSignal {n m : ℕ} (program : Counter.Program n m) (point : State n) : ℝ :=
  ProgramCounter.choose (fun position => match program position with
    | .halt => 1
    | _ => 0) point.1

theorem pcDisplacement_encode {n m : ℕ} (program : Counter.Program n m)
    (configuration : Counter.Configuration n m) :
    pcDisplacement program (encode configuration) =
      pcEffect (program configuration.pc) configuration.pc (encode configuration) :=
  ProgramCounter.choose_at_j _ configuration.pc

theorem registerDisplacement_encode {n m : ℕ} (program : Counter.Program n m)
    (configuration : Counter.Configuration n m) (register : Fin n) :
    registerDisplacement program (encode configuration) register =
      registerEffect (program configuration.pc) (encode configuration) register :=
  ProgramCounter.choose_at_j _ configuration.pc

theorem haltSignal_encode {n m : ℕ} (program : Counter.Program n m)
    (configuration : Counter.Configuration n m) :
    haltSignal program (encode configuration) =
      match program configuration.pc with | .halt => 1 | _ => 0 :=
  ProgramCounter.choose_at_j _ configuration.pc


section Analytic


variable {n m : ℕ}

private theorem analyticAt_registerRead (register : Fin n) (point : State n) :
    AnalyticAt ℝ (fun p : State n => p.2 register) point :=
  ((ContinuousLinearMap.proj (R := ℝ) register).comp
    (ContinuousLinearMap.snd ℝ ℝ (Fin n → ℝ))).analyticAt point

private theorem analyticAt_zeroRead (register : Fin n) (point : State n) :
    AnalyticAt ℝ (fun p : State n => Logarithm.zeroWeight (p.2 register)) point :=
  (Logarithm.analyticAt_zeroWeight (point.2 register)).comp
    (f := fun p : State n => p.2 register) (analyticAt_registerRead register point)

private theorem analyticAt_positionWeight (position : Fin m) (point : State n) :
    AnalyticAt ℝ (fun p : State n => ProgramCounter.pcWeight position p.1) point :=
  (ProgramCounter.analyticAt_pcWeight position point.1).comp
    (f := fun p : State n => p.1) analyticAt_fst

theorem analyticAt_pcEffect (instruction : Counter.Instruction n m)
    (source : Fin m) (point : State n) :
    AnalyticAt ℝ (pcEffect instruction source) point := by
  cases instruction with
  | inc => exact analyticAt_const
  | dec register =>
      exact ((analyticAt_zeroRead register point).mul analyticAt_const).add
        ((analyticAt_const.sub (analyticAt_zeroRead register point)).mul analyticAt_const)
  | halt => exact analyticAt_const

theorem analyticAt_registerEffect (instruction : Counter.Instruction n m)
    (register : Fin n) (point : State n) :
    AnalyticAt ℝ (fun p : State n => registerEffect instruction p register) point := by
  cases instruction with
  | inc => exact analyticAt_const
  | dec target =>
      by_cases same : register = target
      · simp only [registerEffect, same, ↓reduceIte]
        exact analyticAt_const.mul (analyticAt_const.sub (analyticAt_zeroRead target point))
      · simp only [registerEffect, same, ↓reduceIte]
        exact analyticAt_const
  | halt => exact analyticAt_const

theorem analyticAt_pcDisplacement (program : Counter.Program n m) (point : State n) :
    AnalyticAt ℝ (pcDisplacement program) point := by
  unfold pcDisplacement ProgramCounter.choose
  exact Finset.analyticAt_fun_sum Finset.univ (fun position _ =>
    (analyticAt_positionWeight position point).mul
      (analyticAt_pcEffect (program position) position point))

theorem analyticAt_registerDisplacement (program : Counter.Program n m)
    (register : Fin n) (point : State n) :
    AnalyticAt ℝ (fun p : State n => registerDisplacement program p register) point := by
  unfold registerDisplacement ProgramCounter.choose
  exact Finset.analyticAt_fun_sum Finset.univ (fun position _ =>
    (analyticAt_positionWeight position point).mul
      (analyticAt_registerEffect (program position) register point))

theorem analyticAt_next_pc (program : Counter.Program n m) (point : State n) :
    AnalyticAt ℝ (fun p : State n => (next program p).1) point :=
  analyticAt_fst.add (analyticAt_pcDisplacement program point)

theorem analyticAt_next_register (program : Counter.Program n m)
    (register : Fin n) (point : State n) :
    AnalyticAt ℝ (fun p : State n => (next program p).2 register) point :=
  (analyticAt_registerRead register point).add
    (analyticAt_registerDisplacement program register point)

/-- The complete successor is jointly real analytic, for each fixed finite program. -/
theorem analyticAt_next (program : Counter.Program n m) (point : State n) :
    AnalyticAt ℝ (next program) point :=
  (analyticAt_next_pc program point).prod
    (AnalyticAt.pi (fun register => analyticAt_next_register program register point))

theorem analyticAt_haltSignal (program : Counter.Program n m) (point : State n) :
    AnalyticAt ℝ (haltSignal program) point := by
  unfold haltSignal
  exact (ProgramCounter.analyticAt_choose _ point.1).comp
    (f := fun p : State n => p.1) analyticAt_fst

end Analytic


theorem next_encode {n m : ℕ} (program : Counter.Program n m)
    (configuration : Counter.Configuration n m) :
    next program (encode configuration) = encode (Counter.tick program configuration) := by
  unfold next
  rw [pcDisplacement_encode]
  simp_rw [registerDisplacement_encode]
  cases instruction : program configuration.pc with
  | inc target label =>
    apply Prod.ext
    · simp [pcEffect, encode, Counter.tick, Counter.step, instruction]
    · funext register
      by_cases same : register = target
      · subst register
        simp [registerEffect, encode, Counter.tick, Counter.step, instruction, angle]
        ring
      · simp [registerEffect, encode, Counter.tick, Counter.step, instruction, same]
  | dec target zero nonzero =>
    cases counter : configuration.counters target with
    | zero =>
      apply Prod.ext
      · simp [pcEffect, encode, zeroWeight_angle, Counter.tick, Counter.step, instruction, counter]
      · funext register
        by_cases same : register = target <;>
          simp [registerEffect, encode, zeroWeight_angle, Counter.tick, Counter.step,
            instruction, counter, same]
    | succ value =>
      apply Prod.ext
      · simp [pcEffect, encode, zeroWeight_angle, Counter.tick, Counter.step, instruction, counter]
      · funext register
        by_cases same : register = target
        · subst register
          simp [registerEffect, encode, zeroWeight_angle, Counter.tick, Counter.step,
            instruction, counter]
          simp [angle]
          ring
        · simp [registerEffect, encode, Counter.tick, Counter.step,
            instruction, counter, same]
  | halt =>
    apply Prod.ext
    · simp [pcEffect, encode, Counter.tick, Counter.step, instruction]
    · funext register
      simp [registerEffect, encode, Counter.tick, Counter.step, instruction]

namespace Paths


open unitInterval

variable {n m : ℕ}

def coords (point : State n) : Option (Fin n) → ℝ
  | none => point.1
  | some register => point.2 register

def Grid (point : State n) : Prop := ∀ i, Circle.exp (coords point i) = 1

/-- The native analytic target, rather than the counter specification, generates this curve. -/
noncomputable def trajectory (program : Counter.Program n m) (point : State n) :
    C(I, Option (Fin n) → ℝ) where
  toFun t i := coords point i + (t : ℝ) * (coords (next program point) i - coords point i)
  continuous_toFun := continuous_pi fun _ =>
    continuous_const.add (continuous_subtype_val.mul continuous_const)

theorem trajectory_start (program : Counter.Program n m) (point : State n) :
    trajectory program point 0 = coords point := by
  funext i
  simp [trajectory]

theorem trajectory_end (program : Counter.Program n m) (point : State n) :
    trajectory program point 1 = coords (next program point) := by
  funext i
  simp [trajectory]

/-- A generated loop needs only certificates that its native endpoints lie on the grid. -/
noncomputable def path (program : Counter.Program n m) (point : State n)
    (source : Grid point) (target : Grid (next program point))
    (i : Option (Fin n)) : Path (1 : Circle) 1 where
  toFun t := Circle.exp (trajectory program point t i)
  continuous_toFun := Circle.exp.continuous.comp
    ((continuous_apply i).comp (trajectory program point).continuous)
  source' := by rw [trajectory_start]; exact source i
  target' := by rw [trajectory_end]; exact target i

/-- Every generated coordinate path is executed by its actual exponential-cover lift. -/
theorem path_transport (program : Counter.Program n m) (point : State n)
    (source : Grid point) (target : Grid (next program point)) (i : Option (Fin n)) :
    (Transport.transport Circle.isCoveringMap_exp (path program point source target i)
      ⟨coords point i, source i⟩ : ℝ) = coords (next program point) i := by
  calc
    _ = trajectory program point 1 i := Transport.transport_eq_actual_lift
      Circle.isCoveringMap_exp (path program point source target i)
      ⟨coords point i, source i⟩
      ⟨fun t => trajectory program point t i,
        (continuous_apply i).comp (trajectory program point).continuous⟩
      rfl (congrFun (trajectory_start program point) i)
    _ = _ := congrFun (trajectory_end program point) i

theorem grid_encode (configuration : Counter.Configuration n m) : Grid (encode configuration) := by
  intro i
  cases i <;> simp [coords, encode, angle]

/-- A separately proved refinement supplies the native endpoint's grid certificate. -/
theorem grid_next_encode (program : Counter.Program n m)
    (configuration : Counter.Configuration n m) : Grid (next program (encode configuration)) := by
  rw [next_encode]
  exact grid_encode _

theorem encoded_transport (program : Counter.Program n m)
    (configuration : Counter.Configuration n m) (i : Option (Fin n)) :
    (Transport.transport Circle.isCoveringMap_exp
      (path program (encode configuration) (grid_encode configuration)
        (grid_next_encode program configuration) i)
      ⟨coords (encode configuration) i, grid_encode configuration i⟩ : ℝ) =
      coords (encode (Counter.tick program configuration)) i := by
  rw [path_transport, next_encode]

end Paths



theorem angle_injective : Function.Injective angle := by
  intro first second same
  unfold angle at same
  exact Nat.cast_injective
    (mul_right_cancel₀ (mul_ne_zero two_ne_zero Real.pi_ne_zero) same)

theorem encode_injective {n m : ℕ} :
    Function.Injective (@encode n m) := by
  intro first second same
  have positions : first.pc = second.pc :=
    Fin.ext (angle_injective (congrArg Prod.fst same))
  have counters : first.counters = second.counters :=
    funext (fun register => angle_injective (congrFun (congrArg Prod.snd same) register))
  exact congrArg₂ Counter.Configuration.mk positions counters

namespace Execution

open scoped Classical

def Valid {n : ℕ} (m : ℕ) (point : State n) : Prop :=
  ∃ configuration : Counter.Configuration n m, encode configuration = point

abbrev Memory (n m : ℕ) := {point : State n // Valid m point}

noncomputable def init {n m : ℕ} (configuration : Counter.Configuration n m) : Memory n m :=
  ⟨encode configuration, configuration, rfl⟩

theorem init_injective {n m : ℕ} :
    Function.Injective (@init n m) := by
  intro first second same
  exact encode_injective (congrArg Subtype.val same)

theorem next_valid {n m : ℕ} (program : Counter.Program n m)
    {point : State n} (valid : Valid m point) : Valid m (next program point) := by
  obtain ⟨configuration, rfl⟩ := valid
  exact ⟨Counter.tick program configuration, (next_encode program configuration).symm⟩

noncomputable def advance {n m : ℕ} (program : Counter.Program n m)
    (memory : Memory n m) : Memory n m :=
  ⟨next program memory.val, next_valid program memory.property⟩

theorem advance_init {n m : ℕ} (program : Counter.Program n m)
    (configuration : Counter.Configuration n m) :
    advance program (init configuration) = init (Counter.tick program configuration) :=
  Subtype.ext (next_encode program configuration)

theorem valid_grid {n m : ℕ} (memory : Memory n m) : Paths.Grid memory.val := by
  obtain ⟨configuration, same⟩ := memory.property
  rw [← same]
  exact Paths.grid_encode configuration

/-- Native execution tests its own analytic halt observation. -/
noncomputable def step {n m : ℕ} (program : Counter.Program n m)
    (memory : Memory n m) : Option (Memory n m) :=
  if haltSignal program memory.val = 1 then none else some (advance program memory)

theorem haltSignal_encode_iff {n m : ℕ} (program : Counter.Program n m)
    (configuration : Counter.Configuration n m) :
    haltSignal program (encode configuration) = 1 ↔ Counter.step program configuration = none := by
  rw [haltSignal_encode]
  cases instruction : program configuration.pc with
  | inc => simp [Counter.step, instruction]
  | dec register =>
    cases counter : configuration.counters register <;> simp [Counter.step, instruction, counter]
  | halt => simp [Counter.step, instruction]

theorem step_init {n m : ℕ} (program : Counter.Program n m)
    (configuration : Counter.Configuration n m) :
    step program (init configuration) = (Counter.step program configuration).map init := by
  unfold step
  split_ifs with signal
  · have stopped := (haltSignal_encode_iff program configuration).mp signal
    simp [stopped]
  · cases result : Counter.step program configuration with
    | none => exact (signal ((haltSignal_encode_iff program configuration).mpr result)).elim
    | some successor =>
      apply congrArg some
      apply Subtype.ext
      change next program (encode configuration) = encode successor
      rw [next_encode]
      simp [Counter.tick, result]

/-- Partial execution follows only native successors and the native halt signal. -/
noncomputable def eval {n m : ℕ} (program : Counter.Program n m) : Memory n m → Part (Memory n m) :=
  StateTransition.eval (step program)

theorem eval_init {n m : ℕ} (program : Counter.Program n m)
    (configuration : Counter.Configuration n m) :
    eval program (init configuration) = init <$> Counter.eval program configuration := by
  have refinement : StateTransition.Respects (Counter.step program) (step program)
      (fun first second => init first = second) := by
    apply StateTransition.fun_respects.mpr
    intro source
    cases result : Counter.step program source with
    | none =>
      change step program (init source) = none
      simp [step_init, result]
    | some successor =>
      change StateTransition.Reaches₁ (step program) (init source) (init successor)
      apply Relation.TransGen.single
      simp [step_init, result]
  exact StateTransition.tr_eval' (Counter.step program) (step program) init refinement configuration

end Execution

namespace Execution


variable {n m : ℕ}

noncomputable def coordinate (memory : Memory n m) (i : Option (Fin n)) : Logarithm.Memory :=
  ⟨Paths.coords memory.val i, valid_grid memory i⟩

/-- Only the native current state and native analytic target determine the path. -/
noncomputable def stepPath (program : Counter.Program n m)
    (memory : Memory n m) (i : Option (Fin n)) : Path (1 : Circle) 1 :=
  Paths.path program memory.val (valid_grid memory) (valid_grid (advance program memory)) i

theorem step_transport (program : Counter.Program n m)
    (memory : Memory n m) (i : Option (Fin n)) :
    Transport.transport Circle.isCoveringMap_exp (stepPath program memory i)
      (coordinate memory i) = coordinate (advance program memory) i := by
  apply Subtype.ext
  exact Paths.path_transport program memory.val (valid_grid memory)
    (valid_grid (advance program memory)) i

/-- Each later path is generated from the succeeding native memory, without an instruction list. -/
noncomputable def runPath (program : Counter.Program n m) :
    ℕ → Memory n m → Option (Fin n) → Path (1 : Circle) 1
  | 0, _, _ => Path.refl 1
  | rounds + 1, memory, i =>
      (stepPath program memory i).trans (runPath program rounds (advance program memory) i)

/-- Every finite run is the actual transport along its internally generated complete paths. -/
theorem run_transport (program : Counter.Program n m) (rounds : ℕ)
    (memory : Memory n m) (i : Option (Fin n)) :
    Transport.transport Circle.isCoveringMap_exp (runPath program rounds memory i)
      (coordinate memory i) = coordinate (((advance program)^[rounds]) memory) i := by
  induction rounds generalizing memory with
  | zero => simp [runPath]
  | succ rounds ih =>
      change Transport.transport Circle.isCoveringMap_exp
        ((stepPath program memory i).trans
          (runPath program rounds (advance program memory) i)) _ = _
      rw [Transport.transport_trans, step_transport, ih, Function.iterate_succ_apply]

end Execution

end Monodromy.Control
