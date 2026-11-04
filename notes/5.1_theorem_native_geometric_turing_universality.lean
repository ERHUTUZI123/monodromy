module

public import Mathlib.Computability.TuringMachine.ToPartrec
public import Monodromy.FiniteSupport
public import Monodromy.Counter

/-!
# Finite Turing tables and native continuation

Mathlib's stack evaluator is translated to a Post–Turing table and restricted
to its finite support. The source code fixes the table; its numeric arguments
are supplied through an explicit finite input word.

The native simulation composes the actual finite counter compilers with
fixed geometric Word execution. It preserves full configurations, complete
partial results, halting and divergence. Source steps are causal first returns
marked by finite analytic root observations. Finite executions are realized
by the two matching covering-space lifts.
-/

@[expose] public section

namespace Monodromy.FormalCompilation

open Turing

abbrev Stack := PartrecToTM2.K'
abbrev Symbol := PartrecToTM2.Γ'
abbrev Store := Option Symbol
abbrev Label2 := PartrecToTM2.Λ'
abbrev Alphabet := TM2to1.Γ' Stack (fun _ => Symbol)

instance stackFintype : Fintype Stack where
  elems := {.main, .rev, .aux, .stack}
  complete := by intro value; cases value <;> simp

/-- The parameter fixes the distinguished initial label of the compiled table. -/
@[nolint unusedArguments]
def Control1 (_source : ToPartrec.Code) : Type :=
  TM2to1.Λ' Stack (fun _ => Symbol) Label2 Store

variable (source : ToPartrec.Code)

instance control1Inhabited : Inhabited (Control1 source) :=
  ⟨TM2to1.Λ'.normal (PartrecToTM2.trNormal source PartrecToTM2.Cont'.halt)⟩

def machine1 : Control1 source → TM1.Stmt Alphabet (Control1 source) Store :=
  TM2to1.tr PartrecToTM2.tr

def Control0 : Type := TM1to0.Λ' (machine1 source)

instance control0Inhabited : Inhabited (Control0 source) :=
  inferInstanceAs (Inhabited (TM1to0.Λ' (machine1 source)))

def machine0 : TM0.Machine Alphabet (Control0 source) := TM1to0.tr (machine1 source)

noncomputable def labels1 : Finset (Control1 source) :=
  TM2to1.trSupp PartrecToTM2.tr (PartrecToTM2.codeSupp source PartrecToTM2.Cont'.halt)

theorem supports1 : TM1.Supports (machine1 source) (labels1 source) := by
  let _ : Inhabited Label2 := ⟨PartrecToTM2.trNormal source PartrecToTM2.Cont'.halt⟩
  exact TM2to1.tr_supports PartrecToTM2.tr
    (PartrecToTM2.tr_supports source PartrecToTM2.Cont'.halt)

noncomputable def labels0 : Finset (Control0 source) := TM1to0.trStmts (machine1 source) (labels1 source)

theorem supports0 : TM0.Supports (machine0 source) (labels0 source : Set (Control0 source)) :=
  TM1to0.tr_supports (machine1 source) (supports1 source)

noncomputable def finiteSupport : FiniteSupport.Support (machine0 source) :=
  ⟨labels0 source, supports0 source⟩

omit source in
/-- Every list of numeric arguments has an explicit word over the finite tape alphabet. -/
def tapeData (values : List ℕ) : List Alphabet :=
  TM2to1.trInit PartrecToTM2.K'.main (PartrecToTM2.trList values)

theorem initial_relation (values : List ℕ) :
    TM2to1.TrCfg (PartrecToTM2.init source values)
      (TM1.init (tapeData values) : TM1.Cfg Alphabet (Control1 source) Store) := by
  let _ : Inhabited Label2 := ⟨PartrecToTM2.trNormal source PartrecToTM2.Cont'.halt⟩
  have initial := TM2to1.trCfg_init (Γ := fun _ : Stack => Symbol) (Λ := Label2) (σ := Store)
    PartrecToTM2.K'.main (PartrecToTM2.trList values)
  have same : (TM2.init PartrecToTM2.K'.main (PartrecToTM2.trList values) :
      TM2.Cfg (fun _ : Stack => Symbol) Label2 Store) = PartrecToTM2.init source values := by
    apply congrArg (fun storage => TM2.Cfg.mk
      (some (PartrecToTM2.trNormal source PartrecToTM2.Cont'.halt)) none storage)
    funext index
    cases index <;> rfl
  rw [same] at initial
  exact initial

/-- Projection to every stack determines the entire packed tape. -/
theorem relation_unique
    {configuration : TM2.Cfg (fun _ : Stack => Symbol) Label2 Store}
    {first second : TM1.Cfg Alphabet (Control1 source) Store}
    (first_related : TM2to1.TrCfg configuration first)
    (second_related : TM2to1.TrCfg configuration second) : first = second := by
  cases first_related with
  | mk first first_projection =>
      cases second_related with
      | mk second second_projection =>
          have same : first = second := by
            apply ListBlank.ext
            intro index
            funext column
            have projected := congrArg (fun word => ListBlank.nth word index)
              ((first_projection column).trans (second_projection column).symm)
            simpa only [proj_map_nth] using projected
          subst second
          rfl

theorem relation_stop
    {configuration : TM2.Cfg (fun _ : Stack => Symbol) Label2 Store}
    {target : TM1.Cfg Alphabet (Control1 source) Store}
    (related : TM2to1.TrCfg configuration target) :
    TM2to1.TrCfg (Λ := Label2) { configuration with l := none } { target with l := none } := by
  cases related with
  | mk contents projection => exact TM2to1.TrCfg.mk contents projection

def halt1 (values : List ℕ) : TM1.Cfg Alphabet (Control1 source) Store :=
  { (TM1.init (tapeData values) : TM1.Cfg Alphabet (Control1 source) Store) with l := none }

theorem halt_relation (values : List ℕ) :
    TM2to1.TrCfg (PartrecToTM2.halt values) (halt1 source values) :=
  relation_stop source (initial_relation source values)

/-- The complete result, including divergence, survives stack-to-tape translation. -/
theorem eval1 (values : List ℕ) :
    StateTransition.eval (TM1.step (machine1 source))
      (TM1.init (tapeData values) : TM1.Cfg Alphabet (Control1 source) Store) =
      halt1 source <$> source.eval values := by
  have source_evaluation := PartrecToTM2.tr_eval source values
  apply Part.ext
  intro target
  constructor
  · intro completed
    obtain ⟨source_result, related, finished⟩ := StateTransition.tr_eval_rev
      (TM2to1.tr_respects PartrecToTM2.tr) (initial_relation source values) completed
    rw [source_evaluation] at finished
    obtain ⟨value, value_finished, rfl⟩ := (Part.mem_map_iff _).mp finished
    exact (Part.mem_map_iff _).mpr
      ⟨value, value_finished, (relation_unique source related (halt_relation source value)).symm⟩
  · intro completed
    obtain ⟨result, result_finished, rfl⟩ := (Part.mem_map_iff _).mp completed
    have source_finished : PartrecToTM2.halt result ∈
        StateTransition.eval (TM2.step PartrecToTM2.tr) (PartrecToTM2.init source values) := by
      rw [source_evaluation]
      exact (Part.mem_map_iff _).mpr ⟨result, result_finished, rfl⟩
    obtain ⟨target, related, finished⟩ := StateTransition.tr_eval
      (TM2to1.tr_respects PartrecToTM2.tr) (initial_relation source values) source_finished
    have same := relation_unique source related (halt_relation source result)
    rw [same] at finished
    exact finished

def halt0 (values : List ℕ) : TM0.Cfg Alphabet (Control0 source) :=
  TM1to0.trCfg (machine1 source) (halt1 source values)

theorem initial0 (values : List ℕ) :
    TM1to0.trCfg (machine1 source) (TM1.init (tapeData values)) =
      (TM0.init (tapeData values) : TM0.Cfg Alphabet (Control0 source)) := rfl

/-- Compilation preserves the complete partial function on every numeric argument list. -/
theorem eval0 (values : List ℕ) :
    StateTransition.eval (TM0.step (machine0 source))
      (TM0.init (tapeData values) : TM0.Cfg Alphabet (Control0 source)) =
      halt0 source <$> source.eval values := by
  have translated := StateTransition.tr_eval' (TM1.step (machine1 source)) (TM0.step (machine0 source))
    (TM1to0.trCfg (machine1 source)) (TM1to0.tr_respects (machine1 source))
    (TM1.init (tapeData values))
  rw [initial0, eval1] at translated
  exact translated.trans (by rfl)

/-- The actual control carrier is finite; embedding preserves the entire final configuration. -/
theorem eval_finite (values : List ℕ) :
    (finiteSupport source).embed <$>
      StateTransition.eval (TM0.step (finiteSupport source).restrict) (TM0.init (tapeData values)) =
      halt0 source <$> source.eval values := by
  rw [← (finiteSupport source).eval_embed, (finiteSupport source).embed_init]
  exact eval0 source values

theorem halting_finite_iff (values : List ℕ) :
    (StateTransition.eval (TM0.step (finiteSupport source).restrict) (TM0.init (tapeData values))).Dom ↔
      (source.eval values).Dom := by
  have same := congrArg Part.Dom (eval_finite source values)
  exact same.to_iff

omit source in
/-- Every partial recursive unary numeric function has a finite table with exact encoded output. -/
theorem every_partrec {f : ℕ → Part ℕ} (partial_recursive : Partrec f) :
    ∃ source : ToPartrec.Code, ∀ input : ℕ,
      (finiteSupport source).embed <$>
        StateTransition.eval (TM0.step (finiteSupport source).restrict) (TM0.init (tapeData [input])) =
        (fun result => halt0 source [result]) <$> f input := by
  obtain ⟨source, correct⟩ := ToPartrec.Code.exists_code (Nat.Partrec'.part_iff₁.mpr partial_recursive)
  refine ⟨source, fun input => ?_⟩
  rw [eval_finite, correct ⟨[input], rfl⟩]
  rfl

end Monodromy.FormalCompilation

noncomputable section

namespace Monodromy.NativeTuring

open Turing CoupledContinuation

variable (a q : ℕ) [NeZero a] [NeZero q]

def source3 (machine : TM0.Machine (Fin a) (Fin q)) :
    Counter.Program 3 (Counter.TuringCompiler.size a q) :=
  Counter.TuringCompiler.program a q machine

def source2 (machine : TM0.Machine (Fin a) (Fin q)) :
    Counter.Program 2 (Counter.Compression.size (source3 a q machine)) :=
  Counter.Compression.program (source3 a q machine)

instance source3_nonempty : NeZero (Counter.TuringCompiler.size a q) := by
  have bound := (Counter.TuringCompiler.dispatch a q (0, 0)).isLt
  exact ⟨by omega⟩

instance source2_nonempty (machine : TM0.Machine (Fin a) (Fin q)) :
    NeZero (Counter.Compression.size (source3 a q machine)) := by
  have bound := (Counter.Compression.dispatch (source3 a q machine)
    (Counter.TuringCompiler.dispatch a q (0, 0))).isLt
  exact ⟨by omega⟩

/-- The only runtime is the existing finite native Word/Program interpreter. -/
def program (machine : TM0.Machine (Fin a) (Fin q)) :
    CoupledContinuation.Program (Counter.Compression.size (source3 a q machine) * 3) :=
  CounterContinuation.compile (source2 a q machine)

/-- Initialization composes the three already verified, faithful source encodings. -/
def iota (machine : TM0.Machine (Fin a) (Fin q)) (state : TM0.Cfg (Fin a) (Fin q)) : Memory :=
  CounterContinuation.encode
    (Counter.Compression.encode (source3 a q machine) (Counter.TuringCompiler.encode a q state))

theorem iota_injective (machine : TM0.Machine (Fin a) (Fin q)) :
    Function.Injective (iota a q machine) :=
  CounterContinuation.encode_injective.comp
    ((Counter.Compression.encode_injective (source3 a q machine)).comp
      (Counter.TuringCompiler.encode_injective a q))

/-- Every live source step has a positive native run, including source self-loops. -/
theorem step_reaches (machine : TM0.Machine (Fin a) (Fin q))
    {first last : TM0.Cfg (Fin a) (Fin q)} (transition : TM0.step machine first = some last) :
    StateTransition.Reaches₁ (program a q machine).step (iota a q machine first) (iota a q machine last) := by
  have run3 := Counter.TuringCompiler.firstReturn_positive a q machine
    (Counter.TuringCompiler.step_firstReturn a q machine transition)
  rcases StateTransition.tr_reaches₁ (Counter.Compression.respects (source3 a q machine))
    rfl run3 with ⟨_, rfl, run2⟩
  rcases StateTransition.tr_reaches₁ (CounterContinuation.simulates (source2 a q machine))
    rfl run2 with ⟨_, rfl, native_run⟩
  exact native_run

/-- A halted source configuration halts at its actual native root state. -/
theorem step_halt (machine : TM0.Machine (Fin a) (Fin q))
    (state : TM0.Cfg (Fin a) (Fin q)) (halted : TM0.step machine state = none) :
    (program a q machine).step (iota a q machine state) = none := by
  have halted3 := (Counter.TuringCompiler.halt_encode a q machine state).mpr halted
  have halted2 := (Counter.Compression.halt_encode (source3 a q machine)
    (Counter.TuringCompiler.encode a q state)).mpr halted3
  have result := StateTransition.fun_respects.mp (CounterContinuation.simulates (source2 a q machine))
    (a₁ := Counter.Compression.encode (source3 a q machine) (Counter.TuringCompiler.encode a q state))
  change Counter.step (source2 a q machine)
    (Counter.Compression.encode (source3 a q machine) (Counter.TuringCompiler.encode a q state)) = none at halted2
  rw [halted2] at result
  exact result

/-- The complete geometric transition system refines every finite Post–Turing machine. -/
theorem respects (machine : TM0.Machine (Fin a) (Fin q)) :
    StateTransition.Respects (TM0.step machine) (program a q machine).step
      (fun original native => iota a q machine original = native) := by
  apply StateTransition.fun_respects.mpr
  intro state
  cases transition : TM0.step machine state with
  | none => exact step_halt a q machine state transition
  | some next => exact step_reaches a q machine transition

/-- Exact complete configurations, not only output values, agree under native execution. -/
theorem eval_iota (machine : TM0.Machine (Fin a) (Fin q)) (state : TM0.Cfg (Fin a) (Fin q)) :
    (program a q machine).eval (iota a q machine state) =
      iota a q machine <$> StateTransition.eval (TM0.step machine) state :=
  StateTransition.tr_eval' (TM0.step machine) (program a q machine).step
    (iota a q machine) (respects a q machine) state

theorem halting_iff (machine : TM0.Machine (Fin a) (Fin q)) (state : TM0.Cfg (Fin a) (Fin q)) :
    ((program a q machine).eval (iota a q machine state)).Dom ↔
      (StateTransition.eval (TM0.step machine) state).Dom := by
  rw [eval_iota]
  rfl

theorem divergence_iff (machine : TM0.Machine (Fin a) (Fin q)) (state : TM0.Cfg (Fin a) (Fin q)) :
    ¬ ((program a q machine).eval (iota a q machine state)).Dom ↔
      ¬ (StateTransition.eval (TM0.step machine) state).Dom :=
  not_congr (halting_iff a q machine state)

/-- Source results are reached exactly, with their complete encoded configuration. -/
theorem result_iota (machine : TM0.Machine (Fin a) (Fin q))
    {first last : TM0.Cfg (Fin a) (Fin q)}
    (completed : last ∈ StateTransition.eval (TM0.step machine) first) :
    iota a q machine last ∈ (program a q machine).eval (iota a q machine first) := by
  rw [eval_iota]
  exact (Part.mem_map_iff _).mpr ⟨last, completed, rfl⟩

/-- Every native result has a unique source result, by the faithful encoding. -/
theorem result_iff (machine : TM0.Machine (Fin a) (Fin q))
    (first last : TM0.Cfg (Fin a) (Fin q)) :
    iota a q machine last ∈ (program a q machine).eval (iota a q machine first) ↔
      last ∈ StateTransition.eval (TM0.step machine) first := by
  rw [eval_iota]
  constructor
  · intro result
    rcases (Part.mem_map_iff _).mp result with ⟨source, completed, same⟩
    have recovered := iota_injective a q machine same
    simpa only [recovered] using completed
  · intro result
    exact (Part.mem_map_iff _).mpr ⟨last, result, rfl⟩

/-- Every finite source run lifts to a finite run of the same fixed native program. -/
theorem reaches_iota (machine : TM0.Machine (Fin a) (Fin q))
    {first last : TM0.Cfg (Fin a) (Fin q)}
    (run : StateTransition.Reaches (TM0.step machine) first last) :
    StateTransition.Reaches (program a q machine).step (iota a q machine first) (iota a q machine last) := by
  rcases StateTransition.tr_reaches (respects a q machine) rfl run with ⟨_, rfl, lifted⟩
  exact lifted

/-- The same causal path generator realizes every finite prefix, whether or not execution halts. -/
theorem finite_run_path (machine : TM0.Machine (Fin a) (Fin q))
    {first last : TM0.Cfg (Fin a) (Fin q)}
    (run : StateTransition.Reaches (TM0.step machine) first last) :
    ∃ count : ℕ,
      restrictedTrajectory ((program a q machine).runDriver count (iota a q machine first))
        (iota a q machine first) 1 = restrictedState (iota a q machine last) :=
  (program a q machine).runDriver_endpoint_of_reaches (reaches_iota a q machine run)

/-- The finite path generator uses only the initial state and preceding actual lift results. -/
theorem result_actual_lifts (machine : TM0.Machine (Fin a) (Fin q))
    {first last : TM0.Cfg (Fin a) (Fin q)}
    (completed : last ∈ StateTransition.eval (TM0.step machine) first) :
    ∃ count : ℕ,
      let initial := iota a q machine first
      let driver := (program a q machine).runDriver count initial
      intermediateCurve driver initial =
        CoupledPullback.lowerCovering.liftPath driver.restrictedPath
          (CoupledPullback.upperProjection (restrictedState initial))
          (driver.restrictedPath.source.trans (restrictedState_over_base initial).symm) ∧
      restrictedTrajectory driver initial =
        CoupledPullback.upperCovering.liftPath (intermediatePath driver initial) (restrictedState initial)
          (intermediatePath driver initial).source ∧
      restrictedTrajectory driver initial 1 = restrictedState (iota a q machine last) := by
  obtain ⟨count, endpoint⟩ := (program a q machine).runDriver_of_eval (result_iota a q machine completed)
  refine ⟨count, ?_⟩
  dsimp only
  refine ⟨intermediateCurve_actual_lift _ _, restrictedTrajectory_actual_lift _ _, ?_⟩
  rw [restrictedTrajectory_end, endpoint]

section FiniteTypes

variable {Γ Q : Type} [Fintype Γ] [Inhabited Γ] [Fintype Q] [Inhabited Q]

/-- Pointed finite enumeration changes only the presentation of the source alphabet and control. -/
def finiteProgram (machine : TM0.Machine Γ Q) :=
  program (Fintype.card Γ) (Fintype.card Q) (FiniteRenaming.machine machine)

def finiteIota (machine : TM0.Machine Γ Q) (state : TM0.Cfg Γ Q) : Memory :=
  iota (Fintype.card Γ) (Fintype.card Q) (FiniteRenaming.machine machine)
    (FiniteRenaming.configuration state)

theorem finiteIota_injective (machine : TM0.Machine Γ Q) :
    Function.Injective (finiteIota machine) :=
  (iota_injective _ _ (FiniteRenaming.machine machine)).comp FiniteRenaming.configuration_injective

/-- The same native model simulates every finite pointed alphabet and control type. -/
theorem finite_eval_iota (machine : TM0.Machine Γ Q) (state : TM0.Cfg Γ Q) :
    (finiteProgram machine).eval (finiteIota machine state) =
      finiteIota machine <$> StateTransition.eval (TM0.step machine) state := by
  unfold finiteProgram finiteIota
  rw [eval_iota, FiniteRenaming.eval_configuration]
  rfl

theorem finite_step_reaches (machine : TM0.Machine Γ Q)
    {first last : TM0.Cfg Γ Q} (transition : TM0.step machine first = some last) :
    StateTransition.Reaches₁ (finiteProgram machine).step (finiteIota machine first) (finiteIota machine last) := by
  apply step_reaches
  rw [← FiniteRenaming.step_configuration, transition]
  rfl

theorem finite_halting_iff (machine : TM0.Machine Γ Q) (state : TM0.Cfg Γ Q) :
    ((finiteProgram machine).eval (finiteIota machine state)).Dom ↔
      (StateTransition.eval (TM0.step machine) state).Dom := by
  rw [finite_eval_iota]
  rfl

theorem finite_divergence_iff (machine : TM0.Machine Γ Q) (state : TM0.Cfg Γ Q) :
    ¬ ((finiteProgram machine).eval (finiteIota machine state)).Dom ↔
      ¬ (StateTransition.eval (TM0.step machine) state).Dom :=
  not_congr (finite_halting_iff machine state)

end FiniteTypes

end Monodromy.NativeTuring

namespace Monodromy.NativeTuring

open Turing CoupledContinuation

section Marking

variable {m : ℕ} [NeZero m]

/-- A static finite table marks selected phase-zero source addresses. -/
def markTable (mark : Fin m → Bool) (index : Fin (m * 3)) : Bool :=
  let address := finProdFinEquiv.symm index
  if address.2 = 0 then mark address.1 else false

/-- Only the stopping table changes; every actual geometric word is retained. -/
def markedProgram (source : Counter.Program 2 m) (mark : Fin m → Bool) : Program (m * 3) :=
  ⟨(CounterContinuation.compile source).table, markTable mark⟩

/-- The boundary is an actual analytic finite-root observation of the native state. -/
def MarkedBoundary (source : Counter.Program 2 m) (mark : Fin m → Bool) (state : Memory) : Prop :=
  (markedProgram source mark).haltSignal state = 1

@[simp] theorem markedProgram_advance (source : Counter.Program 2 m) (mark : Fin m → Bool)
    (state : Memory) :
    (markedProgram source mark).advance state = (CounterContinuation.compile source).advance state := rfl

theorem markedBoundary_label_iff (source : Counter.Program 2 m) (mark : Fin m → Bool)
    (position : Fin m) (phase : Fin 3) (left right : ℤ) :
    MarkedBoundary source mark (prepare left right (CounterContinuation.label position phase)) ↔
      phase = 0 ∧ mark position = true := by
  have signal := Program.haltSignal_prepare (markedProgram source mark) left right 0
    (finProdFinEquiv (position, phase))
  have stop_at : (markedProgram source mark).stop (finProdFinEquiv (position, phase)) =
      markTable mark (finProdFinEquiv (position, phase)) := rfl
  rw [stop_at] at signal
  have at_label : (markedProgram source mark).haltSignal
      (prepare left right (CounterContinuation.label position phase)) =
      if markTable mark (finProdFinEquiv (position, phase)) then 1 else 0 := by
    simpa only [mul_zero, zero_add, CounterContinuation.label] using signal
  unfold MarkedBoundary
  rw [at_label]
  by_cases phase_zero : phase = 0
  · cases value : mark position <;> simp [markTable, phase_zero, value]
  · simp [markTable, phase_zero]

theorem markedBoundary_encode_iff (source : Counter.Program 2 m) (mark : Fin m → Bool)
    (state : Counter.Configuration 2 m) :
    MarkedBoundary source mark (CounterContinuation.encode state) ↔ mark state.pc = true := by
  unfold CounterContinuation.encode
  rw [markedBoundary_label_iff]
  simp

private theorem advance_of_native_step (source : Counter.Program 2 m) {first last : Memory}
    (transition : (CounterContinuation.compile source).step first = some last) :
    (CounterContinuation.compile source).advance first = last := by
  unfold Program.step at transition
  split at transition
  · contradiction
  · exact Option.some.inj transition

/-- The existing intermediate native phase can never satisfy any phase-zero mark. -/
theorem two_returns_marked (source : Counter.Program 2 m) (mark : Fin m → Bool)
    (first last : Counter.Configuration 2 m) (transition : Counter.step source first = some last) :
    ∃ middle : Memory,
      (CounterContinuation.compile source).step (CounterContinuation.encode first) = some middle ∧
      ¬ MarkedBoundary source mark middle ∧
      (CounterContinuation.compile source).step middle = some (CounterContinuation.encode last) := by
  obtain ⟨middle, initial, final⟩ := CounterContinuation.two_returns source first last transition
  have live : source first.pc ≠ .halt := by
    intro halted
    simp [Counter.step, halted] at transition
  have advance := advance_of_native_step source initial
  refine ⟨middle, initial, ?_, final⟩
  rw [← advance]
  rcases CounterContinuation.advance_live_phase source first live with one | two
  · rw [one, markedBoundary_label_iff]
    simp
  · rw [two, markedBoundary_label_iff]
    simp

/-- Interior actual steps are unchanged when only the root stopping table is replaced. -/
theorem marked_step_of_original (source : Counter.Program 2 m) (mark : Fin m → Bool)
    {first last : Memory} (transition : (CounterContinuation.compile source).step first = some last)
    (interior : ¬ MarkedBoundary source mark first) :
    (markedProgram source mark).step first = some last := by
  change (if (markedProgram source mark).haltSignal first = 1 then none
    else some ((markedProgram source mark).advance first)) = some last
  change (markedProgram source mark).haltSignal first ≠ 1 at interior
  rw [ite_eq_right interior, markedProgram_advance]
  exact congrArg some (advance_of_native_step source transition)

end Marking

variable (a q : ℕ) [NeZero a] [NeZero q]

/-- This finite PC flag marks exactly nested source dispatch cells, independently of storage. -/
def CounterMarked (machine : TM0.Machine (Fin a) (Fin q))
    (cell : Fin (Counter.Compression.size (source3 a q machine))) : Prop :=
  ∃ row : Counter.TuringCompiler.Row a q,
    cell = Counter.Compression.dispatch (source3 a q machine)
      (Counter.TuringCompiler.dispatch a q row)

def counterMark (machine : TM0.Machine (Fin a) (Fin q))
    (cell : Fin (Counter.Compression.size (source3 a q machine))) : Bool :=
  @decide (CounterMarked a q machine cell) (by unfold CounterMarked; infer_instance)

def boundaryProgram (machine : TM0.Machine (Fin a) (Fin q)) :
    Program (Counter.Compression.size (source3 a q machine) * 3) :=
  markedProgram (source2 a q machine) (counterMark a q machine)

/-- No integer labels or memory tests enter the native boundary definition. -/
def Boundary (machine : TM0.Machine (Fin a) (Fin q)) (state : Memory) : Prop :=
  (boundaryProgram a q machine).haltSignal state = 1

theorem counterMarked_encode3_iff (machine : TM0.Machine (Fin a) (Fin q))
    (state : Counter.Configuration 3 (Counter.TuringCompiler.size a q)) :
    CounterMarked a q machine (Counter.Compression.encode (source3 a q machine) state).pc ↔
      Counter.TuringCompiler.Boundary a q state.pc := by
  constructor
  · rintro ⟨row, same⟩
    exact ⟨row, Counter.Compression.dispatch_injective (source3 a q machine) same⟩
  · rintro ⟨row, same⟩
    exact ⟨row, congrArg (Counter.Compression.dispatch (source3 a q machine)) same⟩

theorem counterMarked_implies_boundary (machine : TM0.Machine (Fin a) (Fin q))
    {cell : Fin (Counter.Compression.size (source3 a q machine))}
    (marked : CounterMarked a q machine cell) : Counter.Compression.Boundary (source3 a q machine) cell := by
  rcases marked with ⟨row, same⟩
  exact ⟨Counter.TuringCompiler.dispatch a q row, same⟩

theorem boundary_encode2_iff (machine : TM0.Machine (Fin a) (Fin q))
    (state : Counter.Configuration 2 (Counter.Compression.size (source3 a q machine))) :
    Boundary a q machine (CounterContinuation.encode state) ↔ CounterMarked a q machine state.pc := by
  change MarkedBoundary (source2 a q machine) (counterMark a q machine)
    (CounterContinuation.encode state) ↔ _
  rw [markedBoundary_encode_iff]
  simp [counterMark]

@[simp] theorem boundary_iota (machine : TM0.Machine (Fin a) (Fin q))
    (state : TM0.Cfg (Fin a) (Fin q)) : Boundary a q machine (iota a q machine state) := by
  rw [iota, boundary_encode2_iff, counterMarked_encode3_iff]
  exact Counter.TuringCompiler.encode_boundary a q state

/-- Proof-side interior relation for the already defined two-counter table. -/
def CounterInternalStep (machine : TM0.Machine (Fin a) (Fin q))
    (first last : Counter.Configuration 2 (Counter.Compression.size (source3 a q machine))) : Prop :=
  Counter.step (source2 a q machine) first = some last ∧ ¬ CounterMarked a q machine first.pc

abbrev CounterInternalReaches (machine : TM0.Machine (Fin a) (Fin q)) :=
  Relation.ReflTransGen (CounterInternalStep a q machine)

private theorem compression_internal (machine : TM0.Machine (Fin a) (Fin q))
    {first last : Counter.Configuration 2 (Counter.Compression.size (source3 a q machine))}
    (run : Counter.Compression.InternalReaches (source3 a q machine) first last) :
    CounterInternalReaches a q machine first last := by
  induction run with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ edge previous =>
      exact previous.tail ⟨edge.1, fun marked => edge.2 (counterMarked_implies_boundary a q machine marked)⟩

private theorem turing_internal_step (machine : TM0.Machine (Fin a) (Fin q))
    {first last : Counter.Configuration 3 (Counter.TuringCompiler.size a q)}
    (edge : Counter.TuringCompiler.InternalStep a q machine first last) :
    CounterInternalReaches a q machine
      (Counter.Compression.encode (source3 a q machine) first)
      (Counter.Compression.encode (source3 a q machine) last) := by
  obtain ⟨after, initial, rest⟩ := Counter.Compression.step_firstReturn (source3 a q machine) edge.1
  exact Relation.ReflTransGen.head
    ⟨initial, fun marked => edge.2 ((counterMarked_encode3_iff a q machine first).mp marked)⟩
    (compression_internal a q machine rest)

private theorem turing_internal (machine : TM0.Machine (Fin a) (Fin q))
    {first last : Counter.Configuration 3 (Counter.TuringCompiler.size a q)}
    (run : Counter.TuringCompiler.InternalReaches a q machine first last) :
    CounterInternalReaches a q machine
      (Counter.Compression.encode (source3 a q machine) first)
      (Counter.Compression.encode (source3 a q machine) last) := by
  induction run with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ edge previous => exact previous.trans (turing_internal_step a q machine edge)

/-- Nested source compilation has a positive first return to exactly the marked finite PCs. -/
theorem counter_firstReturn (machine : TM0.Machine (Fin a) (Fin q))
    {first last : TM0.Cfg (Fin a) (Fin q)} (transition : TM0.step machine first = some last) :
    ∃ after,
      Counter.step (source2 a q machine)
        (Counter.Compression.encode (source3 a q machine) (Counter.TuringCompiler.encode a q first)) =
          some after ∧
      CounterInternalReaches a q machine after
        (Counter.Compression.encode (source3 a q machine) (Counter.TuringCompiler.encode a q last)) := by
  obtain ⟨after3, initial3, rest3⟩ := Counter.TuringCompiler.step_firstReturn a q machine transition
  obtain ⟨after2, initial2, rest2⟩ := Counter.Compression.step_firstReturn (source3 a q machine) initial3
  exact ⟨after2, initial2,
    (compression_internal a q machine rest2).trans (turing_internal a q machine rest3)⟩

/-- The native words execute unchanged; only the geometric boundary mark is excluded internally. -/
def InternalStep (machine : TM0.Machine (Fin a) (Fin q)) (first last : Memory) : Prop :=
  (program a q machine).step first = some last ∧ ¬ Boundary a q machine first

abbrev InternalReaches (machine : TM0.Machine (Fin a) (Fin q)) :=
  Relation.ReflTransGen (InternalStep a q machine)

private theorem native_counter_internal_step (machine : TM0.Machine (Fin a) (Fin q))
    {first last : Counter.Configuration 2 (Counter.Compression.size (source3 a q machine))}
    (edge : CounterInternalStep a q machine first last) :
    InternalReaches a q machine (CounterContinuation.encode first) (CounterContinuation.encode last) := by
  obtain ⟨middle, initial, middle_unmarked, final⟩ :=
    two_returns_marked (source2 a q machine) (counterMark a q machine) first last edge.1
  have first_unmarked : ¬ Boundary a q machine (CounterContinuation.encode first) := by
    intro marked
    exact edge.2 ((boundary_encode2_iff a q machine first).mp marked)
  exact Relation.ReflTransGen.head ⟨initial, first_unmarked⟩
    (Relation.ReflTransGen.single ⟨final, middle_unmarked⟩)

private theorem native_counter_internal (machine : TM0.Machine (Fin a) (Fin q))
    {first last : Counter.Configuration 2 (Counter.Compression.size (source3 a q machine))}
    (run : CounterInternalReaches a q machine first last) :
    InternalReaches a q machine (CounterContinuation.encode first) (CounterContinuation.encode last) := by
  induction run with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ edge previous => exact previous.trans (native_counter_internal_step a q machine edge)

/-- One actual native step, followed only by actual steps whose sources are unmarked. -/
def FirstReturn (machine : TM0.Machine (Fin a) (Fin q)) (first last : Memory) : Prop :=
  ∃ after, (program a q machine).step first = some after ∧ InternalReaches a q machine after last

/-- Every live TM step is exactly the first return to the analytic native boundary. -/
theorem step_firstReturn (machine : TM0.Machine (Fin a) (Fin q))
    {first last : TM0.Cfg (Fin a) (Fin q)} (transition : TM0.step machine first = some last) :
    FirstReturn a q machine (iota a q machine first) (iota a q machine last) := by
  obtain ⟨after2, initial2, rest2⟩ := counter_firstReturn a q machine transition
  obtain ⟨middle, initial, middle_unmarked, final⟩ :=
    two_returns_marked (source2 a q machine) (counterMark a q machine) _ _ initial2
  exact ⟨middle, initial, Relation.ReflTransGen.head ⟨final, middle_unmarked⟩
    (native_counter_internal a q machine rest2)⟩

theorem internal_from_boundary (machine : TM0.Machine (Fin a) (Fin q))
    {first last : Memory} (run : InternalReaches a q machine first last)
    (marked : Boundary a q machine first) : first = last := by
  rcases Relation.ReflTransGen.cases_head run with same | ⟨next, edge, _⟩
  · exact same
  · exact False.elim (edge.2 marked)

/-- Interior execution is the same actual word-table execution under the boundary stop table. -/
theorem internal_marked_reaches (machine : TM0.Machine (Fin a) (Fin q))
    {first last : Memory} (run : InternalReaches a q machine first last) :
    StateTransition.Reaches (boundaryProgram a q machine).step first last := by
  induction run with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ edge previous =>
      exact previous.tail (marked_step_of_original (source2 a q machine) (counterMark a q machine)
        edge.1 edge.2)

private theorem boundary_stops (machine : TM0.Machine (Fin a) (Fin q))
    {state : Memory} (marked : Boundary a q machine state) :
    (boundaryProgram a q machine).step state = none := by
  change (boundaryProgram a q machine).haltSignal state = 1 at marked
  simp only [Program.step, ite_eq_left marked]

/-- Leave the current return once, then execute the same words until the next internal root mark.
Its inputs contain no target state, decoded integer labels, or source transition oracle. -/
def macroStep (machine : TM0.Machine (Fin a) (Fin q)) (state : Memory) : Part (Option Memory) :=
  match (program a q machine).step state with
  | none => Part.some none
  | some next => ((boundaryProgram a q machine).eval next).map some

/-- The causally executed native first-return macro is the exact total TM step on encoded states. -/
theorem macroStep_iota (machine : TM0.Machine (Fin a) (Fin q)) (state : TM0.Cfg (Fin a) (Fin q)) :
    macroStep a q machine (iota a q machine state) =
      Part.some ((TM0.step machine state).map (iota a q machine)) := by
  cases transition : TM0.step machine state with
  | none =>
      rw [macroStep, step_halt a q machine state transition]
      rfl
  | some next =>
      obtain ⟨after, initial, interior⟩ := step_firstReturn a q machine transition
      have completed : (boundaryProgram a q machine).eval after = Part.some (iota a q machine next) := by
        apply Part.eq_some_iff.mpr
        exact StateTransition.mem_eval.mpr
          ⟨internal_marked_reaches a q machine interior, boundary_stops a q machine (boundary_iota a q machine next)⟩
      simp only [macroStep, initial, completed, Part.map_some, Option.map_some]


section FiniteTypes

variable {Γ Q : Type} [Fintype Γ] [Inhabited Γ] [Fintype Q] [Inhabited Q]

/-- The same first-return execution under pointed finite source renaming. -/
def finiteMacro (machine : TM0.Machine Γ Q) (state : Memory) : Part (Option Memory) :=
  macroStep (Fintype.card Γ) (Fintype.card Q) (FiniteRenaming.machine machine) state

theorem finiteMacro_iota (machine : TM0.Machine Γ Q) (state : TM0.Cfg Γ Q) :
    finiteMacro machine (finiteIota machine state) =
      Part.some ((TM0.step machine state).map (finiteIota machine)) := by
  unfold finiteMacro finiteIota
  rw [macroStep_iota, ← FiniteRenaming.step_configuration, Option.map_map]
  rfl

end FiniteTypes

/-- A finite native simulation certificate. The generated prefixes are the actual two matching
cover lifts identified by `Program.runDriver_actual_lifts`. -/
theorem native_universality (machine : TM0.Machine (Fin a) (Fin q)) :
    Function.Injective (iota a q machine) ∧
    (∀ state, (program a q machine).eval (iota a q machine state) =
      iota a q machine <$> StateTransition.eval (TM0.step machine) state) ∧
    (∀ state, macroStep a q machine (iota a q machine state) =
      Part.some ((TM0.step machine state).map (iota a q machine))) ∧
    (∀ first last, StateTransition.Reaches (TM0.step machine) first last →
      ∃ count : ℕ,
        restrictedTrajectory ((program a q machine).runDriver count (iota a q machine first))
          (iota a q machine first) 1 = restrictedState (iota a q machine last)) :=
  ⟨iota_injective a q machine, eval_iota a q machine, macroStep_iota a q machine,
    fun _ _ run => finite_run_path a q machine run⟩

end Monodromy.NativeTuring
