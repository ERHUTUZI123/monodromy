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

/-!
## Universal simulation with recoverable history

The ordinary two-counter compilation supplies only the source to be made
reversible. A fixed finite recording graph executes it, retaining the complete
configuration and history. Its four source registers are a proof intermediate;
reversibility-preserving compression to two native memory roots is separate.
-/

namespace Monodromy.RecordedTuring

open Turing

noncomputable section

variable (a q : ℕ) [NeZero a] [NeZero q]

abbrev size (machine : TM0.Machine (Fin a) (Fin q)) : ℕ :=
  Counter.Compression.size (NativeTuring.source3 a q machine)

def counterEncode (machine : TM0.Machine (Fin a) (Fin q))
    (state : TM0.Cfg (Fin a) (Fin q)) : Counter.Configuration 2 (size a q machine) :=
  Counter.Compression.encode (NativeTuring.source3 a q machine)
    (Counter.TuringCompiler.encode a q state)

theorem counterEncode_injective (machine : TM0.Machine (Fin a) (Fin q)) :
    Function.Injective (counterEncode a q machine) :=
  (Counter.Compression.encode_injective (NativeTuring.source3 a q machine)).comp
    (Counter.TuringCompiler.encode_injective a q)

theorem counter_halt (machine : TM0.Machine (Fin a) (Fin q))
    (state : TM0.Cfg (Fin a) (Fin q)) (halted : TM0.step machine state = none) :
    Counter.step (NativeTuring.source2 a q machine) (counterEncode a q machine state) = none := by
  have first := (Counter.TuringCompiler.halt_encode a q machine state).mpr halted
  exact (Counter.Compression.halt_encode (NativeTuring.source3 a q machine)
    (Counter.TuringCompiler.encode a q state)).mpr first

end

end Monodromy.RecordedTuring

namespace Monodromy.ReversibleTuring

open Turing

noncomputable section

variable (a q : ℕ) [NeZero a] [NeZero q]

/-- A fixed finite reversible graph realizes the source; its four registers are an intermediate code. -/
def table (machine : TM0.Machine (Fin a) (Fin q)) :
    Counter.Reversible.Table 4
      (Counter.Reversible.Recording.size (RecordedTuring.size a q machine))
      (Counter.Reversible.Recording.edges (NativeTuring.source2 a q machine)) :=
  Counter.Reversible.Recording.table (NativeTuring.source2 a q machine)

def encode (machine : TM0.Machine (Fin a) (Fin q))
    (state : TM0.Cfg (Fin a) (Fin q)) (history : ℕ) :
    Counter.Reversible.State 4
      (Counter.Reversible.Recording.size (RecordedTuring.size a q machine)) :=
  Counter.Reversible.Recording.encode (RecordedTuring.counterEncode a q machine state) history

/-- At every simulated boundary the history is retained and its working register is zero. -/
theorem boundary_storage (machine : TM0.Machine (Fin a) (Fin q))
    (state : TM0.Cfg (Fin a) (Fin q)) (history : ℕ) :
    ((encode a q machine state history).2 (Counter.Reversible.Recording.historyRegister 2 0),
      (encode a q machine state history).2 (Counter.Reversible.Recording.historyRegister 2 1)) =
        ((history : ℤ), 0) := by
  simp only [encode, Counter.Reversible.Recording.encode, Counter.Reversible.Recording.framed,
    Counter.Reversible.Recording.frame_history, Counter.Reversible.Recording.frame_workspace]

theorem encode_injective (machine : TM0.Machine (Fin a) (Fin q)) :
    Function.Injective (fun pair : TM0.Cfg (Fin a) (Fin q) × ℕ =>
      encode a q machine pair.1 pair.2) := by
  intro first second same
  have logged : (RecordedTuring.counterEncode a q machine first.1, first.2) =
      (RecordedTuring.counterEncode a q machine second.1, second.2) := by
    apply Counter.Reversible.Recording.embed_injective
    exact same
  exact Prod.ext
    (RecordedTuring.counterEncode_injective a q machine (congrArg Prod.fst logged))
    (congrArg (fun state : Counter.Recorded.State 2 (RecordedTuring.size a q machine) => state.2) logged)

/-- Every defined graph step has a unique predecessor, including states outside the encoded domain. -/
theorem defined_step_injective (machine : TM0.Machine (Fin a) (Fin q))
    {first second last : Counter.Reversible.State 4
      (Counter.Reversible.Recording.size (RecordedTuring.size a q machine))}
    (left : Counter.Reversible.step (table a q machine) first = some last)
    (right : Counter.Reversible.step (table a q machine) second = some last) : first = second :=
  Counter.Reversible.step_some_injective (table a q machine)
    (Counter.Reversible.Recording.deterministic (NativeTuring.source2 a q machine))
    (Counter.Reversible.Recording.targetCompatible (NativeTuring.source2 a q machine)) left right

/-- The compiled machine's finite dispatch marks are lifted to recording ports. -/
def Boundary (machine : TM0.Machine (Fin a) (Fin q))
    (state : Counter.Reversible.State 4
      (Counter.Reversible.Recording.size (RecordedTuring.size a q machine))) : Prop :=
  Counter.Reversible.Recording.Marked (NativeTuring.counterMark a q machine) state

instance boundary_decidable (machine : TM0.Machine (Fin a) (Fin q))
    (state : Counter.Reversible.State 4
      (Counter.Reversible.Recording.size (RecordedTuring.size a q machine))) :
    Decidable (Boundary a q machine state) := by
  unfold Boundary
  infer_instance

private theorem source_marked (machine : TM0.Machine (Fin a) (Fin q))
    (state : TM0.Cfg (Fin a) (Fin q)) :
    NativeTuring.counterMark a q machine (RecordedTuring.counterEncode a q machine state).pc = true := by
  unfold RecordedTuring.counterEncode NativeTuring.counterMark
  exact @decide_eq_true _ (by unfold NativeTuring.CounterMarked; infer_instance)
    ((NativeTuring.counterMarked_encode3_iff a q machine
    (Counter.TuringCompiler.encode a q state)).mpr
      (Counter.TuringCompiler.encode_boundary a q state))

theorem boundary_encode (machine : TM0.Machine (Fin a) (Fin q))
    (state : TM0.Cfg (Fin a) (Fin q)) (history : ℕ) :
    Boundary a q machine (encode a q machine state history) :=
  (Counter.Reversible.Recording.marked_encode_iff (NativeTuring.counterMark a q machine)
    (RecordedTuring.counterEncode a q machine state) history).mpr (source_marked a q machine state)

/-- A live Turing step is the first positive return to its finite marked dispatches. -/
theorem step_firstReturn (machine : TM0.Machine (Fin a) (Fin q))
    {first last : TM0.Cfg (Fin a) (Fin q)} (transition : TM0.step machine first = some last)
    (history : ℕ) :
    ∃ finalHistory, history < finalHistory ∧
      Counter.Reversible.Recording.MarkedFirstReturn (NativeTuring.source2 a q machine)
        (NativeTuring.counterMark a q machine)
        (encode a q machine first history) (encode a q machine last finalHistory) := by
  obtain ⟨middle, initial, rest⟩ := NativeTuring.counter_firstReturn a q machine transition
  have internal : Relation.ReflTransGen
      (fun current next : Counter.Configuration 2 (RecordedTuring.size a q machine) =>
        Counter.step (NativeTuring.source2 a q machine) current = some next ∧
          NativeTuring.counterMark a q machine current.pc = false)
      middle (RecordedTuring.counterEncode a q machine last) := by
    refine Relation.ReflTransGen.mono (r := NativeTuring.CounterInternalStep a q machine)
      (fun current next edge => ?_) _ _ rest
    exact ⟨edge.1, by simpa only
      [NativeTuring.counterMark, decide_eq_false_iff_not] using edge.2⟩
  exact Counter.Reversible.Recording.marked_firstReturn (NativeTuring.source2 a q machine)
    (NativeTuring.counterMark a q machine) initial internal
    (source_marked a q machine first) (source_marked a q machine last) history

/-- Each live Turing step runs the fixed graph and leaves a larger recoverable history. -/
theorem step_reaches (machine : TM0.Machine (Fin a) (Fin q))
    {first last : TM0.Cfg (Fin a) (Fin q)} (transition : TM0.step machine first = some last)
    (history : ℕ) :
    ∃ finalHistory, history < finalHistory ∧
      StateTransition.Reaches₁ (Counter.Reversible.step (table a q machine))
        (encode a q machine first history) (encode a q machine last finalHistory) := by
  obtain ⟨finalHistory, grew, _, _, next, initial, interior⟩ :=
    step_firstReturn a q machine transition history
  exact ⟨finalHistory, grew, Relation.TransGen.head' initial
    (Relation.ReflTransGen.mono (fun _ _ edge => edge.1) _ _ interior)⟩

theorem step_halt (machine : TM0.Machine (Fin a) (Fin q))
    (state : TM0.Cfg (Fin a) (Fin q)) (history : ℕ) (halted : TM0.step machine state = none) :
    Counter.Reversible.step (table a q machine) (encode a q machine state history) = none :=
  (Counter.Reversible.Recording.step_encode_none_iff (NativeTuring.source2 a q machine)
    (RecordedTuring.counterEncode a q machine state) history).mpr
      (RecordedTuring.counter_halt a q machine state halted)

/-- The same graph is stopped at the chosen finite dispatch marks. -/
def boundaryTransition (machine : TM0.Machine (Fin a) (Fin q))
    (state : Counter.Reversible.State 4
      (Counter.Reversible.Recording.size (RecordedTuring.size a q machine))) :=
  if Boundary a q machine state then none else Counter.Reversible.step (table a q machine) state

private theorem boundaryTransition_stops (machine : TM0.Machine (Fin a) (Fin q))
    {state : Counter.Reversible.State 4
      (Counter.Reversible.Recording.size (RecordedTuring.size a q machine))}
    (marked : Boundary a q machine state) : boundaryTransition a q machine state = none := by
  simp only [boundaryTransition, ite_eq_left marked]

private theorem internal_marked_reaches (machine : TM0.Machine (Fin a) (Fin q))
    {first last : Counter.Reversible.State 4
      (Counter.Reversible.Recording.size (RecordedTuring.size a q machine))}
    (run : Counter.Reversible.Recording.InternalMarkedReaches
      (NativeTuring.source2 a q machine) (NativeTuring.counterMark a q machine) first last) :
    StateTransition.Reaches (boundaryTransition a q machine) first last := by
  induction run with
  | refl => exact Relation.ReflTransGen.refl
  | @tail first last _ edge previous =>
      apply previous.tail
      change (if Boundary a q machine first then none
        else Counter.Reversible.step (table a q machine) first) = some last
      have unmarked : ¬ Boundary a q machine first := edge.2
      rw [ite_eq_right unmarked]
      exact edge.1

/-- Execute the fixed graph once, then stop it at a finite control mark or a graph dead end. -/
def macroStep (machine : TM0.Machine (Fin a) (Fin q))
    (state : Counter.Reversible.State 4
      (Counter.Reversible.Recording.size (RecordedTuring.size a q machine))) :
    Part (Option (Counter.Reversible.State 4
      (Counter.Reversible.Recording.size (RecordedTuring.size a q machine)))) :=
  match Counter.Reversible.step (table a q machine) state with
  | none => Part.some none
  | some next => (StateTransition.eval (boundaryTransition a q machine) next).map some

theorem macroStep_halt (machine : TM0.Machine (Fin a) (Fin q))
    (state : TM0.Cfg (Fin a) (Fin q)) (history : ℕ) (halted : TM0.step machine state = none) :
    macroStep a q machine (encode a q machine state history) = Part.some none := by
  rw [macroStep, step_halt a q machine state history halted]

/-- The causal marked-return evaluator executes exactly the source step, retaining its new history. -/
theorem macroStep_live (machine : TM0.Machine (Fin a) (Fin q))
    {first last : TM0.Cfg (Fin a) (Fin q)} (transition : TM0.step machine first = some last)
    (history : ℕ) :
    ∃ finalHistory, history < finalHistory ∧
      macroStep a q machine (encode a q machine first history) =
        Part.some (some (encode a q machine last finalHistory)) := by
  obtain ⟨finalHistory, grew, _, marked, next, initial, rest⟩ :=
    step_firstReturn a q machine transition history
  have completed : StateTransition.eval (boundaryTransition a q machine) next =
      Part.some (encode a q machine last finalHistory) := by
    apply Part.eq_some_iff.mpr
    exact StateTransition.mem_eval.mpr
      ⟨internal_marked_reaches a q machine rest, boundaryTransition_stops a q machine marked⟩
  refine ⟨finalHistory, grew, ?_⟩
  change Counter.Reversible.step (table a q machine) (encode a q machine first history) =
    some next at initial
  simp only [macroStep, initial, completed, Part.map_some]

/-- The optional source result and full recorded configuration agree under the defined graph macro. -/
theorem macroStep_encode (machine : TM0.Machine (Fin a) (Fin q))
    (state : TM0.Cfg (Fin a) (Fin q)) (history : ℕ) :
    ∃ finalHistory,
      macroStep a q machine (encode a q machine state history) =
        Part.some ((TM0.step machine state).map (fun next => encode a q machine next finalHistory)) ∧
      (TM0.step machine state ≠ none → history < finalHistory) := by
  cases transition : TM0.step machine state with
  | none =>
      refine ⟨history, ?_, ?_⟩
      · simpa only [transition, Option.map_none] using macroStep_halt a q machine state history transition
      · simp
  | some next =>
      obtain ⟨finalHistory, grew, result⟩ := macroStep_live a q machine transition history
      exact ⟨finalHistory, result, fun _ => grew⟩

def Related (machine : TM0.Machine (Fin a) (Fin q))
    (original : TM0.Cfg (Fin a) (Fin q))
    (compiled : Counter.Reversible.State 4
      (Counter.Reversible.Recording.size (RecordedTuring.size a q machine))) : Prop :=
  ∃ history, encode a q machine original history = compiled

theorem respects (machine : TM0.Machine (Fin a) (Fin q)) :
    StateTransition.Respects (TM0.step machine) (Counter.Reversible.step (table a q machine))
      (Related a q machine) := by
  intro original compiled related
  obtain ⟨history, rfl⟩ := related
  cases transition : TM0.step machine original with
  | none => exact step_halt a q machine original history transition
  | some next =>
      obtain ⟨finalHistory, _, run⟩ := step_reaches a q machine transition history
      exact ⟨encode a q machine next finalHistory, ⟨finalHistory, rfl⟩, run⟩

theorem halting_iff (machine : TM0.Machine (Fin a) (Fin q))
    (state : TM0.Cfg (Fin a) (Fin q)) (history : ℕ) :
    (Counter.Reversible.eval (table a q machine) (encode a q machine state history)).Dom ↔
      (StateTransition.eval (TM0.step machine) state).Dom :=
  StateTransition.tr_eval_dom (respects a q machine) ⟨history, rfl⟩

theorem divergence_iff (machine : TM0.Machine (Fin a) (Fin q))
    (state : TM0.Cfg (Fin a) (Fin q)) (history : ℕ) :
    ¬ (Counter.Reversible.eval (table a q machine) (encode a q machine state history)).Dom ↔
      ¬ (StateTransition.eval (TM0.step machine) state).Dom :=
  not_congr (halting_iff a q machine state history)

/-- The entire final Turing configuration is retained, while the terminal history remains observable. -/
theorem result_iff (machine : TM0.Machine (Fin a) (Fin q))
    (first last : TM0.Cfg (Fin a) (Fin q)) (history : ℕ) :
    (∃ finalHistory, encode a q machine last finalHistory ∈
      Counter.Reversible.eval (table a q machine) (encode a q machine first history)) ↔
      last ∈ StateTransition.eval (TM0.step machine) first := by
  constructor
  · rintro ⟨finalHistory, finished⟩
    obtain ⟨source, ⟨sourceHistory, related⟩, source_finished⟩ :=
      StateTransition.tr_eval_rev (respects a q machine) ⟨history, rfl⟩ finished
    have same : (source, sourceHistory) = (last, finalHistory) :=
      @encode_injective a q _ _ machine (source, sourceHistory) (last, finalHistory) related
    have configurations : source = last := congrArg Prod.fst same
    simpa only [configurations] using source_finished
  · intro source_finished
    obtain ⟨final, ⟨finalHistory, rfl⟩, finished⟩ :=
      StateTransition.tr_eval (respects a q machine) ⟨history, rfl⟩ source_finished
    exact ⟨finalHistory, finished⟩

/-- Reverse execution is generated by the reversed finite graph rather than by a supplied trace. -/
theorem step_retraces (machine : TM0.Machine (Fin a) (Fin q))
    {first last : TM0.Cfg (Fin a) (Fin q)} (transition : TM0.step machine first = some last)
    (history : ℕ) :
    ∃ finalHistory, history < finalHistory ∧
      StateTransition.Reaches
        (Counter.Reversible.step (Counter.Reversible.reverseTable (table a q machine)))
        (encode a q machine last finalHistory) (encode a q machine first history) := by
  obtain ⟨finalHistory, grew, run⟩ := step_reaches a q machine transition history
  refine ⟨finalHistory, grew, ?_⟩
  exact Counter.Reversible.reaches_reverse (table a q machine)
    (Counter.Reversible.Recording.deterministic (NativeTuring.source2 a q machine))
    (Counter.Reversible.Recording.targetCompatible (NativeTuring.source2 a q machine)) run.to_reflTransGen

end

end Monodromy.ReversibleTuring

/-!
## Recoverable-history simulation on two counters
-/

noncomputable section

namespace Monodromy.ReversibleTuring.Compression

open Turing Counter.Reversible

/-- Four source registers use one instance of the uniform finite prime code. -/
def basis : PrimeCode.Basis 4 where
  prime := ![2, 3, 5, 7]
  isPrime := by intro index; fin_cases index <;> decide
  distinct := by
    intro first second same
    fin_cases first <;> fin_cases second <;> simp_all

variable (a q : ℕ) [NeZero a] [NeZero q]

theorem source_deterministic (machine : TM0.Machine (Fin a) (Fin q)) :
    Deterministic (ReversibleTuring.table a q machine) :=
  Recording.deterministic (NativeTuring.source2 a q machine)

theorem source_targetCompatible (machine : TM0.Machine (Fin a) (Fin q)) :
    TargetCompatible (ReversibleTuring.table a q machine) :=
  Recording.targetCompatible (NativeTuring.source2 a q machine)

abbrev size (machine : TM0.Machine (Fin a) (Fin q)) : ℕ :=
  PrimeCompression.size basis (ReversibleTuring.table a q machine)
    (source_deterministic a q machine) (source_targetCompatible a q machine)

abbrev edges (machine : TM0.Machine (Fin a) (Fin q)) : ℕ :=
  PrimeCompression.rawEdges basis (ReversibleTuring.table a q machine)

/-- A fixed finite graph on two counters, with no source-step interpreter in its definition. -/
def table (machine : TM0.Machine (Fin a) (Fin q)) : Table 2 (size a q machine) (edges a q machine) :=
  PrimeCompression.table basis (ReversibleTuring.table a q machine)
    (source_deterministic a q machine) (source_targetCompatible a q machine)

/-- The entire source configuration and its recoverable history are retained. -/
def encode (machine : TM0.Machine (Fin a) (Fin q))
    (state : TM0.Cfg (Fin a) (Fin q)) (history : ℕ) : State 2 (size a q machine) :=
  PrimeCompression.encode basis (ReversibleTuring.table a q machine)
    (source_deterministic a q machine) (source_targetCompatible a q machine)
    (PrimeCompression.toNatural (ReversibleTuring.encode a q machine state history))

theorem deterministic (machine : TM0.Machine (Fin a) (Fin q)) :
    Deterministic (table a q machine) :=
  PrimeCompression.deterministic basis (ReversibleTuring.table a q machine)
    (source_deterministic a q machine) (source_targetCompatible a q machine)

theorem targetCompatible (machine : TM0.Machine (Fin a) (Fin q)) :
    TargetCompatible (table a q machine) :=
  PrimeCompression.targetCompatible basis (ReversibleTuring.table a q machine)
    (source_deterministic a q machine) (source_targetCompatible a q machine)

private theorem source_nonnegative (machine : TM0.Machine (Fin a) (Fin q))
    (state : TM0.Cfg (Fin a) (Fin q)) (history : ℕ) :
    ∀ index, 0 ≤ (ReversibleTuring.encode a q machine state history).2 index := by
  intro index
  exact Recording.encode_reaches_nonnegative (NativeTuring.source2 a q machine)
    (RecordedTuring.counterEncode a q machine state) history Relation.ReflTransGen.refl index

theorem encode_injective (machine : TM0.Machine (Fin a) (Fin q)) :
    Function.Injective (fun pair : TM0.Cfg (Fin a) (Fin q) × ℕ =>
      encode a q machine pair.1 pair.2) := by
  intro first second same
  have natural := PrimeCompression.encode_injective basis (ReversibleTuring.table a q machine)
    (source_deterministic a q machine) (source_targetCompatible a q machine) same
  have original := congrArg PrimeCompression.naturalState natural
  rw [PrimeCompression.naturalState_toNatural _ (source_nonnegative a q machine first.1 first.2),
    PrimeCompression.naturalState_toNatural _ (source_nonnegative a q machine second.1 second.2)] at original
  exact ReversibleTuring.encode_injective a q machine original

/-- Local reversibility holds on every integer state of the compressed graph. -/
theorem defined_step_injective (machine : TM0.Machine (Fin a) (Fin q))
    {first second last : State 2 (size a q machine)}
    (left : step (table a q machine) first = some last)
    (right : step (table a q machine) second = some last) : first = second :=
  step_some_injective (table a q machine) (deterministic a q machine)
    (targetCompatible a q machine) left right

/-- The original recording boundary depends only on its finite control position. -/
def sourceMark (machine : TM0.Machine (Fin a) (Fin q))
    (position : Fin (Recording.size (RecordedTuring.size a q machine))) : Bool :=
  decide (Recording.Marked (n := 2) (NativeTuring.counterMark a q machine)
    (position, fun _ => 0))

theorem sourceMark_true_iff (machine : TM0.Machine (Fin a) (Fin q))
    (state : State 4 (Recording.size (RecordedTuring.size a q machine))) :
    sourceMark a q machine state.1 = true ↔ ReversibleTuring.Boundary a q machine state := by
  change decide (Recording.Marked (n := 2) (NativeTuring.counterMark a q machine)
    (state.1, fun _ => 0)) = true ↔
      Recording.Marked (n := 2) (NativeTuring.counterMark a q machine) (state.1, fun _ => 0)
  exact ⟨of_decide_eq_true, decide_eq_true⟩

theorem sourceMark_false_iff (machine : TM0.Machine (Fin a) (Fin q))
    (state : State 4 (Recording.size (RecordedTuring.size a q machine))) :
    sourceMark a q machine state.1 = false ↔ ¬ ReversibleTuring.Boundary a q machine state := by
  rw [← sourceMark_true_iff a q machine state]
  cases sourceMark a q machine state.1 <;> decide

/-- Marked source boundaries inside the actual compressed control graph. -/
def Boundary (machine : TM0.Machine (Fin a) (Fin q))
    (state : State 2 (size a q machine)) : Prop :=
  PrimeCompression.Marked basis (ReversibleTuring.table a q machine)
    (source_deterministic a q machine) (source_targetCompatible a q machine)
    (sourceMark a q machine) state

instance boundary_decidable (machine : TM0.Machine (Fin a) (Fin q))
    (state : State 2 (size a q machine)) : Decidable (Boundary a q machine state) := by
  unfold Boundary PrimeCompression.Marked
  refine @Fintype.decidableExistsFintype
    (Fin (Recording.size (RecordedTuring.size a q machine))) _ ?_ inferInstance
  intro position
  dsimp only
  exact @instDecidableAnd _ _ (instDecidableEqFin _ _ _) (instDecidableEqBool _ _)

/-- The marker used by a native finite-root table has no memory input. -/
def mark (machine : TM0.Machine (Fin a) (Fin q)) (position : Fin (size a q machine)) : Bool :=
  decide (Boundary a q machine (position, fun _ => 0))

theorem mark_true_iff (machine : TM0.Machine (Fin a) (Fin q))
    (state : State 2 (size a q machine)) :
    mark a q machine state.1 = true ↔ Boundary a q machine state := by
  change decide (Boundary a q machine (state.1, fun _ => 0)) = true ↔
    Boundary a q machine (state.1, fun _ => 0)
  exact ⟨of_decide_eq_true, decide_eq_true⟩

theorem mark_false_iff (machine : TM0.Machine (Fin a) (Fin q))
    (state : State 2 (size a q machine)) :
    mark a q machine state.1 = false ↔ ¬ Boundary a q machine state := by
  rw [← mark_true_iff a q machine state]
  cases mark a q machine state.1 <;> decide

theorem boundary_encode (machine : TM0.Machine (Fin a) (Fin q))
    (state : TM0.Cfg (Fin a) (Fin q)) (history : ℕ) :
    Boundary a q machine (encode a q machine state history) := by
  apply (PrimeCompression.marked_encode_iff basis (ReversibleTuring.table a q machine)
    (source_deterministic a q machine) (source_targetCompatible a q machine)
    (sourceMark a q machine) _).mpr
  exact (sourceMark_true_iff a q machine (ReversibleTuring.encode a q machine state history)).mpr
    (ReversibleTuring.boundary_encode a q machine state history)

/-- Each live Turing step reaches its next marked boundary with the same retained history. -/
theorem step_firstReturn (machine : TM0.Machine (Fin a) (Fin q))
    {first last : TM0.Cfg (Fin a) (Fin q)} (transition : TM0.step machine first = some last)
    (history : ℕ) :
    ∃ finalHistory, history < finalHistory ∧
      PrimeCompression.MarkedFirstReturn basis (ReversibleTuring.table a q machine)
        (source_deterministic a q machine) (source_targetCompatible a q machine)
        (sourceMark a q machine)
        (encode a q machine first history) (encode a q machine last finalHistory) := by
  obtain ⟨finalHistory, grew, first_marked, last_marked, middle, initial, rest⟩ :=
    ReversibleTuring.step_firstReturn a q machine transition history
  have source_rest : Relation.ReflTransGen
      (fun current next : State 4 (Recording.size (RecordedTuring.size a q machine)) =>
        step (ReversibleTuring.table a q machine) current = some next ∧
          sourceMark a q machine current.1 = false)
      middle (ReversibleTuring.encode a q machine last finalHistory) := by
    exact Relation.ReflTransGen.mono
      (fun current _ edge => ⟨edge.1, (sourceMark_false_iff a q machine current).mpr edge.2⟩)
      _ _ rest
  have first_valid : Recording.Valid (NativeTuring.source2 a q machine)
      (ReversibleTuring.encode a q machine first history) :=
    Recording.valid_encode (NativeTuring.source2 a q machine)
      (RecordedTuring.counterEncode a q machine first) history
  have actual := PrimeCompression.marked_firstReturn basis (ReversibleTuring.table a q machine)
    (source_deterministic a q machine) (source_targetCompatible a q machine)
    (Recording.unitShift (NativeTuring.source2 a q machine)) (sourceMark a q machine)
    (Recording.Valid (NativeTuring.source2 a q machine))
    (Recording.stable (NativeTuring.source2 a q machine))
    (Recording.valid_nonnegative (NativeTuring.source2 a q machine)) initial source_rest
    ((sourceMark_true_iff a q machine (ReversibleTuring.encode a q machine first history)).mpr first_marked)
    ((sourceMark_true_iff a q machine (ReversibleTuring.encode a q machine last finalHistory)).mpr last_marked)
    first_valid
  exact ⟨finalHistory, grew, actual⟩

/-- Every Turing step runs the two-counter table with the same strictly growing history. -/
theorem step_reaches (machine : TM0.Machine (Fin a) (Fin q))
    {first last : TM0.Cfg (Fin a) (Fin q)} (transition : TM0.step machine first = some last)
    (history : ℕ) :
    ∃ finalHistory, history < finalHistory ∧
      StateTransition.Reaches₁ (step (table a q machine))
        (encode a q machine first history) (encode a q machine last finalHistory) := by
  obtain ⟨finalHistory, grew, _, _, next, initial, rest⟩ :=
    step_firstReturn a q machine transition history
  exact ⟨finalHistory, grew, Relation.TransGen.head' initial
    (Relation.ReflTransGen.mono (fun _ _ edge => edge.1) _ _ rest)⟩

private theorem counter_instruction_halt {n m : ℕ} (program : Counter.Program n m)
    (state : Counter.Configuration n m) (halted : Counter.step program state = none) :
    program state.pc = .halt := by
  cases instruction : program state.pc with
  | halt => rfl
  | inc => simp [Counter.step, instruction] at halted
  | dec register zero nonzero =>
      cases value : state.counters register <;> simp [Counter.step, instruction, value] at halted

/-- A stopped Turing configuration enters a genuinely source-free recording dispatch. -/
theorem source_no_outgoing_of_halt (machine : TM0.Machine (Fin a) (Fin q))
    (state : TM0.Cfg (Fin a) (Fin q)) (history : ℕ) (halted : TM0.step machine state = none) :
    ¬ PrimeCompression.HasSource (ReversibleTuring.table a q machine)
      (PrimeCompression.toNatural (ReversibleTuring.encode a q machine state history)).pc := by
  have instruction := counter_instruction_halt (NativeTuring.source2 a q machine)
    (RecordedTuring.counterEncode a q machine state)
    (RecordedTuring.counter_halt a q machine state halted)
  rintro ⟨index, same⟩
  exact Recording.halt_no_outgoing (NativeTuring.source2 a q machine)
    (RecordedTuring.counterEncode a q machine state).pc instruction index same

/-- Static halting survives compression independently of the encoded memory values. -/
theorem no_outgoing_of_halt (machine : TM0.Machine (Fin a) (Fin q))
    (state : TM0.Cfg (Fin a) (Fin q)) (history : ℕ) (halted : TM0.step machine state = none) :
    ¬ ∃ index, (table a q machine index).source = (encode a q machine state history).1 :=
  PrimeCompression.no_outgoing_boundary basis (ReversibleTuring.table a q machine)
    (source_deterministic a q machine) (source_targetCompatible a q machine)
    (PrimeCompression.toNatural (ReversibleTuring.encode a q machine state history)).pc
    (source_no_outgoing_of_halt a q machine state history halted)

theorem step_halt (machine : TM0.Machine (Fin a) (Fin q))
    (state : TM0.Cfg (Fin a) (Fin q)) (history : ℕ) (halted : TM0.step machine state = none) :
    step (table a q machine) (encode a q machine state history) = none := by
  rw [step_none_iff]
  rintro ⟨index, enabled⟩
  exact no_outgoing_of_halt a q machine state history halted ⟨index, enabled.1⟩

def Related (machine : TM0.Machine (Fin a) (Fin q))
    (original : TM0.Cfg (Fin a) (Fin q)) (compiled : State 2 (size a q machine)) : Prop :=
  ∃ history, encode a q machine original history = compiled

theorem respects (machine : TM0.Machine (Fin a) (Fin q)) :
    StateTransition.Respects (TM0.step machine) (step (table a q machine)) (Related a q machine) := by
  intro original compiled related
  obtain ⟨history, rfl⟩ := related
  cases transition : TM0.step machine original with
  | none => exact step_halt a q machine original history transition
  | some next =>
      obtain ⟨finalHistory, _, run⟩ := step_reaches a q machine transition history
      exact ⟨encode a q machine next finalHistory, ⟨finalHistory, rfl⟩, run⟩

theorem halting_iff (machine : TM0.Machine (Fin a) (Fin q))
    (state : TM0.Cfg (Fin a) (Fin q)) (history : ℕ) :
    (eval (table a q machine) (encode a q machine state history)).Dom ↔
      (StateTransition.eval (TM0.step machine) state).Dom :=
  StateTransition.tr_eval_dom (respects a q machine) ⟨history, rfl⟩

theorem divergence_iff (machine : TM0.Machine (Fin a) (Fin q))
    (state : TM0.Cfg (Fin a) (Fin q)) (history : ℕ) :
    ¬ (eval (table a q machine) (encode a q machine state history)).Dom ↔
      ¬ (StateTransition.eval (TM0.step machine) state).Dom :=
  not_congr (halting_iff a q machine state history)

/-- Complete final configurations, including their retained history, correspond exactly. -/
theorem result_iff (machine : TM0.Machine (Fin a) (Fin q))
    (first last : TM0.Cfg (Fin a) (Fin q)) (history : ℕ) :
    (∃ finalHistory, encode a q machine last finalHistory ∈
      eval (table a q machine) (encode a q machine first history)) ↔
      last ∈ StateTransition.eval (TM0.step machine) first := by
  constructor
  · rintro ⟨finalHistory, finished⟩
    obtain ⟨original, ⟨originalHistory, related⟩, source_finished⟩ :=
      StateTransition.tr_eval_rev (respects a q machine) ⟨history, rfl⟩ finished
    have same : (original, originalHistory) = (last, finalHistory) :=
      @encode_injective a q _ _ machine (original, originalHistory) (last, finalHistory) related
    have configurations : original = last := congrArg Prod.fst same
    simpa only [configurations] using source_finished
  · intro source_finished
    obtain ⟨final, ⟨finalHistory, rfl⟩, finished⟩ :=
      StateTransition.tr_eval (respects a q machine) ⟨history, rfl⟩ source_finished
    exact ⟨finalHistory, finished⟩

/-- Reversing the same finite graph restores the entire prior configuration and history. -/
theorem step_retraces (machine : TM0.Machine (Fin a) (Fin q))
    {first last : TM0.Cfg (Fin a) (Fin q)} (transition : TM0.step machine first = some last)
    (history : ℕ) :
    ∃ finalHistory, history < finalHistory ∧
      StateTransition.Reaches (step (reverseTable (table a q machine)))
        (encode a q machine last finalHistory) (encode a q machine first history) := by
  obtain ⟨finalHistory, grew, run⟩ := step_reaches a q machine transition history
  exact ⟨finalHistory, grew, reaches_reverse (table a q machine)
    (deterministic a q machine) (targetCompatible a q machine) run.to_reflTransGen⟩

end Monodromy.ReversibleTuring.Compression

end

/-!
## Reversible universality by actual path lifting
-/

noncomputable section

namespace Monodromy.ReversibleNativeTuring

open Turing CoupledContinuation ReversibleTuring

variable (a q : ℕ) [NeZero a] [NeZero q]

instance size_nonzero (machine : TM0.Machine (Fin a) (Fin q)) :
    NeZero (Compression.size a q machine) := by
  constructor
  have bound := (Compression.encode a q machine (TM0.init [] : TM0.Cfg (Fin a) (Fin q)) 0).1.isLt
  omega

/-- The same five geometric primitives execute the complete compressed finite table. -/
def program (machine : TM0.Machine (Fin a) (Fin q)) :
    Program (11 * (Compression.size a q machine + Compression.edges a q machine)) :=
  ReversibleCompilation.haltingProgram (Compression.table a q machine)
    (Compression.deterministic a q machine) (Compression.targetCompatible a q machine)

/-- Complete source configurations and histories occupy the original three-root fiber. -/
def iota (machine : TM0.Machine (Fin a) (Fin q))
    (state : TM0.Cfg (Fin a) (Fin q)) (history : ℕ) : Memory :=
  ReversibleCompilation.iota (e := Compression.edges a q machine) (Compression.encode a q machine state history)

theorem iota_injective (machine : TM0.Machine (Fin a) (Fin q)) :
    Function.Injective (fun pair : TM0.Cfg (Fin a) (Fin q) × ℕ =>
      iota a q machine pair.1 pair.2) := by
  intro first second same
  apply Compression.encode_injective a q machine
  exact ReversibleCompilation.iota_injective same

/-- The same native words, with finite root marks for complete Turing steps. -/
def boundaryProgram (machine : TM0.Machine (Fin a) (Fin q)) :
    Program (11 * (Compression.size a q machine + Compression.edges a q machine)) :=
  ReversibleCompilation.markedProgram (Compression.table a q machine)
    (Compression.deterministic a q machine) (Compression.targetCompatible a q machine)
    (Compression.mark a q machine)

def Boundary (machine : TM0.Machine (Fin a) (Fin q)) (state : Memory) : Prop :=
  (boundaryProgram a q machine).haltSignal state = 1

theorem boundary_iota (machine : TM0.Machine (Fin a) (Fin q))
    (state : TM0.Cfg (Fin a) (Fin q)) (history : ℕ) :
    Boundary a q machine (iota a q machine state history) := by
  apply (ReversibleCompilation.markedBoundary_iota_iff (Compression.table a q machine)
    (Compression.deterministic a q machine) (Compression.targetCompatible a q machine)
    (Compression.mark a q machine) _).mpr
  exact (Compression.mark_true_iff a q machine _).mpr (Compression.boundary_encode a q machine state history)

def FirstReturn (machine : TM0.Machine (Fin a) (Fin q)) (first last : Memory) : Prop :=
  ReversibleCompilation.NativeFirstReturn (Compression.table a q machine)
    (Compression.deterministic a q machine) (Compression.targetCompatible a q machine)
    (Compression.mark a q machine) first last

/-- A source step is precisely the next marked native word return, with its actual history. -/
theorem step_firstReturn (machine : TM0.Machine (Fin a) (Fin q))
    {first last : TM0.Cfg (Fin a) (Fin q)} (transition : TM0.step machine first = some last)
    (history : ℕ) :
    ∃ finalHistory, history < finalHistory ∧
      FirstReturn a q machine (iota a q machine first history) (iota a q machine last finalHistory) := by
  obtain ⟨finalHistory, grew, first_marked, last_marked, middle, initial, rest⟩ :=
    Compression.step_firstReturn a q machine transition history
  have inside : Relation.ReflTransGen
      (fun current next : Counter.Reversible.State 2 (Compression.size a q machine) =>
        Counter.Reversible.step (Compression.table a q machine) current = some next ∧
          Compression.mark a q machine current.1 = false)
      middle (Compression.encode a q machine last finalHistory) :=
    Relation.ReflTransGen.mono
      (fun current _ edge => ⟨edge.1, (Compression.mark_false_iff a q machine current).mpr edge.2⟩)
      _ _ rest
  exact ⟨finalHistory, grew, ReversibleCompilation.marked_firstReturn (Compression.table a q machine)
    (Compression.deterministic a q machine) (Compression.targetCompatible a q machine)
    (Compression.mark a q machine) initial inside
    ((Compression.mark_true_iff a q machine _).mpr first_marked)
    ((Compression.mark_true_iff a q machine _).mpr last_marked)⟩

/-- Every source step is a positive run of actual native returns with its larger history. -/
theorem step_reaches (machine : TM0.Machine (Fin a) (Fin q))
    {first last : TM0.Cfg (Fin a) (Fin q)} (transition : TM0.step machine first = some last)
    (history : ℕ) :
    ∃ finalHistory, history < finalHistory ∧
      StateTransition.Reaches₁ (program a q machine).step
        (iota a q machine first history) (iota a q machine last finalHistory) := by
  obtain ⟨finalHistory, grew, _, _, next, initial, rest⟩ :=
    step_firstReturn a q machine transition history
  exact ⟨finalHistory, grew, Relation.TransGen.head' initial
    (Relation.ReflTransGen.mono (fun _ _ edge => edge.1) _ _ rest)⟩

/-- Stopping is detected from the actual static halt address, without a global completeness premise. -/
theorem step_halt (machine : TM0.Machine (Fin a) (Fin q))
    (state : TM0.Cfg (Fin a) (Fin q)) (history : ℕ) (halted : TM0.step machine state = none) :
    (program a q machine).step (iota a q machine state history) = none := by
  have signal := (ReversibleCompilation.haltSignal_iota_iff (Compression.table a q machine)
    (Compression.deterministic a q machine) (Compression.targetCompatible a q machine)
    (Compression.encode a q machine state history)).mpr
      (Compression.no_outgoing_of_halt a q machine state history halted)
  change (if (program a q machine).haltSignal (iota a q machine state history) = 1 then none
    else some ((program a q machine).advance (iota a q machine state history))) = none
  exact ite_eq_left signal

def Related (machine : TM0.Machine (Fin a) (Fin q))
    (original : TM0.Cfg (Fin a) (Fin q)) (native : Memory) : Prop :=
  ∃ history, iota a q machine original history = native

theorem respects (machine : TM0.Machine (Fin a) (Fin q)) :
    StateTransition.Respects (TM0.step machine) (program a q machine).step (Related a q machine) := by
  intro original native related
  obtain ⟨history, rfl⟩ := related
  cases transition : TM0.step machine original with
  | none => exact step_halt a q machine original history transition
  | some next =>
      obtain ⟨finalHistory, _, run⟩ := step_reaches a q machine transition history
      exact ⟨iota a q machine next finalHistory, ⟨finalHistory, rfl⟩, run⟩

theorem halting_iff (machine : TM0.Machine (Fin a) (Fin q))
    (state : TM0.Cfg (Fin a) (Fin q)) (history : ℕ) :
    ((program a q machine).eval (iota a q machine state history)).Dom ↔
      (StateTransition.eval (TM0.step machine) state).Dom :=
  StateTransition.tr_eval_dom (respects a q machine) ⟨history, rfl⟩

theorem divergence_iff (machine : TM0.Machine (Fin a) (Fin q))
    (state : TM0.Cfg (Fin a) (Fin q)) (history : ℕ) :
    ¬ ((program a q machine).eval (iota a q machine state history)).Dom ↔
      ¬ (StateTransition.eval (TM0.step machine) state).Dom :=
  not_congr (halting_iff a q machine state history)

/-- The entire final configuration is recovered from the native result; history remains observable. -/
theorem result_iff (machine : TM0.Machine (Fin a) (Fin q))
    (first last : TM0.Cfg (Fin a) (Fin q)) (history : ℕ) :
    (∃ finalHistory, iota a q machine last finalHistory ∈
      (program a q machine).eval (iota a q machine first history)) ↔
      last ∈ StateTransition.eval (TM0.step machine) first := by
  constructor
  · rintro ⟨finalHistory, finished⟩
    obtain ⟨original, ⟨originalHistory, related⟩, source_finished⟩ :=
      StateTransition.tr_eval_rev (respects a q machine) ⟨history, rfl⟩ finished
    have same : (original, originalHistory) = (last, finalHistory) :=
      @iota_injective a q _ _ machine (original, originalHistory) (last, finalHistory) related
    have configurations : original = last := congrArg Prod.fst same
    simpa only [configurations] using source_finished
  · intro source_finished
    obtain ⟨native, ⟨finalHistory, rfl⟩, finished⟩ :=
      StateTransition.tr_eval (respects a q machine) ⟨history, rfl⟩ source_finished
    exact ⟨finalHistory, finished⟩

/-- The inverse is another fixed word table on the same fiber and with the same five primitives. -/
def reverseProgram (machine : TM0.Machine (Fin a) (Fin q)) :
    Program (11 * (Compression.size a q machine + Compression.edges a q machine)) :=
  ReversibleCompilation.reverseProgram (Compression.table a q machine)
    (Compression.deterministic a q machine) (Compression.targetCompatible a q machine)

theorem reverse_after_forward (machine : TM0.Machine (Fin a) (Fin q)) (state : Memory) :
    (reverseProgram a q machine).advance ((program a q machine).advance state) = state :=
  ReversibleCompilation.reverse_after_forward (Compression.table a q machine)
    (Compression.deterministic a q machine) (Compression.targetCompatible a q machine) state

theorem forward_after_reverse (machine : TM0.Machine (Fin a) (Fin q)) (state : Memory) :
    (program a q machine).advance ((reverseProgram a q machine).advance state) = state :=
  ReversibleCompilation.forward_after_reverse (Compression.table a q machine)
    (Compression.deterministic a q machine) (Compression.targetCompatible a q machine) state

def executionEquiv (machine : TM0.Machine (Fin a) (Fin q)) : Memory ≃ Memory :=
  ReversibleCompilation.executionEquiv (Compression.table a q machine)
    (Compression.deterministic a q machine) (Compression.targetCompatible a q machine)

theorem program_bijective (machine : TM0.Machine (Fin a) (Fin q)) :
    Function.Bijective (program a q machine).advance :=
  ReversibleCompilation.haltingProgram_bijective (Compression.table a q machine)
    (Compression.deterministic a q machine) (Compression.targetCompatible a q machine)

/-- Inverse native execution restores each whole source step and its prior history. -/
theorem step_retraces (machine : TM0.Machine (Fin a) (Fin q))
    {first last : TM0.Cfg (Fin a) (Fin q)} (transition : TM0.step machine first = some last)
    (history : ℕ) :
    ∃ finalHistory, history < finalHistory ∧ ∃ count : ℕ,
      ((reverseProgram a q machine).advance)^[count] (iota a q machine last finalHistory) =
        iota a q machine first history := by
  obtain ⟨finalHistory, grew, run⟩ := step_reaches a q machine transition history
  obtain ⟨count, reached⟩ := (program a q machine).reaches_iterate_advance run.to_reflTransGen
  refine ⟨finalHistory, grew, count, ?_⟩
  rw [← reached]
  exact (Function.LeftInverse.iterate (reverse_after_forward a q machine) count) _

/-- Native execution determines both departure and the next internal stopping boundary. -/
def macroStep (machine : TM0.Machine (Fin a) (Fin q)) (state : Memory) : Part (Option Memory) :=
  ReversibleCompilation.nativeMacro (Compression.table a q machine)
    (Compression.deterministic a q machine) (Compression.targetCompatible a q machine)
    (Compression.mark a q machine) state

/-- The inverse executes its own fixed word table and the same finite boundary observation. -/
def reverseMacro (machine : TM0.Machine (Fin a) (Fin q)) (state : Memory) : Part Memory :=
  Program.reverseReturn (reverseProgram a q machine) (boundaryProgram a q machine) state

theorem macroStep_of_firstReturn (machine : TM0.Machine (Fin a) (Fin q))
    {first last : Memory} (run : FirstReturn a q machine first last) :
    macroStep a q machine first = Part.some (some last) :=
  ReversibleCompilation.nativeMacro_of_firstReturn (Compression.table a q machine)
    (Compression.deterministic a q machine) (Compression.targetCompatible a q machine)
    (Compression.mark a q machine) run

theorem reverseMacro_of_firstReturn (machine : TM0.Machine (Fin a) (Fin q))
    {first last : Memory} (run : FirstReturn a q machine first last) :
    reverseMacro a q machine last = Part.some first := by
  obtain ⟨marked, _, after, initial, rest⟩ := run
  exact Program.reverseReturn_of_firstReturn (program a q machine) (reverseProgram a q machine)
    (boundaryProgram a q machine) (reverse_after_forward a q machine) initial rest marked

/-- The return has a positive native length and no marked intermediate word return. -/
theorem FirstReturn.iterates (machine : TM0.Machine (Fin a) (Fin q))
    {first last : Memory} (run : FirstReturn a q machine first last) :
    ReversibleReturn.FirstReturn (program a q machine).advance (Boundary a q machine) first last := by
  obtain ⟨marked_first, marked_last, after, initial, interior⟩ := run
  let P := program a q machine
  exact ReversibleReturn.firstReturn_of_relation (advance := P.advance)
    (boundary := Boundary a q machine) (transition := fun left right => P.step left = some right)
    (fun edge => P.advance_of_step edge) initial interior marked_first marked_last

/-- Reversing this native trace gives the first preceding boundary, with the same length. -/
theorem FirstReturn.inverse_iterates (machine : TM0.Machine (Fin a) (Fin q))
    {first last : Memory} (run : FirstReturn a q machine first last) :
    ReversibleReturn.FirstReturn (reverseProgram a q machine).advance (Boundary a q machine) last first :=
  ReversibleReturn.inverse_firstReturn (reverse_after_forward a q machine)
    (FirstReturn.iterates a q machine run)

/-- The two internally executed macros retain and recover the same complete configurations. -/
theorem step_return_pair (machine : TM0.Machine (Fin a) (Fin q))
    {first last : TM0.Cfg (Fin a) (Fin q)} (transition : TM0.step machine first = some last)
    (history : ℕ) :
    ∃ finalHistory, history < finalHistory ∧
      FirstReturn a q machine (iota a q machine first history) (iota a q machine last finalHistory) ∧
      macroStep a q machine (iota a q machine first history) =
        Part.some (some (iota a q machine last finalHistory)) ∧
      reverseMacro a q machine (iota a q machine last finalHistory) =
        Part.some (iota a q machine first history) := by
  obtain ⟨finalHistory, grew, run⟩ := step_firstReturn a q machine transition history
  exact ⟨finalHistory, grew, run, macroStep_of_firstReturn a q machine run,
    reverseMacro_of_firstReturn a q machine run⟩

/-- Halts and live steps agree with the source optional result under the causal native macro. -/
theorem macroStep_iota (machine : TM0.Machine (Fin a) (Fin q))
    (state : TM0.Cfg (Fin a) (Fin q)) (history : ℕ) :
    ∃ finalHistory,
      macroStep a q machine (iota a q machine state history) =
        Part.some ((TM0.step machine state).map (fun next => iota a q machine next finalHistory)) ∧
      (TM0.step machine state ≠ none → history < finalHistory) := by
  cases transition : TM0.step machine state with
  | none =>
      refine ⟨history, ?_, ?_⟩
      · simpa only [transition, Option.map_none, macroStep] using
          ReversibleCompilation.nativeMacro_of_halt (Compression.table a q machine)
            (Compression.deterministic a q machine) (Compression.targetCompatible a q machine)
            (Compression.mark a q machine) _ (step_halt a q machine state history transition)
      · simp
  | some next =>
      obtain ⟨finalHistory, grew, _, completed, _⟩ := step_return_pair a q machine transition history
      exact ⟨finalHistory, completed, fun _ => grew⟩

/-- Every finite source execution, including a nonhalting prefix, is an actual native lifted path. -/
theorem finite_run_actual_lifts (machine : TM0.Machine (Fin a) (Fin q))
    {first last : TM0.Cfg (Fin a) (Fin q)} (history : ℕ)
    (run : StateTransition.Reaches (TM0.step machine) first last) :
    ∃ finalHistory, ∃ count : ℕ,
      let initial := iota a q machine first history
      let driver := (program a q machine).runDriver count initial
      intermediateCurve driver initial =
        CoupledPullback.lowerCovering.liftPath driver.restrictedPath
          (CoupledPullback.upperProjection (restrictedState initial))
          (driver.restrictedPath.source.trans (restrictedState_over_base initial).symm) ∧
      restrictedTrajectory driver initial =
        CoupledPullback.upperCovering.liftPath (intermediatePath driver initial) (restrictedState initial)
          (intermediatePath driver initial).source ∧
      restrictedTrajectory driver initial 1 = restrictedState (iota a q machine last finalHistory) := by
  obtain ⟨native, ⟨finalHistory, rfl⟩, actual⟩ :=
    StateTransition.tr_reaches (respects a q machine) ⟨history, rfl⟩ run
  obtain ⟨count, endpoint⟩ := (program a q machine).runDriver_of_reaches actual
  refine ⟨finalHistory, count, ?_⟩
  dsimp only
  refine ⟨intermediateCurve_actual_lift _ _, restrictedTrajectory_actual_lift _ _, ?_⟩
  rw [restrictedTrajectory_end, endpoint]

/-- Every completed source computation has the two actual matching cover lifts generated by execution. -/
theorem result_actual_lifts (machine : TM0.Machine (Fin a) (Fin q))
    {first last : TM0.Cfg (Fin a) (Fin q)} (history : ℕ)
    (completed : last ∈ StateTransition.eval (TM0.step machine) first) :
    ∃ finalHistory, ∃ count : ℕ,
      let initial := iota a q machine first history
      let driver := (program a q machine).runDriver count initial
      intermediateCurve driver initial =
        CoupledPullback.lowerCovering.liftPath driver.restrictedPath
          (CoupledPullback.upperProjection (restrictedState initial))
          (driver.restrictedPath.source.trans (restrictedState_over_base initial).symm) ∧
      restrictedTrajectory driver initial =
        CoupledPullback.upperCovering.liftPath (intermediatePath driver initial) (restrictedState initial)
          (intermediatePath driver initial).source ∧
      restrictedTrajectory driver initial 1 = restrictedState (iota a q machine last finalHistory) := by
  exact finite_run_actual_lifts a q machine history
    (StateTransition.mem_eval.mp completed).1

/-- Complete reversible universality with endogenous forward and backward first-return macros. -/
theorem native_universality (machine : TM0.Machine (Fin a) (Fin q)) :
    let P := program a q machine
    let R := reverseProgram a q machine
    let I := iota a q machine
    Function.Injective (fun pair : TM0.Cfg (Fin a) (Fin q) × ℕ => I pair.1 pair.2) ∧
    (∀ state, R.advance (P.advance state) = state ∧ P.advance (R.advance state) = state) ∧
    (∀ first last, TM0.step machine first = some last → ∀ history,
      ∃ finalHistory, history < finalHistory ∧
        FirstReturn a q machine (I first history) (I last finalHistory) ∧
        macroStep a q machine (I first history) = Part.some (some (I last finalHistory)) ∧
        reverseMacro a q machine (I last finalHistory) = Part.some (I first history)) ∧
    (∀ state history, TM0.step machine state = none →
      macroStep a q machine (I state history) = Part.some none) ∧
    (∀ first last history,
      (∃ finalHistory, I last finalHistory ∈ P.eval (I first history)) ↔
        last ∈ StateTransition.eval (TM0.step machine) first) ∧
    (∀ state history, (P.eval (I state history)).Dom ↔
      (StateTransition.eval (TM0.step machine) state).Dom) ∧
    (∀ state history, ¬ (P.eval (I state history)).Dom ↔
      ¬ (StateTransition.eval (TM0.step machine) state).Dom) ∧
    (∀ first last history, StateTransition.Reaches (TM0.step machine) first last →
      ∃ finalHistory, ∃ count : ℕ,
        let initial := I first history
        let driver := P.runDriver count initial
        intermediateCurve driver initial =
          CoupledPullback.lowerCovering.liftPath driver.restrictedPath
            (CoupledPullback.upperProjection (restrictedState initial))
            (driver.restrictedPath.source.trans (restrictedState_over_base initial).symm) ∧
        restrictedTrajectory driver initial =
          CoupledPullback.upperCovering.liftPath (intermediatePath driver initial) (restrictedState initial)
            (intermediatePath driver initial).source ∧
        restrictedTrajectory driver initial 1 = restrictedState (I last finalHistory)) := by
  dsimp only
  exact ⟨iota_injective a q machine,
    fun state => ⟨reverse_after_forward a q machine state, forward_after_reverse a q machine state⟩,
    fun _ _ transition history => step_return_pair a q machine transition history,
    fun state history halted => by
      obtain ⟨finalHistory, executed, _⟩ := macroStep_iota a q machine state history
      simpa only [halted, Option.map_none] using executed,
    result_iff a q machine, halting_iff a q machine, divergence_iff a q machine,
    fun _ _ history run => finite_run_actual_lifts a q machine history run⟩


end Monodromy.ReversibleNativeTuring

end
