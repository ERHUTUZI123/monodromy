module

public import Monodromy.Tower

public import Monodromy.CoverExpressions
public import Monodromy.CoverTables
public import Monodromy.Lattice
public import Monodromy.Observation
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Computability.StateTransition

/-!
# Programs built from cover expressions

A finite expression table updates persistent integer coordinates. A finite
cover guard determines stopping. The same syntax supplies analytic execution
and the complete paths that carry its retained logarithmic branches.
-/

@[expose] public section

namespace Monodromy.CoverExpressions

structure Program (n : ℕ) where
  updates : Fin n → Term n
  stop : Guard n

namespace Program

abbrev IntState (n : ℕ) := Fin n → ℤ
abbrev RealState (n : ℕ) := Fin n → ℝ

variable {n : ℕ}

/-- A stopped program returns its current coordinate through its internal guard. -/
def returning (program : Program n) (index : Fin n) : Term n :=
  Guard.gate program.stop (.coord index) (program.updates index)

def nextInt (program : Program n) (state : IntState n) : IntState n :=
  fun index => CoverExpressions.evalInt (returning program index) state

noncomputable def nextReal (program : Program n) (point : RealState n) : RealState n :=
  fun index => CoverExpressions.evalReal (returning program index) point

theorem nextInt_halt (program : Program n) (state : IntState n)
    (done : Guard.evalInt program.stop state = true) : nextInt program state = state := by
  funext index
  simp [nextInt, returning, Guard.eval_gate, done, CoverExpressions.evalInt]

def stepInt (program : Program n) (state : IntState n) : Option (IntState n) :=
  if Guard.evalInt program.stop state then none else some (nextInt program state)

def evalInt (program : Program n) : IntState n → Part (IntState n) :=
  StateTransition.eval (stepInt program)

theorem nextInt_tick (program : Program n) (state : IntState n) :
    nextInt program state = (stepInt program state).getD state := by
  cases done : Guard.evalInt program.stop state with
  | false => simp [stepInt, done]
  | true => simpa [stepInt, done] using nextInt_halt program state done

noncomputable def encode (state : IntState n) : RealState n := fun index => (state index : ℝ)

theorem encode_injective : Function.Injective (@encode n) := by
  intro first second same
  funext index
  exact Int.cast_injective (congrFun same index)

theorem nextReal_encode (program : Program n) (state : IntState n) :
    nextReal program (encode state) = encode (nextInt program state) := by
  funext index
  exact CoverExpressions.evalReal_int (returning program index) state

theorem analyticAt_nextReal (program : Program n) (point : RealState n) :
    AnalyticAt ℝ (nextReal program) point :=
  AnalyticAt.pi (fun index => CoverExpressions.analyticAt_evalReal (returning program index) point)

def Grid (point : RealState n) : Prop := ∃ state : IntState n, encode state = point

abbrev Memory (n : ℕ) := {point : RealState n // Grid point}

noncomputable def init (state : IntState n) : Memory n := ⟨encode state, state, rfl⟩

theorem init_injective : Function.Injective (@init n) := by
  intro first second same
  exact encode_injective (congrArg Subtype.val same)

theorem nextReal_grid (program : Program n) {point : RealState n} (valid : Grid point) :
    Grid (nextReal program point) := by
  obtain ⟨state, rfl⟩ := valid
  exact ⟨nextInt program state, (nextReal_encode program state).symm⟩

/-- The native value is computed solely by the real expression interpretation. -/
noncomputable def advance (program : Program n) (memory : Memory n) : Memory n :=
  ⟨nextReal program memory.val, nextReal_grid program memory.property⟩

theorem advance_init (program : Program n) (state : IntState n) :
    advance program (init state) = init (nextInt program state) :=
  Subtype.ext (nextReal_encode program state)

theorem advance_iterate_init (program : Program n) (rounds : ℕ) (state : IntState n) :
    ((advance program)^[rounds]) (init state) = init (((nextInt program)^[rounds]) state) := by
  induction rounds with
  | zero => rfl
  | succ rounds previous =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', previous, advance_init]

/-- Equality is tested only on the guard's proved integer-grid indicator. -/
noncomputable def stepReal (program : Program n) (memory : Memory n) : Option (Memory n) :=
  if Guard.evalReal program.stop memory.val = 1 then none else some (advance program memory)

noncomputable def evalReal (program : Program n) : Memory n → Part (Memory n) :=
  StateTransition.eval (stepReal program)

theorem guardReal_init (program : Program n) (state : IntState n) :
    Guard.evalReal program.stop (init state).val = if Guard.evalInt program.stop state then 1 else 0 :=
  Guard.evalReal_int program.stop state

theorem stepReal_init (program : Program n) (state : IntState n) :
    stepReal program (init state) = (stepInt program state).map init := by
  unfold stepReal stepInt
  rw [guardReal_init]
  cases Guard.evalInt program.stop state <;> simp [advance_init]

/-- The entire partial execution agrees, including every final coordinate and divergence. -/
theorem evalReal_init (program : Program n) (state : IntState n) :
    evalReal program (init state) = init <$> evalInt program state := by
  have refinement : StateTransition.Respects (stepInt program) (stepReal program)
      (fun first second => init first = second) := by
    apply StateTransition.fun_respects.mpr
    intro source
    cases result : stepInt program source with
    | none =>
        change stepReal program (init source) = none
        simp [stepReal_init, result]
    | some successor =>
        apply Relation.TransGen.single
        simp [stepReal_init, result]
  exact StateTransition.tr_eval' (stepInt program) (stepReal program) init refinement state

noncomputable def coordinates (memory : Memory n) : Fin n → ℝ :=
  fun index => (2 * Real.pi) * memory.val index

theorem coordinates_grid (memory : Memory n) : Lattice.Grid (coordinates memory) := by
  obtain ⟨state, same⟩ := memory.property
  intro index
  change Circle.exp ((2 * Real.pi) * memory.val index) = 1
  rw [← same]
  simpa only [encode, mul_comm] using Circle.exp_int_mul_two_pi (state index)

noncomputable def coordinate (memory : Memory n) (index : Fin n) : Logarithm.Memory :=
  Lattice.Return.coordinate coordinates coordinates_grid memory index

noncomputable def stepPath (program : Program n) (memory : Memory n) (index : Fin n) :
    Path (1 : Circle) 1 :=
  Lattice.Return.stepPath coordinates coordinates_grid (advance program) memory index

theorem step_transport (program : Program n) (memory : Memory n) (index : Fin n) :
    Transport.transport Circle.isCoveringMap_exp (stepPath program memory index)
      (coordinate memory index) = coordinate (advance program memory) index :=
  Lattice.Return.step_transport coordinates coordinates_grid (advance program) memory index

noncomputable def runPath (program : Program n) (rounds : ℕ) (memory : Memory n) (index : Fin n) :
    Path (1 : Circle) 1 :=
  Lattice.Return.runPath coordinates coordinates_grid (advance program) rounds memory index

/-- Every finite native run is the actual transport along its internally generated paths. -/
theorem run_transport (program : Program n) (rounds : ℕ) (memory : Memory n) (index : Fin n) :
    Transport.transport Circle.isCoveringMap_exp (runPath program rounds memory index)
      (coordinate memory index) = coordinate (((advance program)^[rounds]) memory) index :=
  Lattice.Return.run_transport coordinates coordinates_grid (advance program) rounds memory index

end Program

end Monodromy.CoverExpressions

namespace Monodromy.CoverExpressions.Program

variable {n : ℕ}

def Supported (program : Program n) (M : ℤ) : Prop :=
  (∀ index, CoverExpressions.Supported M (program.updates index)) ∧ Guard.Supported M program.stop

def Forward (program : Program n) : Prop :=
  (∀ index, CoverExpressions.Forward (program.updates index)) ∧ Guard.Forward program.stop

theorem nextInt_modEq (program : Program n) {M : ℤ} (supported : Supported program M)
    {first second : IntState n} (same : ∀ index, first index ≡ second index [ZMOD M]) :
    ∀ index, nextInt program first index ≡ nextInt program second index [ZMOD M] := by
  have guards := supported.2.eval_eq same
  intro index
  change CoverExpressions.evalInt (Guard.gate program.stop (.coord index) (program.updates index)) first ≡
    CoverExpressions.evalInt (Guard.gate program.stop (.coord index) (program.updates index)) second [ZMOD M]
  rw [Guard.eval_gate, Guard.eval_gate, ← guards]
  split_ifs
  · exact same index
  · exact (supported.1 index).modEq same

/-- A common residue system is computed once from the complete finite program. -/
def forwardModulus (program : Program n) : ℤ :=
  Guard.forwardModulus program.stop *
    ∏ index, CoverExpressions.forwardModulus (program.updates index)

theorem forwardModulus_positive (program : Program n) : 0 < forwardModulus program :=
  mul_pos (Guard.forwardModulus_positive program.stop)
    (Finset.prod_pos (fun index _ => CoverExpressions.forwardModulus_positive (program.updates index)))

theorem forward_supported_modulus (program : Program n) (forward : Forward program) :
    Supported program (forwardModulus program) := by
  constructor
  · intro index
    exact (CoverExpressions.forward_supported_modulus (program.updates index) (forward.1 index)).mono
      ((Finset.dvd_prod_of_mem (fun index => CoverExpressions.forwardModulus (program.updates index))
        (Finset.mem_univ index)).trans (dvd_mul_left _ _))
  · exact (Guard.forward_supported_modulus program.stop forward.2).mono (dvd_mul_right _ _)

theorem forward_supported (program : Program n) (forward : Forward program) :
    ∃ M : ℤ, 0 < M ∧ Supported program M :=
  ⟨forwardModulus program, forwardModulus_positive program, forward_supported_modulus program forward⟩

abbrev ResidueState (n m : ℕ) := Fin n → ZMod m

def observe (m : ℕ) (state : IntState n) : ResidueState n m := fun index => state index

def representative (m : ℕ) (state : ResidueState n m) : IntState n := fun index => (state index).val

theorem observe_representative (m : ℕ) [NeZero m] (state : ResidueState n m) :
    observe m (representative m state) = state := by
  funext index
  simp [observe, representative]

theorem modEq_of_observe_eq (m : ℕ) {first second : IntState n}
    (same : observe m first = observe m second) :
    ∀ index, first index ≡ second index [ZMOD (m : ℤ)] := fun index =>
  (ZMod.intCast_eq_intCast_iff _ _ m).mp (congrFun same index)

theorem observe_eq_of_modEq (m : ℕ) {first second : IntState n}
    (same : ∀ index, first index ≡ second index [ZMOD (m : ℤ)]) : observe m first = observe m second := by
  funext index
  exact (ZMod.intCast_eq_intCast_iff _ _ m).mpr (same index)

def quotientNext (program : Program n) (m : ℕ) (state : ResidueState n m) : ResidueState n m :=
  observe m (nextInt program (representative m state))

def quotientStop (program : Program n) (m : ℕ) (state : ResidueState n m) : Bool :=
  Guard.evalInt program.stop (representative m state)

def quotientEval (program : Program n) (m : ℕ) : ResidueState n m → Part (ResidueState n m) :=
  StateTransition.eval (Observation.stopped (quotientNext program m) (quotientStop program m))

theorem observe_next (program : Program n) (m : ℕ) [NeZero m]
    (supported : Supported program (m : ℤ)) (state : IntState n) :
    observe m (nextInt program state) = quotientNext program m (observe m state) := by
  apply observe_eq_of_modEq
  apply nextInt_modEq program supported
  have same := modEq_of_observe_eq m (observe_representative m (observe m state))
  exact fun index => (same index).symm

theorem observe_stop (program : Program n) (m : ℕ) [NeZero m]
    (supported : Supported program (m : ℤ)) (state : IntState n) :
    quotientStop program m (observe m state) = Guard.evalInt program.stop state := by
  exact supported.2.eval_eq (modEq_of_observe_eq m (observe_representative m (observe m state)))

/-- A supported program's complete partial execution projects to its finite observation. -/
theorem quotient_eval (program : Program n) (m : ℕ) [NeZero m]
    (supported : Supported program (m : ℤ)) (state : IntState n) :
    quotientEval program m (observe m state) = observe m <$> evalInt program state := by
  have projected := Observation.observed_eval (observe m) (nextInt program)
    (quotientNext program m) (quotientStop program m) (observe_next program m supported) state
  have halts : (fun current => quotientStop program m (observe m current)) = Guard.evalInt program.stop :=
    funext (observe_stop program m supported)
  rw [halts] at projected
  exact projected

/-- Every forward program has one finite residue system preserving all stopping semantics. -/
theorem forward_finite_observation (program : Program n) (forward : Forward program) :
    ∃ m : ℕ, 0 < m ∧ ∀ state : IntState n,
      quotientEval program m (observe m state) = observe m <$> evalInt program state := by
  obtain ⟨M, positive, supported⟩ := forward_supported program forward
  let m := M.toNat
  have positive_m : 0 < m := by dsimp [m]; omega
  have cast : (m : ℤ) = M := Int.toNat_of_nonneg (le_of_lt positive)
  let _ : NeZero m := ⟨by omega⟩
  refine ⟨m, positive_m, ?_⟩
  intro state
  exact quotient_eval program m (cast ▸ supported) state

end Monodromy.CoverExpressions.Program

namespace Monodromy.CoverExpressions

open unitInterval

variable {n : ℕ}

noncomputable def keyCurve (key : Term n) (curve : C(I, Fin n → ℝ)) : C(I, ℝ) where
  toFun t := (2 * Real.pi) * evalReal key (curve t)
  continuous_toFun := continuous_const.mul
    ((continuous_iff_continuousAt.mpr (analyticAt_evalReal key · |>.continuousAt)).comp curve.continuous)

/-- A finite query node follows the actual lift of its own induced base path. -/
theorem query_transport (B : ℕ) (key : Term n) (curve : C(I, Fin n → ℝ)) :
    Transport.transport (Radix.Tower.covering (B + 1))
      (Radix.Tower.basePath (keyCurve key curve))
      ⟨Radix.Tower.observe (B + 1) (keyCurve key curve 0),
        Radix.Tower.square (B + 1) (keyCurve key curve 0)⟩ =
      ⟨Radix.Tower.observe (B + 1) (keyCurve key curve 1),
        Radix.Tower.square (B + 1) (keyCurve key curve 1)⟩ :=
  Radix.Tower.transport_observe (B + 1) (keyCurve key curve)

/-- On integer state, the transported query root is exactly the selected finite digit. -/
theorem query_integer (B : ℕ) (key : Term n) (state : Fin n → ℤ) :
    Radix.readRoot (B + 1) ((2 * Real.pi) * evalReal key (fun index => (state index : ℝ))) =
      Radix.omega (B + 1) (digit B (evalInt key state)) := by
  rw [evalReal_int]
  have angle := congrArg (fun k : ℤ => (2 * Real.pi) * (k : ℝ))
    (decomposition B (evalInt key state)).symm
  rw [angle]
  exact Radix.readRoot_digit (B + 1) _ _

end Monodromy.CoverExpressions

namespace Monodromy.CoverExpressions.Program

variable {n : ℕ}

/-- A supported program stops within the cardinality of its finite observation. -/
theorem supported_halting_bound (program : Program n) (m : ℕ) [NeZero m]
    (supported : Supported program (m : ℤ)) (state : IntState n) :
    (evalInt program state).Dom ↔ ∃ rounds < m ^ n,
      Guard.evalInt program.stop (((nextInt program)^[rounds]) state) = true := by
  have projected : (quotientEval program m (observe m state)).Dom ↔
      (evalInt program state).Dom := by
    rw [quotient_eval program m supported]
    rfl
  have evolution : Function.Semiconj (observe m) (nextInt program) (quotientNext program m) :=
    observe_next program m supported
  have halts (rounds : ℕ) :
      quotientStop program m (((quotientNext program m)^[rounds]) (observe m state)) =
        Guard.evalInt program.stop (((nextInt program)^[rounds]) state) := by
    rw [← evolution.iterate_right rounds state, observe_stop program m supported]
  rw [← projected]
  change (StateTransition.eval (Observation.stopped (quotientNext program m)
    (quotientStop program m)) (observe m state)).Dom ↔ _
  rw [Observation.finite_stopped_dom_iff]
  simp only [ResidueState, Fintype.card_fun, Fintype.card_fin, ZMod.card]
  exact exists_congr fun rounds => and_congr_right fun _ => by rw [halts]

/-- A bounded halting test for the forward sublanguage, computed from its syntax. -/
def forwardHalts (program : Program n) (state : IntState n) : Bool :=
  let m := (forwardModulus program).toNat
  let _ : NeZero m := ⟨by have positive := forwardModulus_positive program; dsimp [m]; omega⟩
  Observation.finiteHalts (quotientNext program m) (quotientStop program m) (observe m state)

/-- The finite test is exact for every program in the forward sublanguage. -/
theorem forwardHalts_eq_true (program : Program n) (forward : Forward program) (state : IntState n) :
    forwardHalts program state = true ↔ (evalInt program state).Dom := by
  let m := (forwardModulus program).toNat
  let _ : NeZero m := ⟨by have positive := forwardModulus_positive program; dsimp [m]; omega⟩
  have cast : (m : ℤ) = forwardModulus program :=
    Int.toNat_of_nonneg (le_of_lt (forwardModulus_positive program))
  have supported : Supported program (m : ℤ) :=
    cast ▸ forward_supported_modulus program forward
  change Observation.finiteHalts (quotientNext program m) (quotientStop program m)
    (observe m state) = true ↔ _
  rw [Observation.finiteHalts_eq_true]
  change (quotientEval program m (observe m state)).Dom ↔ _
  rw [quotient_eval program m supported]
  rfl

/-- A forward program's syntax supplies an explicit stopping-time bound. -/
theorem forward_halting_bound (program : Program n) (forward : Forward program) (state : IntState n) :
    (evalInt program state).Dom ↔ ∃ rounds < (forwardModulus program).toNat ^ n,
      Guard.evalInt program.stop (((nextInt program)^[rounds]) state) = true := by
  let m := (forwardModulus program).toNat
  let _ : NeZero m := ⟨by have positive := forwardModulus_positive program; dsimp [m]; omega⟩
  have cast : (m : ℤ) = forwardModulus program :=
    Int.toNat_of_nonneg (le_of_lt (forwardModulus_positive program))
  exact supported_halting_bound program m (cast ▸ forward_supported_modulus program forward) state

end Monodromy.CoverExpressions.Program

namespace Monodromy.CoverExpressions.Program

variable {n : ℕ}

/-- The input observation sufficient for one complete return at output modulus m. -/
def demand (program : Program n) (m : ℤ) : ℤ :=
  ∏ index, CoverExpressions.demand (returning program index) m

theorem demand_positive (program : Program n) {m : ℤ} (positive : 0 < m) :
    0 < demand program m :=
  Finset.prod_pos (fun index _ => CoverExpressions.demand_positive (returning program index) positive)

theorem nextInt_modEq_demand (program : Program n) (m : ℤ) {first second : IntState n}
    (same : ∀ index, first index ≡ second index [ZMOD demand program m]) :
    ∀ index, nextInt program first index ≡ nextInt program second index [ZMOD m] := by
  intro index
  exact CoverExpressions.evalInt_modEq_demand (returning program index) m
    (fun register => (same register).of_dvd
      (Finset.dvd_prod_of_mem (fun index => CoverExpressions.demand (returning program index) m)
        (Finset.mem_univ index)))

/-- Observation requirements compose backwards through successive native returns. -/
def runDemand (program : Program n) : ℕ → ℤ → ℤ
  | 0, m => m
  | rounds + 1, m => demand program (runDemand program rounds m)

theorem runDemand_positive (program : Program n) (rounds : ℕ) {m : ℤ} (positive : 0 < m) :
    0 < runDemand program rounds m := by
  induction rounds with
  | zero => exact positive
  | succ rounds previous => exact demand_positive program previous

/-- Every finite run asks for a finite initial observation of its retained branches. -/
theorem iterate_modEq_demand (program : Program n) (rounds : ℕ) (m : ℤ)
    {first second : IntState n}
    (same : ∀ index, first index ≡ second index [ZMOD runDemand program rounds m]) :
    ∀ index, ((nextInt program)^[rounds]) first index ≡
      ((nextInt program)^[rounds]) second index [ZMOD m] := by
  induction rounds generalizing first second with
  | zero => exact same
  | succ rounds previous =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      exact previous (nextInt_modEq_demand program (runDemand program rounds m) same)

end Monodromy.CoverExpressions.Program

namespace Monodromy.CoverExpressions

variable {n radix : ℕ}

/-- A program uses one finite cover for every update and stopping observation. -/
def Program.UsesRadix (program : Program n) (radix : ℕ) : Prop :=
  (∀ index, CoverExpressions.UsesRadix radix (program.updates index)) ∧ program.stop.UsesRadix radix

theorem Program.returning_usesRadix (program : Program n) (uses : program.UsesRadix radix)
    (index : Fin n) : CoverExpressions.UsesRadix radix (program.returning index) :=
  Guard.gate_usesRadix program.stop (.coord index) (program.updates index) uses.2 trivial (uses.1 index)

end Monodromy.CoverExpressions
