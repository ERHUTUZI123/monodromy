module

public import Monodromy.NativeIO
public import Monodromy.Effectiveness
public import Monodromy.ForwardBoundary

/-!
# The computational structure of continuation

The interface is fixed before a program is chosen. Integer inputs prepare
canonical branch words; completed native states have one fixed numeric
readout. Finite cubic-cover syntax then realizes exactly the partial
recursive functions, with complete results and stopping semantics.
-/

@[expose] public section

namespace Monodromy.Structure

open CoverExpressions

/-- Interpreting a complete native result uses the fixed integer-grid representation. -/
theorem mem_native (program : Program 3) (initial result : Program.IntState 3) :
    Program.init result ∈ Program.evalReal program (Program.init initial) ↔
      result ∈ Program.evalInt program initial := by
  rw [Program.evalReal_init, Part.map_eq_map, Part.mem_map_iff]
  constructor
  · rintro ⟨state, finished, same⟩
    exact Program.init_injective same ▸ finished
  · intro finished
    exact ⟨result, finished, rfl⟩

/-- Every input and output uses the same representation, independently of the program. -/
def Computes (program : Program 3) (function : ℕ → Part ℕ) : Prop :=
  ∀ input value, value ∈ function input ↔
    ∃ state : Program.IntState 3,
      Program.init state ∈ Program.evalReal program (Program.init (NativeIO.input input)) ∧
        NativeIO.output state = value

/-- The effective continuation language uses three retained branches and one cubic observation. -/
def Realizable (function : ℕ → Part ℕ) : Prop :=
  ∃ program : Program 3, program.UsesRadix 3 ∧ Computes program function

/-- The native graph and the complete partial integer result are equivalent specifications. -/
theorem computes_iff (program : Program 3) (function : ℕ → Part ℕ) :
    Computes program function ↔
      ∀ input, NativeIO.output <$> Program.evalInt program (NativeIO.input input) = function input := by
  constructor
  · intro correct input
    apply Part.ext
    intro value
    rw [Part.map_eq_map, Part.mem_map_iff]
    have meaning := correct input value
    simp_rw [mem_native] at meaning
    exact meaning.symm
  · intro correct input value
    rw [← correct input, Part.map_eq_map, Part.mem_map_iff]
    simp_rw [mem_native]

theorem computes_dom {program : Program 3} {function : ℕ → Part ℕ}
    (correct : Computes program function) (input : ℕ) :
    (Program.evalReal program (Program.init (NativeIO.input input))).Dom ↔ (function input).Dom := by
  rw [Program.evalReal_init, ← (computes_iff program function).mp correct input]
  rfl

theorem computes_divergence {program : Program 3} {function : ℕ → Part ℕ}
    (correct : Computes program function) (input : ℕ) :
    ¬ (Program.evalReal program (Program.init (NativeIO.input input))).Dom ↔ ¬ (function input).Dom :=
  not_congr (computes_dom correct input)

/-- Finite cover syntax and its fixed numeric interface introduce only partial recursive behavior. -/
theorem partrec_of_realizable {function : ℕ → Part ℕ} (realized : Realizable function) : Partrec function := by
  obtain ⟨program, _, correct⟩ := realized
  have execution : Partrec (fun input =>
      NativeIO.output <$> Program.evalInt program (NativeIO.input input)) :=
    ((Program.partrec_evalInt program).comp NativeIO.primrec_input.to_comp).map
      (NativeIO.primrec_output.to_comp.comp Computable.snd).to₂
  exact execution.of_eq ((computes_iff program function).mp correct)

/-- Finite Turing compilation gives one native program for each partial recursive function. -/
theorem realizable_of_partrec {function : ℕ → Part ℕ} (effective : Partrec function) : Realizable function := by
  obtain ⟨source, cubic, simulation⟩ := NativeLowerBound.every_partrec effective
  refine ⟨NativeLowerBound.program source, cubic, (computes_iff _ _).mpr ?_⟩
  intro input
  apply Part.ext
  intro value
  rw [Part.map_eq_map, Part.mem_map_iff]
  constructor
  · rintro ⟨state, finished, read_value⟩
    have defined : (function input).Dom :=
      (simulation input).1.mp (Part.dom_iff_mem.mpr ⟨state, finished⟩)
    obtain ⟨answer, answer_finished⟩ := Part.dom_iff_mem.mp defined
    have source_finished : FormalCompilation.halt0 source [answer] ∈
        (fun result => FormalCompilation.halt0 source [result]) <$> function input :=
      (Part.mem_map_iff _).mpr ⟨answer, answer_finished, rfl⟩
    obtain ⟨represented, represented_finished, representation⟩ :=
      ((simulation input).2 _).mp source_finished
    have same := Part.mem_unique finished represented_finished
    rw [same, NativeIO.output_represents source answer represented representation] at read_value
    exact read_value ▸ answer_finished
  · intro finished
    have source_finished : FormalCompilation.halt0 source [value] ∈
        (fun result => FormalCompilation.halt0 source [result]) <$> function input :=
      (Part.mem_map_iff _).mpr ⟨value, finished, rfl⟩
    obtain ⟨state, native_finished, represented⟩ := ((simulation input).2 _).mp source_finished
    exact ⟨state, native_finished, NativeIO.output_represents source value state represented⟩

/-- Exact computational characterization with fixed I/O and the actual native execution semantics. -/
theorem continuation_characterization (function : ℕ → Part ℕ) :
    Realizable function ↔ Partrec function :=
  ⟨partrec_of_realizable, realizable_of_partrec⟩

/-- Every partial recursive function has a globally analytic realization by actual continuation. -/
theorem analytic_continuation_realization {function : ℕ → Part ℕ} (effective : Partrec function) :
    ∃ program : Program 3, program.UsesRadix 3 ∧ Computes program function ∧
      (∀ point, AnalyticAt ℝ (Program.nextReal program) point) ∧
      ∀ (rounds : ℕ) (memory : Program.Memory 3) (index : Fin 3),
        Transport.transport Circle.isCoveringMap_exp (Program.runPath program rounds memory index)
          (Program.coordinate memory index) =
          Program.coordinate (((Program.advance program)^[rounds]) memory) index := by
  obtain ⟨program, cubic, correct⟩ := realizable_of_partrec effective
  exact ⟨program, cubic, correct, Program.analyticAt_nextReal program, Program.run_transport program⟩

/-- Removing descent strictly reduces the realizable functions with the fixed numeric interface. -/
theorem descent_strictly_extends : ∃ function : ℕ → Part ℕ, Realizable function ∧
    ∀ program : Program 3, program.Forward → ¬ Computes program function := by
  refine ⟨ForwardBoundary.hardFunction,
    realizable_of_partrec ForwardBoundary.hardFunction_partrec, ?_⟩
  intro program forward correct
  apply ForwardBoundary.no_forward_hardFunction program forward NativeIO.input NativeIO.primrec_input.to_comp
  intro input
  exact (congrArg Part.Dom ((computes_iff program _).mp correct input)).to_iff

/-- Presence of a descent expression alone places no lower bound on a program's stopping behavior. -/
theorem descent_can_be_inactive : ∃ program : Program 1,
    program.UsesRadix 3 ∧ ¬ program.Forward ∧
      ∀ state, program.evalInt state = Part.some state := by
  let program : Program 1 := ⟨fun _ => .descend 2 (.coord 0), .constant true⟩
  refine ⟨program, ⟨fun _ => ⟨rfl, trivial⟩, trivial⟩, fun forward => forward.1 0, ?_⟩
  intro state
  apply Part.eq_some_iff.mpr
  exact StateTransition.mem_eval.mpr ⟨.refl, rfl⟩

universe u v

/-- A finite closed stopping observation gives a computable halting domain whenever its input is computable. -/
theorem closed_observation_barrier {S F : Type u} {Input : Type v}
    [Fintype F] [Primcodable F] [Primcodable Input]
    (observe : S → F) (next : S → S) (advance : F → F) (halt : F → Bool)
    (closed : ∀ state, observe (next state) = advance (observe state))
    (initial : Input → S) (effective : Computable (fun input => observe (initial input))) :
    ComputablePred (fun input =>
      (StateTransition.eval (Observation.stopped next (fun state => halt (observe state)))
        (initial input)).Dom) := by
  have test : PrimrecPred (fun state : F => Observation.finiteHalts advance halt state = true) :=
    Primrec.eq.comp (Primrec.dom_finite _) (Primrec.const true)
  have finite_domain : ComputablePred (fun state : F =>
      (StateTransition.eval (Observation.stopped advance halt) state).Dom) :=
    (test.of_eq (Observation.finiteHalts_eq_true advance halt)).computablePred
  exact (ForwardBoundary.computablePred_comp finite_domain effective).of_eq
    (fun input => (Observation.observed_dom observe next advance halt closed (initial input)).symm)

end Monodromy.Structure
