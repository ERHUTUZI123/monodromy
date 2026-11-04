module

public import Monodromy.Effectiveness
public import Monodromy.Observation
public import Mathlib.Computability.Halting

/-!
# The computational boundary of fixed observations

Removing the two zero-conditional loops leaves
a finite control quotient with a bounded primitive-recursive halting test.
One actual conditional loop yields a strictly different halting domain under
the same fixed input representation.
-/

@[expose] public section

namespace Monodromy.ForwardBoundary

/-- Decidable predicates stay decidable under computable changes of input representation. -/
theorem computablePred_comp {α β : Type*} [Primcodable α] [Primcodable β]
    {predicate : β → Prop} {initial : α → β} (decision : ComputablePred predicate)
    (effective : Computable initial) : ComputablePred (fun input => predicate (initial input)) := by
  obtain ⟨decider, computes⟩ := decision
  exact ⟨fun input => decider (initial input), computes.comp effective⟩

/-- A standard numeric presentation of the halting problem. -/
def hardFunction (input : ℕ) : Part ℕ :=
  Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code input) 0

theorem hardFunction_partrec : Partrec hardFunction :=
  Nat.Partrec.Code.eval_part.comp (Computable.ofNat Nat.Partrec.Code) (Computable.const 0)

theorem hardFunction_undecidable : ¬ ComputablePred (fun input => (hardFunction input).Dom) := by
  intro decision
  have codes := computablePred_comp decision
    (Computable.encode : Computable (Encodable.encode : Nat.Partrec.Code → ℕ))
  exact ComputablePred.halting_problem 0
    (codes.of_eq (fun code => by simp [hardFunction]))

end Monodromy.ForwardBoundary

namespace Monodromy.CoupledContinuation

/-- Remove precisely the two zero-conditional monodromy gates; finite control routing remains. -/
def Gate.ProbeFree : Gate → Prop
  | .zeroLeft | .zeroRight => False
  | .left | .right | .control => True

def Word.ProbeFree : Word → Prop
  | [] => True
  | (gate, _) :: rest => gate.ProbeFree ∧ Word.ProbeFree rest

/-- A signed nonconditional gate is a translation on the complete branch presentation. -/
theorem Gate.evalInt_translation (gate : Gate) (backward : Bool) (free : gate.ProbeFree)
    (labels : Labels) :
    Gate.evalInt gate backward labels = labels + Gate.evalInt gate backward 0 := by
  rcases labels with ⟨⟨left, right⟩, control⟩
  cases gate <;> simp_all [Gate.ProbeFree, Gate.evalInt, Prod.mk_add_mk]

/-- Each finite probe-free word translates by its fixed value at the zero label. -/
theorem Word.evalInt_translation (word : Word) (free : word.ProbeFree) (labels : Labels) :
    Word.evalInt word labels = labels + Word.evalInt word 0 := by
  induction word generalizing labels with
  | nil => simp [Word.evalInt]
  | cons atom rest recursive =>
      rcases atom with ⟨gate, backward⟩
      change Word.evalInt rest (Gate.evalInt gate backward labels) =
        labels + Word.evalInt rest (Gate.evalInt gate backward 0)
      calc
        Word.evalInt rest (Gate.evalInt gate backward labels) =
            Gate.evalInt gate backward labels + Word.evalInt rest 0 :=
          recursive free.2 _
        _ = (labels + Gate.evalInt gate backward 0) + Word.evalInt rest 0 := by
          rw [Gate.evalInt_translation gate backward free.1 labels]
        _ = labels + (Gate.evalInt gate backward 0 + Word.evalInt rest 0) := add_assoc _ _ _
        _ = labels + Word.evalInt rest (Gate.evalInt gate backward 0) :=
          congrArg (labels + ·) (recursive free.2 _).symm

/-- The translation law concerns actual geometric execution, through the proved refinement. -/
theorem Word.execute_translation (word : Word) (free : word.ProbeFree) (labels : Labels) :
    execute (Word.driver word) (Labels.prepare labels) =
      Labels.prepare (labels + Word.evalInt word 0) :=
  (Word.execute_evalInt word labels).trans
    (congrArg Labels.prepare (Word.evalInt_translation word free labels))

end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation.Program

variable {degree : ℕ} [NeZero degree]

def ProbeFree (program : Program degree) : Prop := ∀ index, (program.table index).ProbeFree

/-- Equality of control residues is exactly the finite observation needed below. -/
theorem indexInt_eq_of_mod_eq {first second : Labels}
    (same : first.2 % (degree : ℤ) = second.2 % (degree : ℤ)) :
    indexInt degree first = indexInt degree second := by
  apply Fin.ext
  have values := (indexInt_cast (degree := degree) first).trans
    (same.trans (indexInt_cast (degree := degree) second).symm)
  exact_mod_cast values

/-- Each table entry contributes a fixed control displacement to this finite quotient. -/
def quotientNext (program : Program degree) (index : Fin degree) : Fin degree :=
  indexInt degree (((0, 0), (index.val : ℤ)) + Word.evalInt (program.table index) 0)

theorem quotient_closed (program : Program degree) (free : program.ProbeFree) (labels : Labels) :
    indexInt degree (program.nextInt labels) = program.quotientNext (indexInt degree labels) := by
  unfold nextInt quotientNext
  rw [Word.evalInt_translation _ (free _) labels]
  apply indexInt_eq_of_mod_eq
  change (labels.2 + (Word.evalInt (program.table (indexInt degree labels)) 0).2) % (degree : ℤ) =
    (((indexInt degree labels).val : ℤ) +
      (Word.evalInt (program.table (indexInt degree labels)) 0).2) % (degree : ℤ)
  simp only [Int.add_emod, indexInt_cast, Int.emod_emod]

/-- Complete stopping semantics descend to the closed finite observation. -/
theorem probeFree_evalInt_dom (program : Program degree) (free : program.ProbeFree) (labels : Labels) :
    (program.evalInt labels).Dom ↔
      (StateTransition.eval (Observation.stopped program.quotientNext program.stop)
        (indexInt degree labels)).Dom := by
  change (StateTransition.eval
    (Observation.stopped program.nextInt (fun state => program.stop (indexInt degree state))) labels).Dom ↔ _
  exact Observation.observed_dom (indexInt degree) program.nextInt program.quotientNext program.stop
    (quotient_closed program free) labels

theorem probeFree_halting_bound (program : Program degree) (free : program.ProbeFree) (labels : Labels) :
    (program.evalInt labels).Dom ↔ ∃ rounds < degree,
      program.stop ((program.quotientNext^[rounds]) (indexInt degree labels)) = true := by
  rw [probeFree_evalInt_dom program free labels]
  simpa only [Fintype.card_fin] using
    Observation.finite_stopped_dom_iff program.quotientNext program.stop (indexInt degree labels)

/-- A finite bounded search decides stopping for this controlled deletion of the native language. -/
def probeFreeHalts (program : Program degree) (labels : Labels) : Bool :=
  Observation.finiteHalts program.quotientNext program.stop (indexInt degree labels)

theorem probeFreeHalts_eq_true (program : Program degree) (free : program.ProbeFree) (labels : Labels) :
    program.probeFreeHalts labels = true ↔ (program.evalInt labels).Dom := by
  rw [probeFree_evalInt_dom program free labels]
  exact Observation.finiteHalts_eq_true program.quotientNext program.stop (indexInt degree labels)

/-- The same bound applies to actual covering-space execution, not merely its arithmetic presentation. -/
theorem probeFree_native_bound (program : Program degree) (free : program.ProbeFree) (labels : Labels) :
    (program.eval (Labels.prepare labels)).Dom ↔ ∃ rounds < degree,
      program.stop ((program.quotientNext^[rounds]) (indexInt degree labels)) = true := by
  rw [eval_prepareInt]
  change (program.evalInt labels).Dom ↔ _
  exact probeFree_halting_bound program free labels

theorem probeFreeHalts_native (program : Program degree) (free : program.ProbeFree) (labels : Labels) :
    program.probeFreeHalts labels = true ↔ (program.eval (Labels.prepare labels)).Dom := by
  rw [eval_prepareInt]
  change program.probeFreeHalts labels = true ↔ (program.evalInt labels).Dom
  exact probeFreeHalts_eq_true program free labels

end Monodromy.CoupledContinuation.Program

namespace Monodromy.CoupledContinuation.Program

variable {degree : ℕ} [NeZero degree]

/-- The bounded decision procedure is primitive recursive in the complete initial labels. -/
theorem primrec_probeFreeHalts (program : Program degree) : Primrec program.probeFreeHalts :=
  (Primrec.dom_finite (Observation.finiteHalts program.quotientNext program.stop)).comp
    (primrec_indexInt (degree := degree))

/-- Decidability holds for actual native execution under the fixed branch presentation. -/
theorem probeFree_native_halting_primrec (program : Program degree) (free : program.ProbeFree) :
    PrimrecPred (fun labels : Labels => (program.eval (Labels.prepare labels)).Dom) := by
  have decision : PrimrecPred (fun labels : Labels => program.probeFreeHalts labels = true) :=
    Primrec.eq.comp (primrec_probeFreeHalts program) (Primrec.const true)
  exact decision.of_eq (probeFreeHalts_native program free)

end Monodromy.CoupledContinuation.Program

namespace Monodromy.CoupledContinuation.Program

variable {degree : ℕ} [NeZero degree]

/-- All initial data with the same control residue have the same stopping behavior here. -/
theorem probeFree_native_same_control (program : Program degree) (free : program.ProbeFree)
    (first second : Labels)
    (same : first.2 % (degree : ℤ) = second.2 % (degree : ℤ)) :
    (program.eval (Labels.prepare first)).Dom ↔ (program.eval (Labels.prepare second)).Dom := by
  rw [probeFree_native_bound program free first, probeFree_native_bound program free second]
  rw [indexInt_eq_of_mod_eq same]

end Monodromy.CoupledContinuation.Program

namespace Monodromy.CoupledContinuation

/-- One native zero-conditional loop; only its marked finite control root stops execution. -/
def zeroTest : Program 2 where
  table := fun _ => Word.atom .zeroLeft false
  stop := fun index => index.val == 1

/-- The actual geometric computation recognizes zero under the fixed three-root input. -/
theorem zeroTest_native_dom (input : ℤ) :
    (zeroTest.eval (prepare input 0 0)).Dom ↔ input = 0 := by
  change (zeroTest.eval (Labels.prepare (((input, 0), 0) : Labels))).Dom ↔ _
  rw [Program.eval_prepareInt]
  change (StateTransition.eval
    (Observation.stopped zeroTest.nextInt zeroTest.haltInt) (((input, 0), 0) : Labels)).Dom ↔ _
  rw [Observation.stopped_dom_iff]
  constructor
  · rintro ⟨rounds, stops⟩
    by_contra nonzero
    have fixed : zeroTest.nextInt (((input, 0), 0) : Labels) = ((input, 0), 0) := by
      simp [zeroTest, Program.nextInt, Word.atom, Word.evalInt, Gate.evalInt, nonzero]
    have repeated := Function.iterate_fixed fixed rounds
    rw [repeated] at stops
    have keeps_running : zeroTest.haltInt (((input, 0), 0) : Labels) = false := by
      norm_num [zeroTest, Program.haltInt, Program.indexInt]
    rw [keeps_running] at stops
    contradiction
  · intro zero
    subst input
    refine ⟨1, ?_⟩
    change zeroTest.haltInt (zeroTest.nextInt (((0, 0), 0) : Labels)) = true
    norm_num [zeroTest, Program.haltInt, Program.indexInt, Program.nextInt,
      Word.atom, Word.evalInt, Gate.evalInt]

/-- With the same input encoding, the two-gate deletion loses this concrete halting domain. -/
theorem no_probeFree_zeroTest {degree : ℕ} [NeZero degree]
    (program : Program degree) (free : program.ProbeFree) :
    ¬ ∀ input : ℕ,
      (program.eval (prepare (input : ℤ) 0 0)).Dom ↔
        (zeroTest.eval (prepare (input : ℤ) 0 0)).Dom := by
  intro same
  have zero_halts : (program.eval (prepare 0 0 0)).Dom :=
    (same 0).mpr ((zeroTest_native_dom 0).mpr rfl)
  have also_one : (program.eval (prepare 1 0 0)).Dom :=
    (Program.probeFree_native_same_control program free
      (((0, 0), 0) : Labels) (((1, 0), 0) : Labels) rfl).mp zero_halts
  have impossible := (zeroTest_native_dom 1).mp ((same 1).mp also_one)
  norm_num at impossible

end Monodromy.CoupledContinuation
