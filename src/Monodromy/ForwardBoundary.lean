module

public import Monodromy.Effectiveness
public import Mathlib.Computability.Halting

/-!
# The computational boundary of fixed observations

Forward programs have a syntax-computed finite stopping bound. Their halting
predicate is primitive recursive, and remains decidable after any computable
initialization. An undecidable partial recursive domain separates this class
from general cover programs.
-/

@[expose] public section

namespace Monodromy.ForwardBoundary

open CoverExpressions

variable {n : ℕ}

/-- A fixed finite return can be iterated a supplied finite number of times effectively. -/
theorem primrec_iterate (program : Program n) :
    Primrec (fun point : ℕ × Program.IntState n =>
      ((Program.nextInt program)^[point.1]) point.2) :=
  Primrec.nat_iterate Primrec.fst Primrec.snd
    ((Program.primrec_nextInt program).comp Primrec.snd).to₂

/-- The complete halting predicate of a forward program is primitive recursive. -/
theorem primrec_halting (program : Program n) (forward : program.Forward) :
    PrimrecPred (fun state : Program.IntState n => (program.evalInt state).Dom) := by
  have at_round : PrimrecRel (fun rounds : ℕ => fun state : Program.IntState n =>
      Guard.evalInt program.stop (((Program.nextInt program)^[rounds]) state) = true) :=
    Primrec.eq.comp ((Guard.primrec_evalInt program.stop).comp (primrec_iterate program))
      (Primrec.const true)
  have bounded := at_round.exists_mem_list.comp
    (Primrec.const (List.range (program.forwardModulus.toNat ^ n))) Primrec.id
  exact bounded.of_eq (fun state => by
    simpa only [List.mem_range, id_eq] using (program.forward_halting_bound forward state).symm)

/-- Decidable predicates stay decidable under computable changes of input representation. -/
theorem computablePred_comp {α β : Type*} [Primcodable α] [Primcodable β]
    {predicate : β → Prop} {initial : α → β} (decision : ComputablePred predicate)
    (effective : Computable initial) : ComputablePred (fun input => predicate (initial input)) := by
  obtain ⟨decider, computes⟩ := decision
  exact ⟨fun input => decider (initial input), computes.comp effective⟩

theorem initialized_halting {α : Type*} [Primcodable α]
    (program : Program n) (forward : program.Forward) (initial : α → Program.IntState n)
    (effective : Computable initial) :
    ComputablePred (fun input => (program.evalInt (initial input)).Dom) :=
  computablePred_comp (initial := initial)
    (predicate := fun state : Program.IntState n => (program.evalInt state).Dom)
    (primrec_halting program forward).computablePred effective

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

/-- Computable input encoding cannot make forward control realize an undecidable domain. -/
theorem no_forward_hardFunction (program : Program n) (forward : program.Forward)
    (initial : ℕ → Program.IntState n) (effective : Computable initial) :
    ¬ ∀ input, (program.evalInt (initial input)).Dom ↔ (hardFunction input).Dom := by
  intro same_domain
  exact hardFunction_undecidable
    ((initialized_halting program forward initial effective).of_eq same_domain)

/-- One partial recursive domain lies outside the entire forward sublanguage. -/
theorem strict_boundary : ∃ function : ℕ → Part ℕ, Partrec function ∧
    ∀ (n : ℕ) (program : Program n), program.Forward →
      ∀ initial : ℕ → Program.IntState n, Computable initial →
        ¬ ∀ input, (program.evalInt (initial input)).Dom ↔ (function input).Dom :=
  ⟨hardFunction, hardFunction_partrec, fun _ program forward initial effective =>
    no_forward_hardFunction program forward initial effective⟩

end Monodromy.ForwardBoundary
