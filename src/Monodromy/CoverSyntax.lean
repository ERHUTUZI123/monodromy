module

public import Monodromy.CoverPrograms
public import Mathlib.Data.W.Basic

/-!
# Finite presentations of cover programs

Finite-arity trees encode expressions and guards without changing their syntax.
Their executable natural-number encoding makes finite branching explicit.
-/

@[expose] public section

namespace Monodromy.CoverExpressions

inductive TermSymbol (n : ℕ)
  | coord (index : Fin n)
  | integerConst (value : ℤ)
  | add
  | integerScale (value : ℤ)
  | select (B : ℕ)
  | descend (B : ℕ)

abbrev TermData (n : ℕ) := Fin n ⊕ ℤ ⊕ Unit ⊕ ℤ ⊕ ℕ ⊕ ℕ

def TermSymbol.data {n : ℕ} : TermSymbol n → TermData n
  | .coord index => .inl index
  | .integerConst value => .inr (.inl value)
  | .add => .inr (.inr (.inl ()))
  | .integerScale value => .inr (.inr (.inr (.inl value)))
  | .select B => .inr (.inr (.inr (.inr (.inl B))))
  | .descend B => .inr (.inr (.inr (.inr (.inr B))))

def TermSymbol.ofData {n : ℕ} : TermData n → TermSymbol n
  | .inl index => .coord index
  | .inr (.inl value) => .integerConst value
  | .inr (.inr (.inl _)) => .add
  | .inr (.inr (.inr (.inl value))) => .integerScale value
  | .inr (.inr (.inr (.inr (.inl B)))) => .select B
  | .inr (.inr (.inr (.inr (.inr B)))) => .descend B

instance {n : ℕ} : Encodable (TermSymbol n) :=
  Encodable.ofLeftInverse TermSymbol.data TermSymbol.ofData (by intro symbol; cases symbol <;> rfl)

abbrev TermSymbol.arity {n : ℕ} : TermSymbol n → ℕ
  | .coord _ | .integerConst _ => 0
  | .add => 2
  | .integerScale _ | .descend _ => 1
  | .select B => B + 2

abbrev TermTree (n : ℕ) := WType (fun symbol : TermSymbol n => Fin symbol.arity)

def termTree {n : ℕ} : Term n → TermTree n
  | .coord index => ⟨.coord index, Fin.elim0⟩
  | .integerConst value => ⟨.integerConst value, Fin.elim0⟩
  | .add first second => ⟨.add, ![termTree first, termTree second]⟩
  | .integerScale value term => ⟨.integerScale value, fun _ => termTree term⟩
  | .select B key branches =>
      ⟨.select B, Fin.cases (termTree key) (fun index => termTree (branches index))⟩
  | .descend B key => ⟨.descend B, fun _ => termTree key⟩

def treeTerm {n : ℕ} : TermTree n → Term n
  | ⟨.coord index, _⟩ => .coord index
  | ⟨.integerConst value, _⟩ => .integerConst value
  | ⟨.add, branches⟩ => .add (treeTerm (branches 0)) (treeTerm (branches 1))
  | ⟨.integerScale value, branches⟩ => .integerScale value (treeTerm (branches 0))
  | ⟨.select B, branches⟩ =>
      .select B (treeTerm (branches 0)) (fun index => treeTerm (branches index.succ))
  | ⟨.descend B, branches⟩ => .descend B (treeTerm (branches 0))

theorem treeTerm_termTree {n : ℕ} (term : Term n) : treeTerm (termTree term) = term := by
  induction term with
  | coord | integerConst => rfl
  | add _ _ first_ih second_ih => simp [termTree, treeTerm, first_ih, second_ih]
  | integerScale _ _ ih => simp [termTree, treeTerm, ih]
  | select B key branches key_ih branches_ih =>
      simp [termTree, treeTerm, key_ih, branches_ih]
  | descend _ _ ih => simp [termTree, treeTerm, ih]

instance {n : ℕ} : Encodable (Term n) :=
  Encodable.ofLeftInverse termTree treeTerm treeTerm_termTree

abbrev GuardData (n : ℕ) := Bool ⊕ (ℕ × Term n)

abbrev guardArity {n : ℕ} : GuardData n → ℕ
  | .inl _ => 0
  | .inr (B, _) => B + 1

abbrev GuardTree (n : ℕ) := WType (fun data : GuardData n => Fin (guardArity data))

def guardTree {n : ℕ} : Guard n → GuardTree n
  | .constant value => ⟨.inl value, Fin.elim0⟩
  | .select B key branches => ⟨.inr (B, key), fun index => guardTree (branches index)⟩

def treeGuard {n : ℕ} : GuardTree n → Guard n
  | ⟨.inl value, _⟩ => .constant value
  | ⟨.inr (B, key), branches⟩ => .select B key (fun index => treeGuard (branches index))

theorem treeGuard_guardTree {n : ℕ} (guard : Guard n) : treeGuard (guardTree guard) = guard := by
  induction guard with
  | constant => rfl
  | select B key branches ih => simp [guardTree, treeGuard, ih]

instance {n : ℕ} : Encodable (Guard n) :=
  Encodable.ofLeftInverse guardTree treeGuard treeGuard_guardTree

instance {n : ℕ} : Encodable (Program n) :=
  Encodable.ofLeftInverse (fun program => (program.updates, program.stop))
    (fun (updates, stop) => ⟨updates, stop⟩) (fun _ => rfl)

/-- Finite cover programs have a reproducible natural-number presentation. -/
theorem program_encoding_injective (n : ℕ) :
    Function.Injective (Encodable.encode : Program n → ℕ) := Encodable.encode_injective

end Monodromy.CoverExpressions
