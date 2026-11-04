module

public import Mathlib.Computability.TuringMachine.PostTuringMachine
public import Mathlib.Data.Nat.Digits.Lemmas

/-!
# Canonical half-tape codes

Positional encoding descends to blank-padded tapes and preserves every cell.
-/

@[expose] public section

namespace Monodromy.TapeCode

open Turing

variable {a : ℕ} [NeZero a]

/-- Zero is the blank digit; appending blanks leaves this natural number unchanged. -/
def encode (tape : ListBlank (Fin a)) : ℕ :=
  tape.liftOn (fun word => Nat.ofDigits (a + 1) (word.map Fin.val)) (by
    rintro word _ ⟨count, rfl⟩
    simp [List.map_append, List.map_replicate, Fin.default_eq_zero])

@[simp] theorem encode_mk (word : List (Fin a)) :
    encode (ListBlank.mk word) = Nat.ofDigits (a + 1) (word.map Fin.val) := rfl

@[simp] theorem encode_empty : encode (∅ : ListBlank (Fin a)) = 0 := rfl

/-- Push, pop and head observation are arithmetic identities on the blank quotient itself. -/
theorem encode_cons (symbol : Fin a) (tape : ListBlank (Fin a)) :
    encode (tape.cons symbol) = symbol.val + (a + 1) * encode tape := by
  refine ListBlank.induction_on tape (fun word => ?_)
  simp only [ListBlank.cons_mk, encode_mk, List.map_cons, Nat.ofDigits_cons]

theorem decomposition (tape : ListBlank (Fin a)) :
    encode tape = tape.head.val + (a + 1) * encode tape.tail := by
  simpa only [ListBlank.cons_head_tail] using encode_cons tape.head tape.tail

theorem head_code (tape : ListBlank (Fin a)) :
    encode tape % (a + 1) = tape.head.val := by
  rw [decomposition, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (Nat.lt_succ_of_lt tape.head.isLt)]

theorem tail_code (tape : ListBlank (Fin a)) :
    encode tape / (a + 1) = encode tape.tail := by
  rw [decomposition, Nat.add_mul_div_left _ _ (Nat.succ_pos a),
    Nat.div_eq_of_lt (Nat.lt_succ_of_lt tape.head.isLt), zero_add]

/-- Every tape cell is determined by the same fixed code, through repeated quotienting. -/
theorem nth_eq_of_code_eq (index : ℕ) (first second : ListBlank (Fin a))
    (same : encode first = encode second) : first.nth index = second.nth index := by
  induction index generalizing first second with
  | zero =>
      simp only [ListBlank.nth_zero]
      apply Fin.ext
      rw [← head_code first, ← head_code second, same]
  | succ index recursive =>
      rw [ListBlank.nth_succ, ListBlank.nth_succ]
      apply recursive
      rw [← tail_code first, ← tail_code second, same]

/-- The whole infinite blank-padded half-tape has a canonical, injective natural code. -/
theorem encode_injective : Function.Injective (@encode a _) := by
  intro first second same
  apply ListBlank.ext
  intro index
  exact nth_eq_of_code_eq index first second same

theorem encode_eq_zero_iff (tape : ListBlank (Fin a)) : encode tape = 0 ↔ tape = ∅ := by
  constructor
  · intro zero
    apply encode_injective
    exact zero.trans encode_empty.symm
  · rintro rfl
    exact encode_empty

end Monodromy.TapeCode
