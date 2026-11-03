module

public import Monodromy.Radix
public import Monodromy.IntegerPrimrec
public import Mathlib.Computability.Primrec.List

/-!
# Effective reading of block memory

A finite residue table reads a letter, and division exposes the next block.
A bounded iteration suffices on every valid word encoding, giving a total
primitive recursive decoder for the retained natural-number memory.
-/

@[expose] public section

namespace Monodromy.IntegerPrimrec

theorem toNat : Primrec Int.toNat :=
  (cases (α := ℤ) (β := ℕ) Primrec.id Primrec₂.right (Primrec₂.const 0)).of_eq
    (by intro value; cases value <;> rfl)

end Monodromy.IntegerPrimrec

namespace Monodromy.BinaryBlocks

variable {a : ℕ}

/-- The current finite cover address. -/
def address (value : ℕ) : Fin (3 ^ a) :=
  ⟨value % 3 ^ a, Nat.mod_lt _ (pow_pos (by decide) _)⟩

/-- A fixed finite table recognizes the block assigned to each letter. -/
def lookup (value : Fin (3 ^ a)) : Option (Fin a) :=
  (List.finRange a).find? (fun letter => digit letter = value.val)

theorem lookup_digit (letter : Fin a) : lookup ⟨digit letter, digit_lt letter⟩ = some letter := by
  have found : (lookup (⟨digit letter, digit_lt letter⟩ : Fin (3 ^ a))).isSome := by
    apply List.find?_isSome.mpr
    exact ⟨letter, by simp, by simp⟩
  cases result : lookup (⟨digit letter, digit_lt letter⟩ : Fin (3 ^ a)) with
  | none => simp [result] at found
  | some other =>
      have same : digit other = digit letter := by
        have tested := List.find?_some (by exact result)
        simpa only [decide_eq_true_eq] using tested
      exact congrArg some (digit_injective same)

theorem lookup_zero : lookup (0 : Fin (3 ^ a)) = none := by
  apply List.find?_eq_none.mpr
  intro letter _ matched
  have equal : digit letter = 0 := by simpa using (of_decide_eq_true matched)
  exact (ne_of_gt (digit_positive letter)) equal

/-- The accumulator is reversed; zero and invalid addresses end the scan. -/
def decodeStep (state : ℕ × List (Fin a)) : ℕ × List (Fin a) :=
  match lookup (address state.1) with
  | none => (0, state.2)
  | some letter => (state.1 / 3 ^ a, letter :: state.2)

@[simp] theorem decodeStep_zero (accumulator : List (Fin a)) :
    decodeStep (0, accumulator) = (0, accumulator) := by
  simp [decodeStep, address, lookup_zero]

theorem decodeStep_cons (letter : Fin a) (tail accumulator : List (Fin a)) :
    decodeStep (encode (letter :: tail), accumulator) = (encode tail, letter :: accumulator) := by
  have current : address (encode (letter :: tail)) = (⟨digit letter, digit_lt letter⟩ : Fin (3 ^ a)) := by
    apply Fin.ext
    exact encode_cons_mod letter tail
  simp [decodeStep, current, lookup_digit, encode_cons_div]

/-- The memory code itself bounds the number of letters to be read. -/
theorem length_le_encode (word : List (Fin a)) : word.length ≤ encode word := by
  induction word with
  | nil => simp
  | cons letter tail previous =>
      have positive := digit_positive letter
      have growth : encode tail ≤ 3 ^ a * encode tail :=
        Nat.le_mul_of_pos_left _ (pow_pos (by decide) _)
      rw [List.length_cons, encode_cons]
      omega

/-- Any budget at least the word length completes the exact block scan. -/
theorem decodeStep_iterate (word accumulator : List (Fin a)) (rounds : ℕ)
    (enough : word.length ≤ rounds) :
    (decodeStep^[rounds]) (encode word, accumulator) = (0, word.reverse ++ accumulator) := by
  induction word generalizing accumulator rounds with
  | nil =>
      simpa using Function.iterate_fixed (decodeStep_zero accumulator) rounds
  | cons letter tail previous =>
      cases rounds with
      | zero => simp at enough
      | succ rounds =>
          rw [Function.iterate_succ_apply, decodeStep_cons,
            previous (letter :: accumulator) rounds (by simpa using Nat.le_of_succ_le_succ enough)]
          simp

/-- A total finite scan; valid encodings return their entire original word. -/
def decode (value : ℕ) : List (Fin a) :=
  ((decodeStep^[value]) (value, [])).2.reverse

@[simp] theorem decode_encode (word : List (Fin a)) : decode (encode word) = word := by
  unfold decode
  rw [decodeStep_iterate word [] (encode word) (length_le_encode word)]
  simp

/-- Writing block memory is primitive recursive as well. -/
theorem primrec_encode : Primrec (@encode a) := by
  have primitive_digit : Primrec (@digit a) := Primrec.dom_finite _
  have combine : Primrec₂ (fun (_ : List (Fin a)) (entry : Fin a × ℕ) =>
      digit entry.1 + 3 ^ a * entry.2) :=
    (Primrec.nat_add.comp (primitive_digit.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.nat_mul.comp (Primrec.const (3 ^ a)) (Primrec.snd.comp Primrec.snd))).to₂
  have write := Primrec.list_foldr Primrec.id (Primrec.const 0) combine
  apply write.of_eq
  intro word
  induction word with
  | nil => rfl
  | cons letter tail previous =>
      simpa only [id_eq, List.foldr_cons, encode_cons] using
        congrArg (fun value => digit letter + 3 ^ a * value) previous

theorem primrec_address : Primrec (@address a) := by
  apply Primrec.fin_val_iff.mp
  exact Primrec.nat_mod.comp Primrec.id (Primrec.const (3 ^ a))

theorem primrec_lookup : Primrec (@lookup a) := Primrec.dom_finite _

theorem primrec_decodeStep : Primrec (@decodeStep a) := by
  have current : Primrec (fun state : ℕ × List (Fin a) => lookup (a := a) (address state.1)) :=
    (primrec_lookup (a := a)).comp ((primrec_address (a := a)).comp Primrec.fst)
  have append_letter : Primrec₂ (fun (state : ℕ × List (Fin a)) (letter : Fin a) =>
      (state.1 / 3 ^ a, letter :: state.2)) :=
    ((Primrec.nat_div.comp (Primrec.fst.comp Primrec.fst) (Primrec.const (3 ^ a))).pair
      (Primrec.list_cons.comp Primrec.snd (Primrec.snd.comp Primrec.fst))).to₂
  exact (Primrec.option_casesOn current ((Primrec.const 0).pair Primrec.snd) append_letter).of_eq
    (by intro state; cases result : lookup (address state.1) <;> simp [decodeStep, result])

/-- The decoder is primitive recursive on all natural-number inputs. -/
theorem primrec_decode : Primrec (@decode a) := by
  have scan : Primrec (fun value : ℕ => (decodeStep^[value]) (value, ([] : List (Fin a)))) :=
    Primrec.nat_iterate Primrec.id (Primrec.id.pair (Primrec.const []))
      (primrec_decodeStep.comp Primrec.snd).to₂
  exact Primrec.list_reverse.comp (Primrec.snd.comp scan)

end Monodromy.BinaryBlocks
