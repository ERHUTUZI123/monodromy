module

public import Monodromy.FormalCompilation
public import Mathlib.Computability.Primrec.List
public import Mathlib.Data.Fintype.EquivFin

/-!
# A fixed numeric tape interface

Binary symbols carry the number; delimiters, blank columns and the stack
bottom marker leave the accumulator unchanged. The decoder is independent
of the source program and its control labels.
-/

@[expose] public section

namespace Monodromy.CanonicalIO

open Turing PartrecToTM2

abbrev Alphabet := TM2to1.Γ' K' (fun _ => Γ')

def readBit (value : ℕ) : Γ' → ℕ
  | .bit0 => value + value
  | .bit1 => value + value + 1
  | .cons | .consₗ => value

def readSymbol (value : ℕ) (letter : Alphabet) : ℕ :=
  match letter.2 .main with
  | none => value
  | some bit => readBit value bit

def decodeWord (word : List Alphabet) : ℕ := word.foldl readSymbol 0

def decodeBits (word : List Γ') : ℕ := word.foldr (fun bit value => readBit value bit) 0

theorem decode_posNum (value : PosNum) : decodeBits (trPosNum value) = (value : ℕ) := by
  induction value with
  | one => rfl
  | bit0 value previous =>
      change decodeBits (trPosNum value) + decodeBits (trPosNum value) = (value : ℕ) + value
      rw [previous]
  | bit1 value previous =>
      change decodeBits (trPosNum value) + decodeBits (trPosNum value) + 1 = (value : ℕ) + value + 1
      rw [previous]

theorem decode_num (value : Num) : decodeBits (trNum value) = (value : ℕ) := by
  cases value with
  | zero => rfl
  | pos value => exact decode_posNum value

theorem decode_nat (value : ℕ) : decodeBits (trNat value) = value := by
  change decodeBits (trNum (value : Num)) = value
  rw [decode_num, Num.to_of_nat]

set_option backward.isDefEq.respectTransparency false in
/-- Packing the main stack changes its orientation but preserves every numeric bit. -/
theorem decode_packed (word : List Γ') :
    decodeWord (TM2to1.trInit K'.main word) = decodeBits word := by
  rw [decodeBits, ← List.foldl_reverse]
  cases reversed : word.reverse with
  | nil =>
      simp only [decodeWord, TM2to1.trInit, reversed]
      rfl
  | cons bit tail =>
      simp only [decodeWord, TM2to1.trInit, reversed, List.map_cons, List.headI_cons,
        List.tail_cons, List.foldl_cons, List.foldl_map, readSymbol, Function.update_self]

/-- The output protocol is a single numeric item, with a fixed decoder. -/
theorem decode_output (value : ℕ) :
    decodeWord (TM2to1.trInit K'.main (trList [value])) = value := by
  rw [decode_packed]
  simp only [trList]
  change (trNat value ++ [Γ'.cons]).foldr (fun bit result => readBit result bit) 0 = value
  rw [List.foldr_append]
  exact decode_nat value

@[simp] theorem read_blank (value : ℕ) : readSymbol value (default : Alphabet) = value := rfl

theorem fold_blank (count value : ℕ) :
    (List.replicate count (default : Alphabet)).foldl readSymbol value = value := by
  induction count generalizing value with
  | zero => rfl
  | succ count previous => simpa only [List.replicate_succ, List.foldl_cons, read_blank] using previous value

/-- Appending arbitrary blank padding leaves the fixed numeric readout unchanged. -/
theorem decode_blank_extension {first second : List Alphabet} (extension : BlankExtends first second) :
    decodeWord first = decodeWord second := by
  obtain ⟨count, rfl⟩ := extension
  simp [decodeWord, List.foldl_append, fold_blank]

/-- The same readout is well-defined on the complete right half-tape. -/
def decodeTape (tape : ListBlank Alphabet) : ℕ :=
  tape.liftOn decodeWord (fun _ _ extension => decode_blank_extension extension)

@[simp] theorem decodeTape_mk (word : List Alphabet) : decodeTape (ListBlank.mk word) = decodeWord word := rfl


/-- One fixed finite coding is used for all tape-symbol computability statements. -/
noncomputable instance alphabetPrimcodable : Primcodable Alphabet :=
  Primcodable.ofEquiv (Fin (Fintype.card Alphabet)) (Fintype.equivFin Alphabet)

def factor (letter : Alphabet) : ℕ :=
  match letter.2 .main with
  | some .bit0 | some .bit1 => 2
  | _ => 1

def offset (letter : Alphabet) : ℕ :=
  match letter.2 .main with
  | some .bit1 => 1
  | _ => 0

theorem readSymbol_affine (value : ℕ) (letter : Alphabet) :
    value * factor letter + offset letter = readSymbol value letter := by
  cases entry : letter.2 K'.main with
  | none => simp [factor, offset, readSymbol, entry]
  | some bit => cases bit <;> simp [factor, offset, readSymbol, entry, readBit, Nat.mul_two]

/-- The decoder's only unbounded arithmetic is primitive recursive affine arithmetic. -/
theorem primrec_readSymbol : Primrec₂ readSymbol :=
  (Primrec.nat_add.comp
    (Primrec.nat_mul.comp Primrec.fst ((Primrec.dom_finite factor).comp Primrec.snd))
    ((Primrec.dom_finite offset).comp Primrec.snd)).of_eq
      (fun input => readSymbol_affine input.1 input.2)

theorem primrec_decodeWord : Primrec decodeWord :=
  Primrec.list_foldl Primrec.id (Primrec.const 0) (primrec_readSymbol.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂


noncomputable instance symbolPrimcodable : Primcodable Γ' :=
  Primcodable.ofEquiv (Fin (Fintype.card Γ')) (Fintype.equivFin Γ')

def increment : List Γ' → List Γ'
  | [] => [.bit1]
  | .bit0 :: tail => .bit1 :: tail
  | .bit1 :: tail => .bit0 :: increment tail
  | _ :: _ => [.bit1]

theorem increment_posNum (value : PosNum) : increment (trPosNum value) = trPosNum value.succ := by
  induction value with
  | one => rfl
  | bit0 => rfl
  | bit1 value previous => exact congrArg (List.cons Γ'.bit0) previous

theorem increment_nat (value : ℕ) : increment (trNat value) = trNat (value + 1) := by
  simp only [trNat, Nat.cast_succ, Num.add_one]
  cases (value : Num) with
  | zero => rfl
  | pos positive => exact increment_posNum positive

def incrementStep (state : Γ' × List Γ' × List Γ') : List Γ' :=
  if state.1 = .bit0 then .bit1 :: state.2.1
  else if state.1 = .bit1 then .bit0 :: state.2.2
  else [.bit1]

theorem primrec_incrementStep : Primrec incrementStep :=
  Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const Γ'.bit0))
    (Primrec.list_cons.comp (Primrec.const Γ'.bit1) (Primrec.fst.comp Primrec.snd))
    (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const Γ'.bit1))
      (Primrec.list_cons.comp (Primrec.const Γ'.bit0) (Primrec.snd.comp Primrec.snd))
      (Primrec.const [Γ'.bit1]))

theorem primrec_increment : Primrec increment := by
  apply (Primrec.list_rec Primrec.id (Primrec.const [Γ'.bit1])
    (primrec_incrementStep.comp Primrec.snd).to₂).of_eq
  intro word
  induction word with
  | nil => rfl
  | cons bit tail previous =>
      cases bit with
      | consₗ => rfl
      | cons => rfl
      | bit0 => rfl
      | bit1 => exact congrArg (List.cons Γ'.bit0) previous

theorem primrec_trNat : Primrec trNat := by
  apply (Primrec.nat_rec₁ [] (primrec_increment.comp Primrec.snd).to₂).of_eq
  intro value
  induction value with
  | zero => rfl
  | succ value previous =>
      change increment (Nat.rec [] (fun _ bits => increment bits) value) = trNat (value + 1)
      rw [previous, increment_nat]

/-- Packing a main-stack letter uses a fixed finite alphabet map. -/
def pack (bit : Γ') : Alphabet :=
  (false, Function.update (fun _ => none) K'.main (some bit))

def bottomMarker (letter : Alphabet) : Alphabet := (true, letter.2)

def markBottom (word : List Alphabet) : List Alphabet :=
  bottomMarker word.headI :: word.tail

theorem primrec_markBottom : Primrec markBottom :=
  Primrec.list_cons.comp
    ((Primrec.dom_finite bottomMarker).comp Primrec.list_headI)
    Primrec.list_tail

/-- Canonical numeric input is a primitive recursive representation, independent of the program. -/
theorem primrec_tapeData : Primrec (fun value => FormalCompilation.tapeData [value]) := by
  have symbols : Primrec (fun value => trNat value ++ [Γ'.cons]) :=
    Primrec.list_append.comp primrec_trNat (Primrec.const [Γ'.cons])
  have reversed : Primrec (fun value => (trNat value ++ [Γ'.cons]).reverse) :=
    Primrec.list_reverse.comp symbols
  exact primrec_markBottom.comp (Primrec.list_map reversed
    ((Primrec.dom_finite pack).comp Primrec.snd).to₂)


/-- The fixed readout recovers a numeric answer from the complete final TM0 tape. -/
theorem decode_halt (source : ToPartrec.Code) (value : ℕ) :
    decodeTape (FormalCompilation.halt0 source [value]).Tape.right₀ = value := by
  change decodeTape ((Tape.mk' ∅ (ListBlank.mk (FormalCompilation.tapeData [value]))).right₀) = value
  rw [Tape.mk'_right₀, decodeTape_mk]
  exact decode_output value


set_option backward.isDefEq.respectTransparency false in
/-- The first packed output symbol is a delimiter and contributes no numeric bit. -/
theorem output_head_neutral (value : ℕ) :
    readSymbol 0 (FormalCompilation.tapeData [value]).headI = 0 := by
  change readSymbol 0 (TM2to1.trInit K'.main (trNat value ++ [Γ'.cons])).headI = 0
  simp [TM2to1.trInit, readSymbol, readBit]

theorem decode_output_tail (value : ℕ) :
    decodeWord (FormalCompilation.tapeData [value]).tail = value := by
  have neutral := output_head_neutral value
  have whole := decode_output value
  change decodeWord (FormalCompilation.tapeData [value]) = value at whole
  cases word : FormalCompilation.tapeData [value] with
  | nil => simpa only [word, List.tail_nil] using whole
  | cons head tail =>
      rw [word] at neutral whole
      change readSymbol 0 head = 0 at neutral
      simpa only [decodeWord, List.foldl_cons, neutral, List.tail_cons] using whole

/-- The right stack alone supplies the numeric answer; control and current head are unused. -/
theorem decode_halt_right (source : ToPartrec.Code) (value : ℕ) :
    decodeTape (FormalCompilation.halt0 source [value]).Tape.right = value := by
  change decodeTape (ListBlank.mk (FormalCompilation.tapeData [value])).tail = value
  rw [ListBlank.tail_mk, decodeTape_mk]
  exact decode_output_tail value

end Monodromy.CanonicalIO
