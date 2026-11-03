module

public import Monodromy.CanonicalIO
public import Monodromy.NativeLowerBound
public import Monodromy.BlockCoding
public import Monodromy.IntegerPrimrec
import Mathlib.Tactic.FinCases

/-!
# A fixed numeric interface for native cover computation

Input is the canonical numeric tape in the three retained coordinates.
Output reads only the right word branch. The same two maps serve every
source program; their primitive recursive certificates account for the I/O.
-/

@[expose] public section

namespace Monodromy.NativeIO

open Turing CoverExpressions FormalCompilation NativeLowerBound

noncomputable def input (value : ℕ) : Program.IntState 3 := nativeInput [value]

noncomputable def output (state : Program.IntState 3) : ℕ :=
  CanonicalIO.decodeWord ((BinaryBlocks.decode (state 2).toNat).map (FiniteRenaming.fromFin Alphabet))

/-- Finite alphabet names round-trip independently of the source table. -/
theorem inputWord_roundtrip (values : List ℕ) :
    (inputWord values).map (FiniteRenaming.fromFin Alphabet) = tapeData values := by
  simp [inputWord, List.map_map, Function.comp_def]

/-- Projecting the raw configuration's right tape uses no control information. -/
theorem raw_right (source : ToPartrec.Code)
    (stack : TwoStacks.Configuration (Fin letters) (Fin (Fintype.card (FiniteControl source)))) :
    (raw source stack).Tape.right =
      ListBlank.mk (stack.right.map (FiniteRenaming.fromFin Alphabet)) := rfl

/-- Every represented canonical final tape has exactly the fixed numeric readout. -/
theorem output_represents (source : ToPartrec.Code) (value : ℕ) (state : Program.IntState 3)
    (represented : Represents source (halt0 source [value]) state) : output state = value := by
  obtain ⟨stack, raw_same, code_same⟩ := represented
  rw [← code_same]
  change CanonicalIO.decodeWord
    ((BinaryBlocks.decode ((BinaryBlocks.encode stack.right : ℤ).toNat)).map
      (FiniteRenaming.fromFin Alphabet)) = value
  rw [Int.toNat_natCast, BinaryBlocks.decode_encode]
  rw [← CanonicalIO.decodeTape_mk]
  have right_same := congrArg (fun configuration : TM0.Cfg Alphabet (Control0 source) =>
    configuration.Tape.right) raw_same
  rw [raw_right] at right_same
  rw [right_same]
  exact CanonicalIO.decode_halt_right source value

theorem primrec_inputWord : Primrec (fun value => inputWord [value]) :=
  Primrec.list_map CanonicalIO.primrec_tapeData
    ((Primrec.dom_finite (fun letter : Alphabet => FiniteRenaming.toFin Alphabet letter)).comp Primrec.snd).to₂

/-- Input prepares a fixed representation rather than performing the requested computation. -/
theorem primrec_input : Primrec input := by
  apply Primrec.fin_curry.mpr
  apply (Primrec.fin_curry₁.mpr ?_).swap
  intro register
  fin_cases register
  · exact IntegerPrimrec.ofNat.comp (Primrec.fin_val.comp (Primrec.list_headI.comp primrec_inputWord))
  · exact Primrec.const 0
  · exact IntegerPrimrec.ofNat.comp
      (BinaryBlocks.primrec_encode.comp (Primrec.list_tail.comp primrec_inputWord))

/-- The final decoder is the same primitive recursive map for all native programs. -/
theorem primrec_output : Primrec output := by
  have coordinate : Primrec (fun state : Program.IntState 3 => state 2) :=
    Primrec.fin_app.comp Primrec.id (Primrec.const 2)
  have decoded : Primrec (fun state : Program.IntState 3 => BinaryBlocks.decode (a := letters) (state 2).toNat) :=
    BinaryBlocks.primrec_decode.comp (IntegerPrimrec.toNat.comp coordinate)
  exact CanonicalIO.primrec_decodeWord.comp (Primrec.list_map decoded
    ((Primrec.dom_finite (fun letter : Fin letters => FiniteRenaming.fromFin Alphabet letter)).comp Primrec.snd).to₂)

end Monodromy.NativeIO
