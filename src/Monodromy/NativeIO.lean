module

public import Monodromy.CanonicalIO
public import Monodromy.Effectiveness

/-!
# A fixed numeric interface

One primitive-recursive preparation and readout serve every finite native
program. A static prefix supplies the initial head symbol to the compiled
Turing table. Complete results are obtained by actual covering-space lifts;
the numeric readout recovers the right tape from its prime-three exponent.
-/

@[expose] public section

noncomputable section

namespace Monodromy.NativeInterface

open Turing CoupledContinuation

abbrev Alphabet := CanonicalIO.Alphabet
abbrev letters : ℕ := Fintype.card Alphabet

def word (input : ℕ) : List (Fin letters) :=
  (FormalCompilation.tapeData [input]).map (FiniteRenaming.toFin Alphabet)

def rightCode (input : ℕ) : ℕ := TapeCode.Readout.wordCode letters (word input).tail

/-- This preparation uses only the numeric argument and the fixed tape alphabet. -/
def inputLabels (input : ℕ) : Labels :=
  ((Int.ofNat (3 ^ rightCode input), 0), 3 * ((word input).headI.val : ℤ))

def read (letter : Fin letters) (value : ℕ) : ℕ :=
  CanonicalIO.readSymbol value (FiniteRenaming.fromFin Alphabet letter)

theorem read_neutral (value : ℕ) : read 0 value = value := by
  have blank : FiniteRenaming.fromFin Alphabet (0 : Fin letters) = default := by
    simpa only [Fin.default_eq_zero] using (FiniteRenaming.fromFin Alphabet).map_pt
  change CanonicalIO.readSymbol value (FiniteRenaming.fromFin Alphabet 0) = value
  rw [blank]
  exact CanonicalIO.read_blank value

theorem primrec_read (letter : Fin letters) : Primrec (read letter) :=
  CanonicalIO.primrec_readSymbol.comp Primrec.id
    (Primrec.const (FiniteRenaming.fromFin Alphabet letter))

/-- The total output map ignores every control address and the workspace counter. -/
def outputLabels (labels : Labels) : ℕ :=
  TapeCode.Readout.decode read (PrimeReadout.exponent 3 labels.1.1.toNat)

theorem primrec_word : Primrec word :=
  Primrec.list_map CanonicalIO.primrec_tapeData
    ((Primrec.dom_finite (fun letter : Alphabet => FiniteRenaming.toFin Alphabet letter)).comp Primrec.snd).to₂

theorem primrec_rightCode : Primrec rightCode :=
  (TapeCode.Readout.primrec_wordCode letters).comp (Primrec.list_tail.comp primrec_word)

theorem primrec_inputLabels : Primrec inputLabels := by
  have memory : Primrec (fun input : ℕ => Int.ofNat (3 ^ rightCode input)) :=
    IntegerPrimrec.ofNat.comp ((PrimeReadout.primrec_power 3).comp primrec_rightCode)
  have control : Primrec (fun input : ℕ => 3 * ((word input).headI.val : ℤ)) :=
    (IntegerPrimrec.scale 3).comp
      (IntegerPrimrec.ofNat.comp (Primrec.fin_val.comp (Primrec.list_headI.comp primrec_word)))
  exact (memory.pair (Primrec.const 0)).pair control

private theorem primrec_toNat : Primrec Int.toNat :=
  (IntegerPrimrec.cases Primrec.id
    (Primrec.snd : Primrec (Prod.snd : ℤ × ℕ → ℕ)).to₂
    (Primrec.const 0).to₂).of_eq (fun value => by cases value <;> rfl)

theorem primrec_outputLabels : Primrec outputLabels :=
  (TapeCode.Readout.primrec_decode read primrec_read).comp
    ((PrimeReadout.primrec_exponent 3).comp
      (primrec_toNat.comp (Primrec.fst.comp Primrec.fst)))

variable (source : ToPartrec.Code)

abbrev FiniteControl : Type := (FormalCompilation.finiteSupport source).Control
abbrev controls : ℕ := Fintype.card (FiniteControl source)

def table : TM0.Machine (Fin letters) (Fin (controls source)) :=
  FiniteRenaming.machine (FormalCompilation.finiteSupport source).restrict

abbrev bodySize : ℕ := Counter.Compression.size
  (NativeTuring.source3 letters (controls source) (table source))

def body : Counter.Program 2 (bodySize source) :=
  NativeTuring.source2 letters (controls source) (table source)

def entries (letter : Fin letters) : Fin (bodySize source) :=
  Counter.Compression.dispatch
    (NativeTuring.source3 letters (controls source) (table source))
    (Counter.TuringCompiler.dispatch letters (controls source) (0, letter))

def counterProgram : Counter.Program 2 (letters + bodySize source) :=
  Counter.EntryDispatch.program (body source) (entries source)

instance prefix_nonempty : NeZero (letters + bodySize source) := by
  have positive : 0 < letters := Fintype.card_pos
  exact ⟨by omega⟩

/-- The only added source rows are one static entry jump for each input-head letter. -/
def program : CoupledContinuation.Program ((letters + bodySize source) * 3) :=
  CounterContinuation.compile (counterProgram source)

def initial (input : ℕ) : Counter.Configuration 2 (letters + bodySize source) :=
  Counter.EntryDispatch.entryState (word input).headI ![3 ^ rightCode input, 0]

/-- The fixed integer preparation is precisely the native encoding of the finite entry prefix. -/
theorem initial_encode (input : ℕ) :
    CounterContinuation.encode (initial source input) = Labels.prepare (inputLabels input) := by
  simp [initial, Counter.EntryDispatch.entryState, CounterContinuation.encode,
    CounterContinuation.label_eq, Labels.prepare, inputLabels]

/-- Static input-head dispatch supplies the complete, correctly encoded initial tape configuration. -/
theorem initial_body (input : ℕ) :
    (⟨entries source (word input).headI, ![3 ^ rightCode input, 0]⟩ :
      Counter.Configuration 2 (bodySize source)) =
      Counter.Compression.encode
        (NativeTuring.source3 letters (controls source) (table source))
        (Counter.TuringCompiler.encode letters (controls source)
          (TM0.init (word input) : TM0.Cfg (Fin letters) (Fin (controls source)))) := by
  simp [Counter.Compression.encode, Counter.TuringCompiler.encode,
    Counter.TuringCompiler.counters, PrimeCode.encode, TM0.init,
    Tape.mk₁, Tape.mk₂, Tape.mk', ListBlank.tail_mk, entries, rightCode,
    TapeCode.Readout.wordCode, Fin.default_eq_zero]

/-- Entry dispatch preserves complete source results before the existing native compilation. -/
theorem prefix_eval (input : ℕ) :
    Counter.eval (counterProgram source) (initial source input) =
      Counter.mapConfiguration (Fin.natAdd letters) <$>
        Counter.eval (body source)
          (Counter.Compression.encode
            (NativeTuring.source3 letters (controls source) (table source))
            (Counter.TuringCompiler.encode letters (controls source)
              (TM0.init (word input) : TM0.Cfg (Fin letters) (Fin (controls source))))) := by
  have entered := Counter.EntryDispatch.eval_prefix (body source) (entries source)
    (word input).headI ![3 ^ rightCode input, 0] rfl
  rw [initial_body] at entered
  exact entered


/-- Integer labels describe the native encoding of an ordinary two-counter state. -/
def counterLabels {m : ℕ} (state : Counter.Configuration 2 m) : Labels :=
  (((state.counters 0 : ℤ), (state.counters 1 : ℤ)), CounterContinuation.label state.pc 0)

theorem counter_prepare {m : ℕ} (state : Counter.Configuration 2 m) :
    Labels.prepare (counterLabels state) = CounterContinuation.encode state := rfl

def resultLabels (state : TM0.Cfg (Fin letters) (Fin (controls source))) : Labels :=
  counterLabels (Counter.mapConfiguration (Fin.natAdd letters)
    (Counter.Compression.encode
      (NativeTuring.source3 letters (controls source) (table source))
      (Counter.TuringCompiler.encode letters (controls source) state)))

/-- Complete native results agree with the finite Turing table after the static entry prefix. -/
theorem native_eval (input : ℕ) :
    (program source).eval (Labels.prepare (inputLabels input)) =
      Labels.prepare <$> (resultLabels source <$>
        StateTransition.eval (TM0.step (table source))
          (TM0.init (word input))) := by
  unfold program
  rw [← initial_encode source input, CounterContinuation.eval_encode, prefix_eval]
  simp only [body, NativeTuring.source2]
  rw [Counter.Compression.eval_encode]
  simp only [NativeTuring.source3]
  rw [Counter.TuringCompiler.eval_encode]
  rfl

private theorem part_map_injective {A B : Type*} (prepare : A → B)
    (faithful : Function.Injective prepare) : Function.Injective (Part.map prepare) := by
  intro first second same
  apply Part.ext
  intro value
  have member (part : Part A) : prepare value ∈ Part.map prepare part ↔ value ∈ part := by
    rw [Part.mem_map_iff]
    constructor
    · rintro ⟨found, belongs, encoded⟩
      have recovered : found = value := faithful encoded
      simpa only [recovered] using belongs
    · intro belongs
      exact ⟨value, belongs, rfl⟩
  have observed : prepare value ∈ Part.map prepare first ↔ prepare value ∈ Part.map prepare second := by
    rw [same]
  exact (member first).symm.trans (observed.trans (member second))

/-- The arithmetic interpretation is derived from actual native execution. -/
theorem evalInt_input (input : ℕ) :
    (program source).evalInt (inputLabels input) =
      resultLabels source <$> StateTransition.eval (TM0.step (table source))
        (TM0.init (word input)) := by
  apply part_map_injective Labels.prepare CoupledContinuation.prepare_injective
  have same := native_eval source input
  rw [CoupledContinuation.Program.eval_prepareInt] at same
  simpa only [Part.map_eq_map] using same

private theorem exponent_code (registers : Fin 3 → ℕ) :
    PrimeReadout.exponent 3 (PrimeCode.encode registers) = registers 1 := by
  rw [PrimeReadout.exponent_eq_factorization (by decide : Nat.Prime 3)]
  simpa [PrimeCode.prime] using PrimeCode.factorization_encode registers (1 : Fin 3)

/-- The right tape is read from the prime-three exponent; its head and control are unnecessary. -/
theorem output_result (state : TM0.Cfg (Fin letters) (Fin (controls source))) :
    outputLabels (resultLabels source state) =
      TapeCode.Readout.decode read (TapeCode.encode state.Tape.right) := by
  change TapeCode.Readout.decode read
    (PrimeReadout.exponent 3
      (PrimeCode.encode (Counter.TuringCompiler.counters
        (TapeCode.encode state.Tape.left) (TapeCode.encode state.Tape.right)))) = _
  rw [exponent_code]
  rfl

/-- Pointed alphabet renaming preserves the complete blank-invariant numeric fold. -/
theorem decode_renamed_tape (tape : ListBlank Alphabet) :
    TapeCode.Readout.decode read (TapeCode.encode (tape.map (FiniteRenaming.toFin Alphabet))) =
      CanonicalIO.decodeTape tape := by
  rw [TapeCode.Readout.decode_tape read read_neutral]
  refine ListBlank.induction_on tape (fun word => ?_)
  simp [ListBlank.map_mk, TapeCode.Readout.tapeFold_mk, CanonicalIO.decodeTape_mk,
    CanonicalIO.decodeWord, List.foldl_map, read]

def rawOutput (state : TM0.Cfg Alphabet (FormalCompilation.Control0 source)) : ℕ :=
  CanonicalIO.decodeTape state.Tape.right

theorem output_renamed (state : TM0.Cfg Alphabet (FiniteControl source)) :
    outputLabels (resultLabels source (FiniteRenaming.configuration state)) =
      rawOutput source ((FormalCompilation.finiteSupport source).embed state) := by
  rw [output_result]
  exact decode_renamed_tape state.Tape.right

theorem renamed_initial (input : ℕ) :
    FiniteRenaming.configuration
      (TM0.init (FormalCompilation.tapeData [input]) :
        TM0.Cfg Alphabet (FiniteControl source)) =
      (TM0.init (word input) : TM0.Cfg (Fin letters) (Fin (controls source))) := by
  simpa only [word] using
    (FiniteRenaming.configuration_init (Q := FiniteControl source)
      (FormalCompilation.tapeData [input]))

/-- Numeric output is the fixed right-tape readout of the complete finite-support execution. -/
theorem numeric_eval (input : ℕ) :
    outputLabels <$> (program source).evalInt (inputLabels input) =
      rawOutput source <$> ((FormalCompilation.finiteSupport source).embed <$>
        StateTransition.eval (TM0.step (FormalCompilation.finiteSupport source).restrict)
          (TM0.init (FormalCompilation.tapeData [input]))) := by
  rw [evalInt_input, ← renamed_initial source input]
  simp only [table]
  rw [FiniteRenaming.eval_configuration]
  simp only [Part.map_eq_map, Part.map_map]
  apply congrArg (fun reader => Part.map reader
    (StateTransition.eval (TM0.step (FormalCompilation.finiteSupport source).restrict)
      (TM0.init (FormalCompilation.tapeData [input]))))
  funext state
  exact output_renamed source state

omit source in
/-- Every partial recursive function has an actual native realization with the same numeric interface. -/
theorem every_partrec {function : ℕ → Part ℕ} (effective : Partrec function) :
    ∃ source : ToPartrec.Code, ∀ input : ℕ,
      outputLabels <$> (program source).evalInt (inputLabels input) = function input := by
  obtain ⟨source, correct⟩ := FormalCompilation.every_partrec effective
  refine ⟨source, fun input => ?_⟩
  rw [numeric_eval, correct input]
  change Part.map (rawOutput source)
    (Part.map (fun result => FormalCompilation.halt0 source [result]) (function input)) = function input
  rw [Part.map_map]
  apply Part.map_id'
  intro result
  exact CanonicalIO.decode_halt_right source result

omit source in
/-- Prepared lattice membership is exactly the graph of the actual native partial execution. -/
theorem prepared_result_iff {degree : ℕ} [NeZero degree]
    (native : CoupledContinuation.Program degree) (initial result : Labels) :
    Labels.prepare result ∈ native.eval (Labels.prepare initial) ↔ result ∈ native.evalInt initial := by
  rw [CoupledContinuation.Program.eval_prepareInt, Part.map_eq_map, Part.mem_map_iff]
  constructor
  · rintro ⟨found, completed, same⟩
    have recovered : found = result := CoupledContinuation.prepare_injective same
    simpa only [recovered] using completed
  · intro completed
    exact ⟨result, completed, rfl⟩

omit source in
/-- The lower-bound graph is stated directly in terms of actual geometric program results. -/
theorem every_partrec_graph {function : ℕ → Part ℕ} (effective : Partrec function) :
    ∃ source : ToPartrec.Code, ∀ input value : ℕ,
      value ∈ function input ↔ ∃ labels : Labels,
        Labels.prepare labels ∈ (program source).eval (Labels.prepare (inputLabels input)) ∧
          outputLabels labels = value := by
  obtain ⟨source, correct⟩ := every_partrec effective
  refine ⟨source, fun input value => ?_⟩
  rw [← correct input, Part.map_eq_map, Part.mem_map_iff]
  constructor
  · rintro ⟨labels, completed, output⟩
    exact ⟨labels, (prepared_result_iff _ _ _).mpr completed, output⟩
  · rintro ⟨labels, completed, output⟩
    exact ⟨labels, (prepared_result_iff _ _ _).mp completed, output⟩

omit source in
/-- The same fixed interface preserves the ordinary partial-recursive upper bound. -/
theorem effective_execution {degree : ℕ} [NeZero degree]
    (native : CoupledContinuation.Program degree) :
    Partrec (fun input => outputLabels <$> native.evalInt (inputLabels input)) :=
  native.partrec_with_io primrec_inputLabels primrec_outputLabels

end Monodromy.NativeInterface
