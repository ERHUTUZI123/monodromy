module

public import Monodromy.FormalCompilation
public import Monodromy.CoverCompiler
public import Monodromy.Universality
import Mathlib.Tactic.FinCases

/-!
# Native finite-cover realization of partial recursive programs

The alphabet and argument encoding are fixed. Source code determines only a
finite cubic-cover program; every result represents the complete source tape.
-/

@[expose] public section

namespace Monodromy.NativeLowerBound

open Turing CoverExpressions FormalCompilation

abbrev letters : ℕ := Fintype.card Alphabet

noncomputable def inputWord (values : List ℕ) : List (Fin letters) :=
  (tapeData values).map (FiniteRenaming.toFin Alphabet)

/-- The initial integer state depends only on the arguments. -/
noncomputable def nativeInput (values : List ℕ) : Program.IntState 3 :=
  ![((inputWord values).headI.val : ℤ), 0, (BinaryBlocks.encode (inputWord values).tail : ℤ)]

variable (source : ToPartrec.Code)

abbrev FiniteControl := (finiteSupport source).Control

noncomputable def table : TM0.Machine (Fin letters) (Fin (Fintype.card (FiniteControl source))) :=
  FiniteRenaming.machine (finiteSupport source).restrict

noncomputable def program : Program 3 := CoverCompiler.compile (table source)

theorem program_usesRadix : (program source).UsesRadix 3 :=
  CoverCompiler.compile_usesRadix (table source)

noncomputable def initialStack (values : List ℕ) :
    TwoStacks.Configuration (Fin letters) (Fin (Fintype.card (FiniteControl source))) :=
  TwoStacks.init (inputWord values)

/-- Initial control is zero, so the program's control cardinality contributes no input data. -/
theorem initial_code (values : List ℕ) :
    CoverCompiler.code (initialStack source values) = nativeInput values := by
  funext register
  fin_cases register <;>
    simp [CoverCompiler.code, initialStack, TwoStacks.init, nativeInput, CoverCompiler.pc, finProdFinEquiv]

theorem initial_realize (values : List ℕ) :
    CoverCompiler.realize (initialStack source values) = Program.init (nativeInput values) := by
  unfold CoverCompiler.realize
  rw [initial_code]

theorem initial_decode (values : List ℕ) :
    TwoStacks.decode (initialStack source values) =
      FiniteRenaming.configuration
        (TM0.init (tapeData values) : TM0.Cfg Alphabet (FiniteControl source)) := by
  rw [FiniteRenaming.configuration_init]
  rfl

omit source in
noncomputable def unrename {Γ Q : Type} [Fintype Γ] [Inhabited Γ] [Fintype Q] [Inhabited Q]
    (configuration : TM0.Cfg (Fin (Fintype.card Γ)) (Fin (Fintype.card Q))) : TM0.Cfg Γ Q :=
  configuration.map (FiniteRenaming.fromFin Γ) (FiniteRenaming.fromFin Q)

omit source in
theorem unrename_configuration {Γ Q : Type} [Fintype Γ] [Inhabited Γ] [Fintype Q] [Inhabited Q]
    (configuration : TM0.Cfg Γ Q) : unrename (FiniteRenaming.configuration configuration) = configuration := by
  have roundtrip (word : ListBlank Γ) :
      (word.map (FiniteRenaming.toFin Γ)).map (FiniteRenaming.fromFin Γ) = word := by
    apply ListBlank.ext
    intro index
    simp
  rcases configuration with ⟨label, symbol, left, right⟩
  simp [unrename, FiniteRenaming.configuration, TM0.Cfg.map, Tape.map, roundtrip]

/-- Decode only the finite alphabet and support certificates; retain the complete tape. -/
noncomputable def raw (configuration :
    TwoStacks.Configuration (Fin letters) (Fin (Fintype.card (FiniteControl source)))) :
    TM0.Cfg Alphabet (Control0 source) :=
  (finiteSupport source).embed (unrename (TwoStacks.decode configuration))

/-- Complete source results are exactly the projection of the stack execution. -/
theorem raw_eval (values : List ℕ) :
    raw source <$> StateTransition.eval (TwoStacks.step (table source)) (initialStack source values) =
      halt0 source <$> source.eval values := by
  have stack_run := TwoStacks.eval_decode (table source) (initialStack source values)
  rw [initial_decode] at stack_run
  change StateTransition.eval (TM0.step (FiniteRenaming.machine (finiteSupport source).restrict))
    (FiniteRenaming.configuration (TM0.init (tapeData values))) = _ at stack_run
  rw [FiniteRenaming.eval_configuration] at stack_run
  change ((finiteSupport source).embed ∘ unrename) <$>
    (TwoStacks.decode <$> StateTransition.eval (TwoStacks.step (table source)) (initialStack source values)) = _
  rw [← stack_run]
  change (fun configuration => (finiteSupport source).embed
    (unrename (FiniteRenaming.configuration configuration))) <$>
      StateTransition.eval (TM0.step (finiteSupport source).restrict) (TM0.init (tapeData values)) = _
  have identity : (fun configuration : TM0.Cfg Alphabet (FiniteControl source) =>
      (finiteSupport source).embed (unrename (FiniteRenaming.configuration configuration))) =
        (finiteSupport source).embed := by
    funext configuration
    rw [unrename_configuration]
  rw [identity]
  exact eval_finite source values

/-- A native integer state carries one complete raw configuration. -/
def Represents (configuration : TM0.Cfg Alphabet (Control0 source)) (state : Program.IntState 3) : Prop :=
  ∃ stack : TwoStacks.Configuration (Fin letters) (Fin (Fintype.card (FiniteControl source))),
    raw source stack = configuration ∧ CoverCompiler.code stack = state

theorem represents_unique {first second : TM0.Cfg Alphabet (Control0 source)} {state : Program.IntState 3}
    (one : Represents source first state) (two : Represents source second state) : first = second := by
  obtain ⟨first_stack, first_raw, first_code⟩ := one
  obtain ⟨second_stack, second_raw, second_code⟩ := two
  have same := CoverCompiler.code_injective (first_code.trans second_code.symm)
  simpa only [same, second_raw] using first_raw.symm

/-- Native results and complete typed source results agree in both directions. -/
theorem result_iff (values : List ℕ) (target : TM0.Cfg Alphabet (Control0 source)) :
    target ∈ halt0 source <$> source.eval values ↔
      ∃ result, result ∈ Program.evalInt (program source) (nativeInput values) ∧
        Represents source target result := by
  constructor
  · intro finished
    rw [← raw_eval source values] at finished
    obtain ⟨stack, stack_finished, rfl⟩ := (Part.mem_map_iff _).mp finished
    refine ⟨CoverCompiler.code stack, ?_, stack, rfl, rfl⟩
    rw [← initial_code source values, program, CoverCompiler.evalInt_code]
    exact (Part.mem_map_iff _).mpr ⟨stack, stack_finished, rfl⟩
  · rintro ⟨result, finished, stack, raw_same, code_same⟩
    rw [← initial_code source values, program, CoverCompiler.evalInt_code] at finished
    obtain ⟨executed, executed_finished, same⟩ := (Part.mem_map_iff _).mp finished
    have stack_same := CoverCompiler.code_injective (same.trans code_same.symm)
    rw [stack_same] at executed_finished
    rw [← raw_eval source values]
    exact (Part.mem_map_iff _).mpr ⟨stack, executed_finished, raw_same⟩

theorem halting_iff (values : List ℕ) :
    (Program.evalInt (program source) (nativeInput values)).Dom ↔ (source.eval values).Dom := by
  have same : (Program.evalInt (program source) (nativeInput values)).Dom = (source.eval values).Dom := by
    calc
      _ = (StateTransition.eval (TwoStacks.step (table source)) (initialStack source values)).Dom := by
        rw [← initial_code source values, program, CoverCompiler.evalInt_code]
        rfl
      _ = (source.eval values).Dom := congrArg Part.Dom (raw_eval source values)
  exact same.to_iff

theorem native_halting_iff (values : List ℕ) :
    (Program.evalReal (program source) (Program.init (nativeInput values))).Dom ↔
      (source.eval values).Dom := by
  rw [Program.evalReal_init]
  exact halting_iff source values

omit source in
/-- Every partial recursive function is realized with the same argument encoding and cubic cover. -/
theorem every_partrec {f : ℕ → Part ℕ} (partial_recursive : Partrec f) :
    ∃ source : ToPartrec.Code, (program source).UsesRadix 3 ∧ ∀ input : ℕ,
      ((Program.evalInt (program source) (nativeInput [input])).Dom ↔ (f input).Dom) ∧
      ∀ target : TM0.Cfg Alphabet (Control0 source),
        target ∈ (fun result => halt0 source [result]) <$> f input ↔
          ∃ result, result ∈ Program.evalInt (program source) (nativeInput [input]) ∧
            Represents source target result := by
  obtain ⟨source, correct⟩ := ToPartrec.Code.exists_code (Nat.Partrec'.part_iff₁.mpr partial_recursive)
  refine ⟨source, program_usesRadix source, fun input => ?_⟩
  constructor
  · rw [halting_iff, correct ⟨[input], rfl⟩]
    rfl
  · intro target
    have result := result_iff source [input] target
    rw [correct ⟨[input], rfl⟩] at result
    exact result

end Monodromy.NativeLowerBound
