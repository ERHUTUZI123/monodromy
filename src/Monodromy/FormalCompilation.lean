module

public import Mathlib.Computability.TuringMachine.ToPartrec
public import Monodromy.FiniteSupport

/-!
# Partial recursive programs as finite Turing tables

Mathlib's stack evaluator is translated to a Post–Turing table and restricted
to its finite support. The source code fixes the table; its numeric arguments
are supplied through an explicit finite input word.
-/

@[expose] public section

namespace Monodromy.FormalCompilation

open Turing

abbrev Stack := PartrecToTM2.K'
abbrev Symbol := PartrecToTM2.Γ'
abbrev Store := Option Symbol
abbrev Label2 := PartrecToTM2.Λ'
abbrev Alphabet := TM2to1.Γ' Stack (fun _ => Symbol)

instance stackFintype : Fintype Stack where
  elems := {.main, .rev, .aux, .stack}
  complete := by intro value; cases value <;> simp

/-- The parameter fixes the distinguished initial label of the compiled table. -/
@[nolint unusedArguments]
def Control1 (_source : ToPartrec.Code) : Type :=
  TM2to1.Λ' Stack (fun _ => Symbol) Label2 Store

variable (source : ToPartrec.Code)

instance control1Inhabited : Inhabited (Control1 source) :=
  ⟨TM2to1.Λ'.normal (PartrecToTM2.trNormal source PartrecToTM2.Cont'.halt)⟩

def machine1 : Control1 source → TM1.Stmt Alphabet (Control1 source) Store :=
  TM2to1.tr PartrecToTM2.tr

def Control0 : Type := TM1to0.Λ' (machine1 source)

instance control0Inhabited : Inhabited (Control0 source) :=
  inferInstanceAs (Inhabited (TM1to0.Λ' (machine1 source)))

def machine0 : TM0.Machine Alphabet (Control0 source) := TM1to0.tr (machine1 source)

noncomputable def labels1 : Finset (Control1 source) :=
  TM2to1.trSupp PartrecToTM2.tr (PartrecToTM2.codeSupp source PartrecToTM2.Cont'.halt)

theorem supports1 : TM1.Supports (machine1 source) (labels1 source) := by
  let _ : Inhabited Label2 := ⟨PartrecToTM2.trNormal source PartrecToTM2.Cont'.halt⟩
  exact TM2to1.tr_supports PartrecToTM2.tr
    (PartrecToTM2.tr_supports source PartrecToTM2.Cont'.halt)

noncomputable def labels0 : Finset (Control0 source) := TM1to0.trStmts (machine1 source) (labels1 source)

theorem supports0 : TM0.Supports (machine0 source) (labels0 source : Set (Control0 source)) :=
  TM1to0.tr_supports (machine1 source) (supports1 source)

noncomputable def finiteSupport : FiniteSupport.Support (machine0 source) :=
  ⟨labels0 source, supports0 source⟩

omit source in
/-- Every list of numeric arguments has an explicit word over the finite tape alphabet. -/
def tapeData (values : List ℕ) : List Alphabet :=
  TM2to1.trInit PartrecToTM2.K'.main (PartrecToTM2.trList values)

theorem initial_relation (values : List ℕ) :
    TM2to1.TrCfg (PartrecToTM2.init source values)
      (TM1.init (tapeData values) : TM1.Cfg Alphabet (Control1 source) Store) := by
  let _ : Inhabited Label2 := ⟨PartrecToTM2.trNormal source PartrecToTM2.Cont'.halt⟩
  have initial := TM2to1.trCfg_init (Γ := fun _ : Stack => Symbol) (Λ := Label2) (σ := Store)
    PartrecToTM2.K'.main (PartrecToTM2.trList values)
  have same : (TM2.init PartrecToTM2.K'.main (PartrecToTM2.trList values) :
      TM2.Cfg (fun _ : Stack => Symbol) Label2 Store) = PartrecToTM2.init source values := by
    apply congrArg (fun storage => TM2.Cfg.mk
      (some (PartrecToTM2.trNormal source PartrecToTM2.Cont'.halt)) none storage)
    funext index
    cases index <;> rfl
  rw [same] at initial
  exact initial

/-- Projection to every stack determines the entire packed tape. -/
theorem relation_unique
    {configuration : TM2.Cfg (fun _ : Stack => Symbol) Label2 Store}
    {first second : TM1.Cfg Alphabet (Control1 source) Store}
    (first_related : TM2to1.TrCfg configuration first)
    (second_related : TM2to1.TrCfg configuration second) : first = second := by
  cases first_related with
  | mk first first_projection =>
      cases second_related with
      | mk second second_projection =>
          have same : first = second := by
            apply ListBlank.ext
            intro index
            funext column
            have projected := congrArg (fun word => ListBlank.nth word index)
              ((first_projection column).trans (second_projection column).symm)
            simpa only [proj_map_nth] using projected
          subst second
          rfl

theorem relation_stop
    {configuration : TM2.Cfg (fun _ : Stack => Symbol) Label2 Store}
    {target : TM1.Cfg Alphabet (Control1 source) Store}
    (related : TM2to1.TrCfg configuration target) :
    TM2to1.TrCfg (Λ := Label2) { configuration with l := none } { target with l := none } := by
  cases related with
  | mk contents projection => exact TM2to1.TrCfg.mk contents projection

def halt1 (values : List ℕ) : TM1.Cfg Alphabet (Control1 source) Store :=
  { (TM1.init (tapeData values) : TM1.Cfg Alphabet (Control1 source) Store) with l := none }

theorem halt_relation (values : List ℕ) :
    TM2to1.TrCfg (PartrecToTM2.halt values) (halt1 source values) :=
  relation_stop source (initial_relation source values)

/-- The complete result, including divergence, survives stack-to-tape translation. -/
theorem eval1 (values : List ℕ) :
    StateTransition.eval (TM1.step (machine1 source))
      (TM1.init (tapeData values) : TM1.Cfg Alphabet (Control1 source) Store) =
      halt1 source <$> source.eval values := by
  have source_evaluation := PartrecToTM2.tr_eval source values
  apply Part.ext
  intro target
  constructor
  · intro completed
    obtain ⟨source_result, related, finished⟩ := StateTransition.tr_eval_rev
      (TM2to1.tr_respects PartrecToTM2.tr) (initial_relation source values) completed
    rw [source_evaluation] at finished
    obtain ⟨value, value_finished, rfl⟩ := (Part.mem_map_iff _).mp finished
    exact (Part.mem_map_iff _).mpr
      ⟨value, value_finished, (relation_unique source related (halt_relation source value)).symm⟩
  · intro completed
    obtain ⟨result, result_finished, rfl⟩ := (Part.mem_map_iff _).mp completed
    have source_finished : PartrecToTM2.halt result ∈
        StateTransition.eval (TM2.step PartrecToTM2.tr) (PartrecToTM2.init source values) := by
      rw [source_evaluation]
      exact (Part.mem_map_iff _).mpr ⟨result, result_finished, rfl⟩
    obtain ⟨target, related, finished⟩ := StateTransition.tr_eval
      (TM2to1.tr_respects PartrecToTM2.tr) (initial_relation source values) source_finished
    have same := relation_unique source related (halt_relation source result)
    rw [same] at finished
    exact finished

def halt0 (values : List ℕ) : TM0.Cfg Alphabet (Control0 source) :=
  TM1to0.trCfg (machine1 source) (halt1 source values)

theorem initial0 (values : List ℕ) :
    TM1to0.trCfg (machine1 source) (TM1.init (tapeData values)) =
      (TM0.init (tapeData values) : TM0.Cfg Alphabet (Control0 source)) := rfl

/-- Compilation preserves the complete partial function on every numeric argument list. -/
theorem eval0 (values : List ℕ) :
    StateTransition.eval (TM0.step (machine0 source))
      (TM0.init (tapeData values) : TM0.Cfg Alphabet (Control0 source)) =
      halt0 source <$> source.eval values := by
  have translated := StateTransition.tr_eval' (TM1.step (machine1 source)) (TM0.step (machine0 source))
    (TM1to0.trCfg (machine1 source)) (TM1to0.tr_respects (machine1 source))
    (TM1.init (tapeData values))
  rw [initial0, eval1] at translated
  exact translated.trans (by rfl)

/-- The actual control carrier is finite; embedding preserves the entire final configuration. -/
theorem eval_finite (values : List ℕ) :
    (finiteSupport source).embed <$>
      StateTransition.eval (TM0.step (finiteSupport source).restrict) (TM0.init (tapeData values)) =
      halt0 source <$> source.eval values := by
  rw [← (finiteSupport source).eval_embed, (finiteSupport source).embed_init]
  exact eval0 source values

theorem halting_finite_iff (values : List ℕ) :
    (StateTransition.eval (TM0.step (finiteSupport source).restrict) (TM0.init (tapeData values))).Dom ↔
      (source.eval values).Dom := by
  have same := congrArg Part.Dom (eval_finite source values)
  exact same.to_iff

omit source in
/-- Every partial recursive unary numeric function has a finite table with exact encoded output. -/
theorem every_partrec {f : ℕ → Part ℕ} (partial_recursive : Partrec f) :
    ∃ source : ToPartrec.Code, ∀ input : ℕ,
      (finiteSupport source).embed <$>
        StateTransition.eval (TM0.step (finiteSupport source).restrict) (TM0.init (tapeData [input])) =
        (fun result => halt0 source [result]) <$> f input := by
  obtain ⟨source, correct⟩ := ToPartrec.Code.exists_code (Nat.Partrec'.part_iff₁.mpr partial_recursive)
  refine ⟨source, fun input => ?_⟩
  rw [eval_finite, correct ⟨[input], rfl⟩]
  rfl

end Monodromy.FormalCompilation
