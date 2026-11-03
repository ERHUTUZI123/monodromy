module

public import Monodromy.CoverPrograms
public import Monodromy.CoverTables
public import Monodromy.TwoStacks
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Finite Turing tables through one cubic cover

Letters occupy finite binary blocks in the ternary tower. Every table query
and memory descent uses the same cubic observation; depth carries the finite
alphabet and control information.
-/

@[expose] public section

namespace Monodromy.CoverCompiler

open Turing CoverExpressions

variable {a q : ℕ}

def pc (label : Fin q) (symbol : Fin a) : ℤ :=
  (finProdFinEquiv (label, symbol)).val

def code (configuration : TwoStacks.Configuration (Fin a) (Fin q)) : Fin 3 → ℤ :=
  ![pc configuration.q configuration.head,
    (BinaryBlocks.encode configuration.left : ℤ), (BinaryBlocks.encode configuration.right : ℤ)]

theorem address_bound (n : ℕ) : n < 3 ^ n := by
  induction n with
  | zero => decide
  | succ n previous => rw [pow_succ]; omega

def address {N : ℕ} (index : Fin N) : Fin (3 ^ N) :=
  ⟨index.val, index.isLt.trans (address_bound N)⟩

theorem residue_fin {N : ℕ} (index : Fin N) :
    Ternary.residue N (index.val : ℤ) = address index := by
  apply Fin.ext
  have casted : ((Ternary.residue N (index.val : ℤ)).val : ℤ) = (index.val : ℤ) := by
    rw [Ternary.residue_cast, Int.emod_eq_of_lt (by omega)]
    exact_mod_cast (address index).isLt
  exact_mod_cast casted

theorem residue_word (letter : Fin a) (tail : List (Fin a)) :
    Ternary.residue a (BinaryBlocks.encode (letter :: tail) : ℤ) =
      ⟨BinaryBlocks.digit letter, BinaryBlocks.digit_lt letter⟩ := by
  apply Fin.ext
  have casted : ((Ternary.residue a (BinaryBlocks.encode (letter :: tail) : ℤ)).val : ℤ) =
      (BinaryBlocks.digit letter : ℤ) := by
    rw [Ternary.residue_cast, ← Int.natCast_emod, BinaryBlocks.encode_cons_mod]
  exact_mod_cast casted

theorem quotient_word (word : List (Fin a)) :
    (BinaryBlocks.encode word : ℤ) / (3 : ℤ) ^ a =
      (BinaryBlocks.encode word.tail : ℤ) := by
  have quotient : (BinaryBlocks.encode word : ℤ) / ((3 ^ a : ℕ) : ℤ) =
      (BinaryBlocks.encode word.tail : ℤ) := by
    rw [← Int.natCast_ediv]
    cases word <;> simp
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using quotient

variable [NeZero a] [NeZero q]

def headValue (label : Fin q) (index : Fin (3 ^ a)) : ℤ :=
  pc label (default : Fin a) + ∑ letter : Fin a,
    if BinaryBlocks.digit letter = index.val then pc label letter - pc label (default : Fin a) else 0

omit [NeZero q] in
theorem headValue_zero (label : Fin q) : headValue (a := a) label 0 = pc label (default : Fin a) := by
  simp [headValue, ne_of_gt (BinaryBlocks.digit_positive _)]

omit [NeZero q] in
theorem headValue_letter (label : Fin q) (letter : Fin a) :
    headValue label ⟨BinaryBlocks.digit letter, BinaryBlocks.digit_lt letter⟩ = pc label letter := by
  have condition (other : Fin a) :
      (BinaryBlocks.digit other = BinaryBlocks.digit letter) ↔ other = letter :=
    BinaryBlocks.digit_injective.eq_iff
  simp only [headValue, condition]
  simp

def readHead (label : Fin q) (key : Term 3) : Term 3 :=
  Ternary.selectPower a key (fun index => .integerConst (headValue label index))

def push (symbol : Fin a) (key : Term 3) : Term 3 :=
  .add (.integerConst (BinaryBlocks.digit symbol)) (.integerScale ((3 ^ a : ℕ) : ℤ) key)

omit [NeZero q] in
theorem eval_readHead (label : Fin q) (word : List (Fin a)) (key : Term 3) (point : Fin 3 → ℤ)
    (key_value : CoverExpressions.evalInt key point = (BinaryBlocks.encode word : ℤ)) :
    CoverExpressions.evalInt (readHead (a := a) label key) point = pc label word.headI := by
  rw [readHead, Ternary.eval_selectPower, key_value]
  change headValue label (Ternary.residue a (BinaryBlocks.encode word : ℤ)) = pc label word.headI
  cases word with
  | nil => simpa [Ternary.residue] using headValue_zero (a := a) label
  | cons letter tail => simpa only [residue_word, List.headI_cons] using headValue_letter label letter

def row (machine : TM0.Machine (Fin a) (Fin q)) (index : Fin (q * a)) : Fin 3 → Term 3 :=
  let (label, symbol) := finProdFinEquiv.symm index
  match machine label symbol with
  | none => fun register => .coord register
  | some (target, .write value) => ![.integerConst (pc target value), .coord 1, .coord 2]
  | some (target, .move .left) =>
      ![readHead (a := a) target (.coord 1), Ternary.quotientPower a (.coord 1), push symbol (.coord 2)]
  | some (target, .move .right) =>
      ![readHead (a := a) target (.coord 2), push symbol (.coord 1), Ternary.quotientPower a (.coord 2)]

def halted (machine : TM0.Machine (Fin a) (Fin q)) (index : Fin (q * a)) : Bool :=
  let (label, symbol) := finProdFinEquiv.symm index
  (machine label symbol).isNone

def rows (machine : TM0.Machine (Fin a) (Fin q)) (index : Fin (3 ^ (q * a))) : Fin 3 → Term 3 :=
  if valid : index.val < q * a then row machine ⟨index.val, valid⟩ else fun register => .coord register

def stopRow (machine : TM0.Machine (Fin a) (Fin q)) (index : Fin (3 ^ (q * a))) : Guard 3 :=
  .constant (if valid : index.val < q * a then halted machine ⟨index.val, valid⟩ else true)

/-- All addresses beyond the source table are stationary halt sentinels. -/
def compile (machine : TM0.Machine (Fin a) (Fin q)) : Program 3 where
  updates register := Ternary.selectPower (q * a) (.coord 0) (fun index => rows machine index register)
  stop := Ternary.selectGuardPower (q * a) (.coord 0) (stopRow machine)

theorem stop_code (machine : TM0.Machine (Fin a) (Fin q))
    (configuration : TwoStacks.Configuration (Fin a) (Fin q)) :
    Guard.evalInt (compile machine).stop (code configuration) =
      (machine configuration.q configuration.head).isNone := by
  simp only [compile, Ternary.eval_selectGuardPower, CoverExpressions.evalInt, code, Matrix.cons_val_zero,
    pc, residue_fin, stopRow, address, Guard.evalInt, Fin.isLt, ↓reduceDIte,
    halted]
  change (machine (finProdFinEquiv.symm (finProdFinEquiv (configuration.q, configuration.head))).1
    (finProdFinEquiv.symm (finProdFinEquiv (configuration.q, configuration.head))).2).isNone = _
  rw [Equiv.symm_apply_apply]

/-- A static expression row exactly performs its reference tape operation. -/
theorem row_code (machine : TM0.Machine (Fin a) (Fin q))
    (configuration : TwoStacks.Configuration (Fin a) (Fin q)) :
    (fun register => CoverExpressions.evalInt
      (row machine (finProdFinEquiv (configuration.q, configuration.head)) register)
      (code configuration)) =
      code ((TwoStacks.step machine configuration).getD configuration) := by
  simp only [row, Equiv.symm_apply_apply]
  cases transition : machine configuration.q configuration.head with
  | none => simp [TwoStacks.step, transition, CoverExpressions.evalInt]
  | some instruction =>
      rcases instruction with ⟨target, instruction⟩
      cases instruction with
      | write value =>
          funext register
          fin_cases register <;>
            simp [TwoStacks.step, transition, TwoStacks.write, code, CoverExpressions.evalInt]
      | move direction =>
          cases direction <;>
            funext register <;>
            fin_cases register <;>
            simp [TwoStacks.step, transition, TwoStacks.move, code, push, CoverExpressions.evalInt,
              Ternary.eval_quotientPower, quotient_word, BinaryBlocks.encode_cons]
          all_goals first
            | exact eval_readHead target configuration.left (.coord 1) _ rfl
            | exact eval_readHead target configuration.right (.coord 2) _ rfl

theorem updates_code (machine : TM0.Machine (Fin a) (Fin q))
    (configuration : TwoStacks.Configuration (Fin a) (Fin q)) :
    (fun register => CoverExpressions.evalInt ((compile machine).updates register) (code configuration)) =
      code ((TwoStacks.step machine configuration).getD configuration) := by
  funext register
  change CoverExpressions.evalInt
    (Ternary.selectPower (q * a) (.coord 0) (fun index => rows machine index register))
    (code configuration) = _
  rw [Ternary.eval_selectPower]
  change CoverExpressions.evalInt
    (rows machine (Ternary.residue (q * a) (pc configuration.q configuration.head)) register)
    (code configuration) = _
  rw [pc, residue_fin]
  simpa only [rows, address, Fin.isLt, ↓reduceDIte] using congrFun (row_code machine configuration) register

theorem nextInt_code (machine : TM0.Machine (Fin a) (Fin q))
    (configuration : TwoStacks.Configuration (Fin a) (Fin q)) :
    Program.nextInt (compile machine) (code configuration) =
      code ((TwoStacks.step machine configuration).getD configuration) := by
  funext register
  change CoverExpressions.evalInt
    (Guard.gate (compile machine).stop (.coord register) ((compile machine).updates register))
    (code configuration) = _
  rw [Guard.eval_gate, stop_code]
  cases transition : machine configuration.q configuration.head with
  | none => simp [TwoStacks.step, transition, CoverExpressions.evalInt]
  | some instruction =>
      simpa only [Option.isNone_some, Bool.false_eq_true, ↓reduceIte] using
        congrFun (updates_code machine configuration) register

theorem stepInt_code (machine : TM0.Machine (Fin a) (Fin q))
    (configuration : TwoStacks.Configuration (Fin a) (Fin q)) :
    Program.stepInt (compile machine) (code configuration) =
      (TwoStacks.step machine configuration).map code := by
  unfold Program.stepInt
  rw [stop_code, nextInt_code]
  cases transition : machine configuration.q configuration.head <;>
    simp [TwoStacks.step, transition]

omit [NeZero q] in
theorem readHead_usesRadix (label : Fin q) (key : Term 3) (uses : UsesRadix 3 key) :
    UsesRadix 3 (readHead (a := a) label key) :=
  Ternary.selectPower_usesRadix a key _ uses (fun _ => trivial)

theorem row_usesRadix (machine : TM0.Machine (Fin a) (Fin q))
    (index : Fin (q * a)) (register : Fin 3) : UsesRadix 3 (row machine index register) := by
  rcases position : finProdFinEquiv.symm index with ⟨label, symbol⟩
  simp only [row, position]
  cases transition : machine label symbol with
  | none => trivial
  | some instruction =>
      rcases instruction with ⟨target, instruction⟩
      cases instruction with
      | write value => fin_cases register <;> simp [UsesRadix]
      | move direction =>
          cases direction <;> fin_cases register <;> simp [push, UsesRadix]
          all_goals first
            | exact readHead_usesRadix _ _ trivial
            | exact Ternary.quotientPower_usesRadix _ _ trivial

theorem compile_usesRadix (machine : TM0.Machine (Fin a) (Fin q)) :
    (compile machine).UsesRadix 3 := by
  constructor
  · intro register
    change UsesRadix 3 (Ternary.selectPower (q * a) (.coord 0) (fun index => rows machine index register))
    apply Ternary.selectPower_usesRadix (q * a) (.coord 0)
      (fun index => rows machine index register) (by trivial)
    intro index
    unfold rows
    split_ifs
    · exact row_usesRadix machine _ register
    · trivial
  · change Guard.UsesRadix 3 (Ternary.selectGuardPower (q * a) (.coord 0) (stopRow machine))
    apply Ternary.selectGuardPower_usesRadix (q * a) (.coord 0) (stopRow machine) (by trivial)
    intro index
    unfold stopRow
    trivial

/-- Stopping and every executed return retain the same fixed cubic observation. -/
theorem returning_usesRadix (machine : TM0.Machine (Fin a) (Fin q)) (index : Fin 3) :
    UsesRadix 3 ((compile machine).returning index) :=
  Program.returning_usesRadix (compile machine) (compile_usesRadix machine) index

theorem stopIndicator_usesRadix (machine : TM0.Machine (Fin a) (Fin q)) :
    UsesRadix 3 ((compile machine).stop.compile) :=
  Guard.compile_usesRadix (compile machine).stop (compile_usesRadix machine).2

omit [NeZero a] [NeZero q] in
theorem code_injective : Function.Injective (@code a q) := by
  intro first second same
  have positions : (first.q, first.head) = (second.q, second.head) :=
    finProdFinEquiv.injective (Fin.ext (Nat.cast_injective (congrFun same 0)))
  have left : first.left = second.left :=
    BinaryBlocks.encode_injective (Nat.cast_injective (congrFun same 1))
  have right : first.right = second.right :=
    BinaryBlocks.encode_injective (Nat.cast_injective (congrFun same 2))
  have labels := congrArg Prod.fst positions
  have heads := congrArg Prod.snd positions
  cases first
  cases second
  cases labels
  cases left
  cases heads
  cases right
  rfl

/-- The compiled integer program agrees on the entire final tape presentation. -/
theorem evalInt_code (machine : TM0.Machine (Fin a) (Fin q))
    (configuration : TwoStacks.Configuration (Fin a) (Fin q)) :
    Program.evalInt (compile machine) (code configuration) =
      code <$> StateTransition.eval (TwoStacks.step machine) configuration := by
  have refinement : StateTransition.Respects (TwoStacks.step machine)
      (Program.stepInt (compile machine)) (fun first second => code first = second) := by
    apply StateTransition.fun_respects.mpr
    intro source
    cases result : TwoStacks.step machine source with
    | none =>
        change Program.stepInt (compile machine) (code source) = none
        simp [stepInt_code, result]
    | some successor =>
        apply Relation.TransGen.single
        simp [stepInt_code, result]
  exact StateTransition.tr_eval' (TwoStacks.step machine) (Program.stepInt (compile machine))
    code refinement configuration

noncomputable def realize (configuration : TwoStacks.Configuration (Fin a) (Fin q)) : Program.Memory 3 :=
  Program.init (code configuration)

omit [NeZero a] [NeZero q] in
theorem realize_injective : Function.Injective (@realize a q) := by
  intro first second same
  exact code_injective (Program.init_injective same)

/-- Native analytic execution and integer specification have the same complete partial result. -/
theorem evalReal_realize (machine : TM0.Machine (Fin a) (Fin q))
    (configuration : TwoStacks.Configuration (Fin a) (Fin q)) :
    Program.evalReal (compile machine) (realize configuration) =
      realize <$> StateTransition.eval (TwoStacks.step machine) configuration := by
  unfold realize
  rw [Program.evalReal_init, evalInt_code]
  simp only [Functor.map_map]

theorem halting_iff (machine : TM0.Machine (Fin a) (Fin q))
    (configuration : TwoStacks.Configuration (Fin a) (Fin q)) :
    (Program.evalReal (compile machine) (realize configuration)).Dom ↔
      (StateTransition.eval (TwoStacks.step machine) configuration).Dom := by
  rw [evalReal_realize]
  rfl

theorem divergence_iff (machine : TM0.Machine (Fin a) (Fin q))
    (configuration : TwoStacks.Configuration (Fin a) (Fin q)) :
    ¬ (Program.evalReal (compile machine) (realize configuration)).Dom ↔
      ¬ (StateTransition.eval (TwoStacks.step machine) configuration).Dom :=
  not_congr (halting_iff machine configuration)

def tick (machine : TM0.Machine (Fin a) (Fin q))
    (configuration : TwoStacks.Configuration (Fin a) (Fin q)) :
    TwoStacks.Configuration (Fin a) (Fin q) :=
  (TwoStacks.step machine configuration).getD configuration

/-- Each compiled return performs exactly one reference return, including stationary halt. -/
theorem iterate_code (machine : TM0.Machine (Fin a) (Fin q)) (rounds : ℕ)
    (configuration : TwoStacks.Configuration (Fin a) (Fin q)) :
    ((Program.nextInt (compile machine))^[rounds]) (code configuration) =
      code (((tick machine)^[rounds]) configuration) := by
  induction rounds with
  | zero => rfl
  | succ rounds previous =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', previous, nextInt_code]
      rfl

theorem advance_iterate_realize (machine : TM0.Machine (Fin a) (Fin q)) (rounds : ℕ)
    (configuration : TwoStacks.Configuration (Fin a) (Fin q)) :
    ((Program.advance (compile machine))^[rounds]) (realize configuration) =
      realize (((tick machine)^[rounds]) configuration) := by
  unfold realize
  rw [Program.advance_iterate_init, iterate_code]

/-- The source run's encoded endpoint is reached by actual covering transport. -/
theorem run_transport (machine : TM0.Machine (Fin a) (Fin q)) (rounds : ℕ)
    (configuration : TwoStacks.Configuration (Fin a) (Fin q)) (index : Fin 3) :
    Transport.transport Circle.isCoveringMap_exp
      (Program.runPath (compile machine) rounds (realize configuration) index)
      (Program.coordinate (realize configuration) index) =
      Program.coordinate (realize (((tick machine)^[rounds]) configuration)) index := by
  rw [Program.run_transport, advance_iterate_realize]

end Monodromy.CoverCompiler
