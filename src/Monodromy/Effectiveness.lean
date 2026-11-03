module

public import Monodromy.CoverPrograms
public import Monodromy.IntegerPrimrec
public import Mathlib.Computability.PartrecCode

/-!
# The effective content of cover execution

Each fixed finite expression has primitive recursive integer semantics.
Iterating its finite transition table gives an ordinary partial recursive
function on integer configurations.
-/

@[expose] public section

namespace Monodromy.Effectiveness

/-- A computable transition system has a partial recursive complete execution. -/
theorem partrec_eval {S : Type*} [Primcodable S] {transition : S → Option S}
    (effective : Computable transition) : Partrec (StateTransition.eval transition) := by
  let body : S → S ⊕ S := fun state => (transition state).elim (Sum.inl state) Sum.inr
  have body_computable : Computable body :=
    (Computable.option_casesOn effective Computable.sumInl
      (Computable.sumInr.comp Computable.snd).to₂).of_eq fun state => by
        cases result : transition state <;> simp [body, result]
  exact Partrec.fix body_computable.partrec

end Monodromy.Effectiveness

namespace Monodromy.CoverExpressions

variable {n : ℕ}

/-- Use the encoding attached to the primitive-recursive finite-vector presentation. -/
def Program.stateCode (state : Program.IntState n) : ℕ :=
  @Encodable.encode _ (inferInstance : Primcodable (Program.IntState n)).toEncodable state

theorem Program.stateCode_injective : Function.Injective (@Program.stateCode n) := by
  intro first second same
  exact @Encodable.encode_injective _ (inferInstance : Primcodable (Program.IntState n)).toEncodable
    first second same

theorem primrec_digit (B : ℕ) : Primrec (digit B) := by
  apply Primrec.fin_val_iff.mp
  exact IntegerPrimrec.remainder B

/-- A fixed finite expression has primitive recursive integer semantics. -/
theorem primrec_evalInt (term : Term n) : Primrec (evalInt term) := by
  induction term with
  | coord index => exact Primrec.fin_app.comp Primrec.id (Primrec.const index)
  | integerConst value => exact Primrec.const value
  | add first second first_primitive second_primitive =>
      exact IntegerPrimrec.add.comp first_primitive second_primitive
  | integerScale value term primitive => exact (IntegerPrimrec.scale value).comp primitive
  | select B key branches key_primitive branches_primitive =>
      exact (Primrec.fin_curry₁.mpr branches_primitive).comp
        ((primrec_digit B).comp key_primitive) Primrec.id
  | descend B key primitive => exact (IntegerPrimrec.quotient B).comp primitive

/-- The internal finite-root stopping decision is primitive recursive. -/
theorem Guard.primrec_evalInt (guard : Guard n) : Primrec (Guard.evalInt guard) := by
  induction guard with
  | constant value => exact Primrec.const value
  | select B key branches branches_primitive =>
      exact (Primrec.fin_curry₁.mpr branches_primitive).comp
        ((primrec_digit B).comp
          (CoverExpressions.primrec_evalInt key)) Primrec.id

/-- A native return's exact lattice interpretation is primitive recursive. -/
theorem Program.primrec_nextInt (program : Program n) : Primrec (Program.nextInt program) := by
  apply Primrec.fin_curry.mpr
  exact (Primrec.fin_curry₁.mpr (fun index =>
    primrec_evalInt (program.returning index))).swap

/-- The complete guarded transition table is primitive recursive. -/
theorem Program.primrec_stepInt (program : Program n) : Primrec (Program.stepInt program) := by
  have primitive := Primrec.cond
    (Guard.primrec_evalInt program.stop)
    (Primrec.const none)
    (Primrec.option_some.comp
      (Program.primrec_nextInt program))
  exact primitive.of_eq fun state => by
    cases done : Guard.evalInt program.stop state <;> simp [Program.stepInt, done]

/-- Complete execution belongs to the usual class of partial recursive functions. -/
theorem Program.partrec_evalInt (program : Program n) : Partrec (Program.evalInt program) :=
  Effectiveness.partrec_eval
    (Program.primrec_stepInt program).to_comp

/-- An ordinary recursive code realizes every encoded complete program result. -/
theorem Program.exists_code (program : Program n) :
    ∃ code : Nat.Partrec.Code, ∀ state : Program.IntState n,
      code.eval (Program.stateCode state) = (Program.evalInt program state).map Program.stateCode := by
  obtain ⟨code, realizes⟩ := Nat.Partrec.Code.exists_code.mp
    (Program.partrec_evalInt program)
  refine ⟨code, fun state => ?_⟩
  have execution := congrFun realizes (Program.stateCode state)
  dsimp only [Program.stateCode] at execution ⊢
  simp only [Encodable.encodek, Part.coe_some, Part.bind_some] at execution
  have encoder :
      (@Encodable.encode (Program.IntState n)
        (inferInstance : Primcodable (Program.IntState n)).toEncodable) = Program.stateCode :=
    funext fun _ => rfl
  rw [encoder] at execution
  exact execution

end Monodromy.CoverExpressions
