module

public import Monodromy.Continuation
public import Monodromy.Tape
public import Mathlib.Computability.Primrec.List
public import Monodromy.IntegerPrimrec
public import Mathlib.Computability.PartrecCode
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-!
# The effective content of cover execution

Fixed words of the five native loops have primitive recursive integer
interpretations. Complete native word execution
agrees with this proof interpretation, including results and divergence.
The trajectory-generating core uses the actual covering lifts throughout.
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

noncomputable section

namespace Monodromy.CoupledContinuation

theorem Gate.primrec_evalInt (gate : Gate) (backward : Bool) : Primrec (Gate.evalInt gate backward) := by
  let displacement : ℤ := if backward then -1 else 1
  have first_coordinate : Primrec (fun labels : Labels => labels.1.1) := Primrec.fst.comp Primrec.fst
  have second_coordinate : Primrec (fun labels : Labels => labels.1.2) := Primrec.snd.comp Primrec.fst
  have control : Primrec (fun labels : Labels => labels.2) := Primrec.snd
  have left_test : PrimrecPred (fun labels : Labels => labels.1.1 = 0) :=
    Primrec.eq.comp first_coordinate (Primrec.const 0)
  have right_test : PrimrecPred (fun labels : Labels => labels.1.2 = 0) :=
    Primrec.eq.comp second_coordinate (Primrec.const 0)
  cases gate with
  | left =>
      exact ((IntegerPrimrec.add.comp first_coordinate (Primrec.const displacement)).pair second_coordinate).pair control
  | right =>
      exact (first_coordinate.pair (IntegerPrimrec.add.comp second_coordinate (Primrec.const displacement))).pair control
  | zeroLeft =>
      exact Primrec.fst.pair (IntegerPrimrec.add.comp control
        (Primrec.ite left_test (Primrec.const displacement) (Primrec.const 0)))
  | zeroRight =>
      exact Primrec.fst.pair (IntegerPrimrec.add.comp control
        (Primrec.ite right_test (Primrec.const displacement) (Primrec.const 0)))
  | control =>
      exact Primrec.fst.pair (IntegerPrimrec.add.comp control (Primrec.const displacement))

theorem Word.primrec_evalInt (word : Word) : Primrec (Word.evalInt word) := by
  induction word with
  | nil => exact Primrec.id
  | cons atom rest recursive =>
      rcases atom with ⟨gate, backward⟩
      exact recursive.comp (Gate.primrec_evalInt gate backward)

namespace Program

variable {degree : ℕ} [NeZero degree]

theorem primrec_indexInt : Primrec (indexInt degree) := by
  apply Primrec.fin_val_iff.mp
  have degree_eq : degree - 1 + 1 = degree := by
    have positive := Nat.pos_of_ne_zero (NeZero.ne degree)
    omega
  exact ((IntegerPrimrec.remainder (degree - 1)).comp
    (Primrec.snd : Primrec (Prod.snd : Labels → ℤ))).of_eq
      (by intro labels; simp [degree_eq, indexInt])

theorem primrec_nextInt (program : Program degree) : Primrec program.nextInt :=
  (Primrec.fin_curry₁.mpr (fun index => Word.primrec_evalInt (program.table index))).comp
    primrec_indexInt Primrec.id

theorem primrec_haltInt (program : Program degree) : Primrec program.haltInt :=
  (Primrec.dom_finite program.stop).comp primrec_indexInt

theorem primrec_stepInt (program : Program degree) : Primrec program.stepInt := by
  have primitive := Primrec.cond (primrec_haltInt program) (Primrec.const none)
    (Primrec.option_some.comp (primrec_nextInt program))
  exact primitive.of_eq fun labels => by
    cases done : program.haltInt labels <;> simp [stepInt, done]

/-- Complete execution of a finite geometric word table is partial recursive. -/
theorem partrec_evalInt (program : Program degree) : Partrec program.evalInt :=
  Effectiveness.partrec_eval (primrec_stepInt program).to_comp

/-- Fixed effective interfaces preserve the ordinary partial-recursive upper bound. -/
theorem partrec_with_io (program : Program degree) {input : ℕ → Labels} {output : Labels → ℕ}
    (input_primitive : Primrec input) (output_primitive : Primrec output) :
    Partrec (fun value => (program.evalInt (input value)).map output) :=
  ((program.partrec_evalInt).comp input_primitive.to_comp).map
    (output_primitive.to_comp.comp Computable.snd).to₂

end Program

end Monodromy.CoupledContinuation

namespace Monodromy.PrimeReadout

/-- A bounded search reads a prime exponent without an unbounded factorization oracle. -/
def exponent (prime input : ℕ) : ℕ := input.findGreatest (fun power => prime ^ power ∣ input)

theorem primrec_power (base : ℕ) : Primrec (fun power : ℕ => base ^ power) :=
  (Primrec₂.unpaired'.mp Nat.Primrec.pow).comp (Primrec.const base) Primrec.id

theorem primrec_exponent (prime : ℕ) : Primrec (exponent prime) := by
  have divides : PrimrecRel (fun input power : ℕ => prime ^ power ∣ input) := by
    have remainder : Primrec (fun pair : ℕ × ℕ => pair.1 % prime ^ pair.2) :=
      Primrec.nat_mod.comp Primrec.fst ((primrec_power prime).comp Primrec.snd)
    exact (Primrec.eq.comp remainder (Primrec.const 0)).primrecRel.of_eq
      (fun _ _ => Nat.dvd_iff_mod_eq_zero.symm)
  exact Primrec.nat_findGreatest Primrec.id divides

/-- For a prime, the bounded readout agrees with the exact factorization exponent. -/
theorem exponent_eq_factorization {prime : ℕ} (is_prime : prime.Prime) (input : ℕ) :
    exponent prime input = input.factorization prime := by
  by_cases zero : input = 0
  · subst input
    simp [exponent]
  · apply Nat.findGreatest_eq_iff.mpr
    refine ⟨(Nat.factorization_lt prime zero).le, ?_, ?_⟩
    · intro _
      exact (is_prime.pow_dvd_iff_le_factorization zero).mpr le_rfl
    · intro power larger _ divides
      exact (not_lt_of_ge ((is_prime.pow_dvd_iff_le_factorization zero).mp divides)) larger

end Monodromy.PrimeReadout

namespace Monodromy.TapeCode.Readout

/-- The same fixed positional code is effective on finite words. -/
def wordCode (a : ℕ) (word : List (Fin a)) : ℕ :=
  Nat.ofDigits (a + 1) (word.map Fin.val)

theorem wordCode_foldr (a : ℕ) (word : List (Fin a)) :
    wordCode a word = word.foldr (fun letter total => letter.val + (a + 1) * total) 0 := by
  induction word with
  | nil => rfl
  | cons letter rest recursive => simpa [wordCode, Nat.ofDigits_cons] using congrArg (fun total => letter.val + (a + 1) * total) recursive

theorem primrec_wordCode (a : ℕ) : Primrec (wordCode a) := by
  have folded : Primrec (fun word : List (Fin a) =>
      word.foldr (fun letter total => letter.val + (a + 1) * total) 0) :=
    Primrec.list_foldr Primrec.id (Primrec.const 0)
      (Primrec.nat_add.comp
        (Primrec.fin_val.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.nat_mul.comp (Primrec.const (a + 1)) (Primrec.snd.comp Primrec.snd))).to₂
  exact folded.of_eq (fun word => (wordCode_foldr a word).symm)

section Decoder

variable {a : ℕ} [NeZero a]

/-- The unused last residue is interpreted as blank by a fixed finite table. -/
def extend (read : Fin a → ℕ → ℕ) (letter : Fin (a + 1)) : ℕ → ℕ :=
  Fin.lastCases (read 0) read letter

def digit (a : ℕ) (value : ℕ) : Fin (a + 1) :=
  ⟨value % (a + 1), Nat.mod_lt _ (Nat.succ_pos a)⟩

def step (read : Fin a → ℕ → ℕ) (state : ℕ × ℕ) : ℕ × ℕ :=
  (state.1 / (a + 1), extend read (digit a state.1) state.2)

def run (read : Fin a → ℕ → ℕ) (fuel : ℕ) (state : ℕ × ℕ) : ℕ × ℕ :=
  (step read)^[fuel] state

/-- A bounded numeric readout, independent of the program producing the code. -/
def decode (read : Fin a → ℕ → ℕ) (value : ℕ) : ℕ :=
  (run read value (value, 0)).2

theorem primrec_digit (a : ℕ) : Primrec (digit a) :=
  Primrec.fin_val_iff.mp (Primrec.nat_mod.comp Primrec.id (Primrec.const (a + 1)))

theorem primrec_extend (read : Fin a → ℕ → ℕ) (effective : ∀ letter, Primrec (read letter)) :
    Primrec₂ (extend read) := by
  apply Primrec.fin_curry₁.mpr
  intro letter
  refine Fin.lastCases ?_ (fun original => ?_) letter
  · simpa [extend] using effective 0
  · simpa [extend] using effective original

theorem primrec_step (read : Fin a → ℕ → ℕ) (effective : ∀ letter, Primrec (read letter)) :
    Primrec (step read) :=
  (Primrec.nat_div.comp Primrec.fst (Primrec.const (a + 1))).pair
    ((primrec_extend read effective).comp ((primrec_digit a).comp Primrec.fst) Primrec.snd)

theorem primrec_run (read : Fin a → ℕ → ℕ) (effective : ∀ letter, Primrec (read letter)) :
    Primrec₂ (run read) :=
  (Primrec.nat_iterate Primrec.fst Primrec.snd
    ((primrec_step read effective).comp Primrec.snd).to₂).to₂

theorem primrec_decode (read : Fin a → ℕ → ℕ) (effective : ∀ letter, Primrec (read letter)) :
    Primrec (decode read) :=
  Primrec.snd.comp ((primrec_run read effective).comp Primrec.id (Primrec.id.pair (Primrec.const 0)))

variable (read : Fin a → ℕ → ℕ) (neutral : ∀ initial, read 0 initial = initial)

private theorem fold_blanks (neutral : ∀ initial, read 0 initial = initial) (count initial : ℕ) :
    (List.replicate count (0 : Fin a)).foldl (fun total letter => read letter total) initial = initial := by
  induction count generalizing initial with
  | zero => rfl
  | succ count recursive => simpa only [List.replicate_succ, List.foldl_cons, neutral] using recursive initial

/-- Neutral blank padding makes the human-readable fold a function of the complete half-tape. -/
def tapeFold (neutral : ∀ initial, read 0 initial = initial) (tape : Turing.ListBlank (Fin a)) (initial : ℕ) : ℕ :=
  tape.liftOn (fun word => word.foldl (fun total letter => read letter total) initial) (by
    rintro first _ ⟨count, rfl⟩
    simp [List.foldl_append, Fin.default_eq_zero, fold_blanks read neutral])

@[simp] theorem tapeFold_mk (word : List (Fin a)) (initial : ℕ) :
    tapeFold read neutral (Turing.ListBlank.mk word) initial =
      word.foldl (fun total letter => read letter total) initial := rfl

@[simp] theorem tapeFold_empty (initial : ℕ) :
    tapeFold read neutral (∅ : Turing.ListBlank (Fin a)) initial = initial := rfl

theorem tapeFold_cons (letter : Fin a) (tape : Turing.ListBlank (Fin a)) (initial : ℕ) :
    tapeFold read neutral (tape.cons letter) initial =
      tapeFold read neutral tape (read letter initial) := by
  refine Turing.ListBlank.induction_on tape (fun word => ?_)
  rw [Turing.ListBlank.cons_mk]
  rfl

theorem tapeFold_head_tail (tape : Turing.ListBlank (Fin a)) (initial : ℕ) :
    tapeFold read neutral tape initial = tapeFold read neutral tape.tail (read tape.head initial) := by
  simpa only [Turing.ListBlank.cons_head_tail] using tapeFold_cons read neutral tape.head tape.tail initial

theorem digit_encode (tape : Turing.ListBlank (Fin a)) :
    digit a (TapeCode.encode tape) = tape.head.castSucc := by
  apply Fin.ext
  exact TapeCode.head_code tape

theorem step_encode (tape : Turing.ListBlank (Fin a)) (initial : ℕ) :
    step read (TapeCode.encode tape, initial) = (TapeCode.encode tape.tail, read tape.head initial) := by
  simp [step, TapeCode.tail_code, digit_encode, extend]

theorem step_zero (neutral : ∀ initial, read 0 initial = initial) (initial : ℕ) : step read (0, initial) = (0, initial) := by
  have blank_digit : digit a 0 = (0 : Fin a).castSucc := by apply Fin.ext; rfl
  change (0 / (a + 1), extend read (digit a 0) initial) = (0, initial)
  rw [blank_digit]
  simp only [extend, Fin.lastCases_castSucc, neutral, Nat.zero_div]

theorem run_zero (neutral : ∀ initial, read 0 initial = initial) (fuel initial : ℕ) : run read fuel (0, initial) = (0, initial) :=
  Function.iterate_fixed (step_zero read neutral initial) fuel

theorem run_succ (fuel : ℕ) (state : ℕ × ℕ) :
    run read (fuel + 1) state = run read fuel (step read state) :=
  Function.iterate_succ_apply _ _ _

/-- The numeric code itself is a sufficient uniform bound on the number of useful reads. -/
private theorem run_code (neutral : ∀ initial, read 0 initial = initial) (code : ℕ) :
    ∀ tape : Turing.ListBlank (Fin a), TapeCode.encode tape = code →
      ∀ fuel : ℕ, code ≤ fuel → ∀ initial : ℕ,
        run read fuel (code, initial) = (0, tapeFold read neutral tape initial) := by
  induction code using Nat.strong_induction_on with
  | h code recursive =>
      intro tape encoding fuel enough initial
      by_cases zero : code = 0
      · have blank : tape = ∅ := (TapeCode.encode_eq_zero_iff tape).mp (encoding.trans zero)
        rw [zero, blank, tapeFold_empty]
        exact run_zero read neutral fuel initial
      · have positive : 0 < code := Nat.pos_of_ne_zero zero
        have base_large : 1 < a + 1 := by
          have nonempty := Nat.pos_of_ne_zero (NeZero.ne a)
          omega
        have smaller : TapeCode.encode tape.tail < code := by
          rw [← TapeCode.tail_code tape, encoding]
          exact Nat.div_lt_self positive base_large
        cases fuel with
        | zero => omega
        | succ fuel =>
            have actual_step : step read (code, initial) =
                (TapeCode.encode tape.tail, read tape.head initial) := by
              rw [← encoding]
              exact step_encode read tape initial
            rw [run_succ, actual_step]
            have rest := recursive (TapeCode.encode tape.tail) smaller tape.tail rfl fuel
              (by omega) (read tape.head initial)
            exact rest.trans (congrArg (fun value => (0, value))
              (tapeFold_head_tail read neutral tape initial).symm)

/-- The code is fully consumed and its fold is exact after any sufficient bounded iteration. -/
theorem run_tape_state (tape : Turing.ListBlank (Fin a)) (fuel : ℕ)
    (enough : TapeCode.encode tape ≤ fuel) (initial : ℕ) :
    run read fuel (TapeCode.encode tape, initial) = (0, tapeFold read neutral tape initial) :=
  run_code read neutral (TapeCode.encode tape) tape rfl fuel enough initial

/-- Every representative, including arbitrary blank padding, has the same bounded numeric readout. -/
theorem run_tape (tape : Turing.ListBlank (Fin a)) (fuel : ℕ)
    (enough : TapeCode.encode tape ≤ fuel) (initial : ℕ) :
    (run read fuel (TapeCode.encode tape, initial)).2 = tapeFold read neutral tape initial :=
  congrArg Prod.snd (run_tape_state read neutral tape fuel enough initial)

/-- The fixed total primitive-recursive decoder agrees with the blank-invariant tape fold. -/
theorem decode_tape (tape : Turing.ListBlank (Fin a)) :
    decode read (TapeCode.encode tape) = tapeFold read neutral tape 0 :=
  run_tape read neutral tape (TapeCode.encode tape) le_rfl 0

/-- In particular the same readout acts on every finite word, without choosing a representative. -/
theorem decode_word (neutral : ∀ initial, read 0 initial = initial) (word : List (Fin a)) :
    decode read (wordCode a word) = word.foldl (fun total letter => read letter total) 0 :=
  decode_tape read neutral (Turing.ListBlank.mk word)

end Decoder

end Monodromy.TapeCode.Readout

/-!
## Direct analytic comparison

The same finite word table has a globally real analytic successor on three
real coordinates. Its complete execution on the exact integer lattice agrees
with native transport. The comparison evaluates formulas directly and carries
no assertion about off-lattice conjugacy, physical robustness, or equal cost.
-/

/-- The removable value at zero preserves real analyticity. -/
theorem Real.analyticAt_sinc (x : ℝ) : AnalyticAt ℝ Real.sinc x := by
  rw [Real.sinc_eq_dslope]
  by_cases same : x = 0
  · subst x
    obtain ⟨series, analytic⟩ := (Real.analyticAt_sin : AnalyticAt ℝ Real.sin 0)
    exact ⟨series.fslope, analytic.has_fpower_series_dslope_fslope⟩
  · have analytic : AnalyticAt ℝ (fun y : ℝ => (Real.sin y - Real.sin 0) / (y - 0)) x :=
      (Real.analyticAt_sin.sub analyticAt_const).div
        (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr same)
    apply analytic.congr
    filter_upwards [isOpen_ne.mem_nhds same] with y other
    simp only [dslope_of_ne Real.sin other, slope_def_field]

namespace Monodromy.AnalyticComparison

/-- An analytic exact zero indicator on the integer lattice. -/
def zero (x : ℝ) : ℝ := Real.sinc (Real.pi * x)

theorem analyticAt_zero (x : ℝ) : AnalyticAt ℝ zero x :=
  (Real.analyticAt_sinc _).comp (analyticAt_const.mul analyticAt_id)

theorem zero_int (n : ℤ) : zero (n : ℝ) = if n = 0 then 1 else 0 := by
  by_cases same : n = 0
  · subst n
    simp [zero]
  · have nonzero : Real.pi * (n : ℝ) ≠ 0 :=
      mul_ne_zero Real.pi_ne_zero (by exact_mod_cast same)
    rw [zero, Real.sinc_of_ne_zero nonzero, mul_comm Real.pi (n : ℝ),
      Real.sin_int_mul_pi, zero_div, ite_eq_right same]

/-- A real analytic cardinal selector for the finite control residue. -/
def weight (degree : ℕ) [NeZero degree] (marked : Fin degree) (x : ℝ) : ℝ :=
  (Choice.kernel (fun z : ℂ => z ^ degree) (Radix.omega degree marked : ℂ)
    (Radix.readRoot degree ((2 * Real.pi) * x) : ℂ)).re

theorem analyticAt_weight (degree : ℕ) [NeZero degree] (marked : Fin degree) (x : ℝ) :
    AnalyticAt ℝ (weight degree marked) x := by
  have root : AnalyticAt ℂ (fun z : ℂ =>
      Complex.exp (((2 * Real.pi : ℝ) : ℂ) * z / (degree : ℂ) * Complex.I)) (x : ℂ) :=
    analyticAt_cexp.comp
      (((analyticAt_const.mul analyticAt_id).div_const).mul analyticAt_const)
  have analytic : AnalyticAt ℂ (fun z : ℂ =>
      Choice.kernel (fun w : ℂ => w ^ degree) (Radix.omega degree marked : ℂ)
        (Complex.exp (((2 * Real.pi : ℝ) : ℂ) * z / (degree : ℂ) * Complex.I))) (x : ℂ) :=
    (Choice.analyticAt_kernel (fun _ => analyticAt_id.pow degree)
      (Radix.omega degree marked : ℂ) _).comp root
  change AnalyticAt ℝ (fun y : ℝ =>
    (Choice.kernel (fun z : ℂ => z ^ degree) (Radix.omega degree marked : ℂ)
      (Radix.readRoot degree ((2 * Real.pi) * y) : ℂ)).re) x
  simpa only [Radix.readRoot, Circle.coe_exp, Complex.ofReal_div,
    Complex.ofReal_mul, Complex.ofReal_natCast] using analytic.re_ofReal

theorem weight_int_digit (degree : ℕ) [NeZero degree]
    (quotient : ℤ) (marked digit : Fin degree) :
    weight degree marked (((degree : ℤ) * quotient + digit.val : ℤ) : ℝ) =
      if marked = digit then 1 else 0 := by
  unfold weight
  rw [Radix.readRoot_digit, Radix.kernel_root]
  split_ifs <;> simp

theorem weight_digit (degree : ℕ) [NeZero degree] (marked : Fin degree)
    (quotient : ℤ) (digit : Fin degree) :
    weight degree marked ((degree : ℝ) * (quotient : ℝ) + (digit.val : ℝ)) =
      if marked = digit then 1 else 0 := by
  simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast] using
    weight_int_digit degree quotient marked digit

theorem weight_int (degree : ℕ) [NeZero degree] (marked : Fin degree) (n : ℤ) :
    weight degree marked (n : ℝ) =
      if n % (degree : ℤ) = (marked.val : ℤ) then 1 else 0 := by
  have positive : 0 < (degree : ℤ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne degree)
  let digit : Fin degree := ⟨(n % (degree : ℤ)).toNat, by
    have lower := Int.emod_nonneg n positive.ne'
    have upper := Int.emod_lt_of_pos n positive
    omega⟩
  have digit_value : (digit.val : ℤ) = n % (degree : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg n positive.ne')
  have decomposition : (degree : ℤ) * (n / (degree : ℤ)) + digit.val = n := by
    rw [digit_value]
    exact Int.mul_ediv_add_emod n (degree : ℤ)
  have observed := weight_int_digit degree (n / (degree : ℤ)) marked digit
  rw [decomposition] at observed
  have same : marked = digit ↔ n % (degree : ℤ) = (marked.val : ℤ) := by
    constructor
    · rintro rfl
      exact digit_value.symm
    · intro equality
      apply Fin.ext
      exact_mod_cast equality.symm.trans digit_value.symm
  simpa only [same] using observed

end Monodromy.AnalyticComparison

namespace Monodromy.AnalyticComparison

open CoupledContinuation

abbrev State := (ℝ × ℝ) × ℝ

def embed (labels : Labels) : State :=
  (((labels.1.1 : ℝ), (labels.1.2 : ℝ)), (labels.2 : ℝ))

theorem embed_injective : Function.Injective embed := by
  rintro ⟨⟨x, y⟩, z⟩ ⟨⟨x', y'⟩, z'⟩ same
  have hx : (x : ℝ) = x' := congrArg (fun s : State => s.1.1) same
  have hy : (y : ℝ) = y' := congrArg (fun s : State => s.1.2) same
  have hz : (z : ℝ) = z' := congrArg (fun s : State => s.2) same
  have : x = x' := by exact_mod_cast hx
  have : y = y' := by exact_mod_cast hy
  have : z = z' := by exact_mod_cast hz
  aesop

/-- These analytic shears evaluate formulas directly, with no path-lifting operation. -/
def gate (operation : Gate) (backward : Bool) (state : State) : State :=
  let displacement : ℝ := if backward then -1 else 1
  match operation with
  | .left => ((state.1.1 + displacement, state.1.2), state.2)
  | .right => ((state.1.1, state.1.2 + displacement), state.2)
  | .zeroLeft => (state.1, state.2 + displacement * zero state.1.1)
  | .zeroRight => (state.1, state.2 + displacement * zero state.1.2)
  | .control => (state.1, state.2 + displacement)

theorem analyticAt_gate (operation : Gate) (backward : Bool) (state : State) :
    AnalyticAt ℝ (gate operation backward) state := by
  have first : AnalyticAt ℝ (fun s : State => s.1.1) state :=
    analyticAt_fst.comp analyticAt_fst
  have second : AnalyticAt ℝ (fun s : State => s.1.2) state :=
    analyticAt_snd.comp analyticAt_fst
  have control : AnalyticAt ℝ (fun s : State => s.2) state := analyticAt_snd
  cases operation with
  | left => exact ((first.add analyticAt_const).prod second).prod control
  | right => exact (first.prod (second.add analyticAt_const)).prod control
  | zeroLeft =>
      exact analyticAt_fst.prod (control.add
        (analyticAt_const.mul ((analyticAt_zero _).comp first)))
  | zeroRight =>
      exact analyticAt_fst.prod (control.add
        (analyticAt_const.mul ((analyticAt_zero _).comp second)))
  | control => exact analyticAt_fst.prod (control.add analyticAt_const)

theorem gate_embed (operation : Gate) (backward : Bool) (labels : Labels) :
    gate operation backward (embed labels) = embed (operation.evalInt backward labels) := by
  rcases labels with ⟨⟨left, right⟩, control⟩
  cases operation <;> cases backward <;>
    simp [gate, Gate.evalInt, embed, zero_int]

def word : Word → State → State
  | [], state => state
  | (operation, backward) :: rest, state => word rest (gate operation backward state)

theorem gate_reverse (operation : Gate) (backward : Bool) (state : State) :
    gate operation (!backward) (gate operation backward state) = state := by
  rcases state with ⟨⟨left, right⟩, control⟩
  cases operation <;> cases backward <;> simp [gate]

theorem word_append (first second : Word) (state : State) :
    word (first ++ second) state = word second (word first state) := by
  induction first generalizing state with
  | nil => rfl
  | cons atom rest recursive => simpa only [List.cons_append, word] using recursive _

/-- The same formal reverse word inverts every analytic primitive on the whole real space. -/
theorem word_inverse (operations : Word) (state : State) :
    word operations.inverse (word operations state) = state := by
  induction operations generalizing state with
  | nil => rfl
  | cons atom rest recursive =>
      rcases atom with ⟨operation, backward⟩
      rw [Word.inverse, word_append, word, recursive]
      simpa only [Word.atom, word] using gate_reverse operation backward state

theorem analyticAt_word (operations : Word) (state : State) :
    AnalyticAt ℝ (word operations) state := by
  induction operations generalizing state with
  | nil => exact analyticAt_id
  | cons atom rest recursive =>
      exact (recursive _).comp (analyticAt_gate atom.1 atom.2 state)

theorem word_embed (operations : Word) (labels : Labels) :
    word operations (embed labels) = embed (operations.evalInt labels) := by
  induction operations generalizing labels with
  | nil => rfl
  | cons atom rest recursive =>
      simp only [word, Word.evalInt, gate_embed, recursive]

variable {degree : ℕ} [NeZero degree]

/-- A finite analytic successor over three real coordinates. -/
def next (program : Program degree) (state : State) : State :=
  ∑ index, weight degree index state.2 • word (program.table index) state

def halt (program : Program degree) (state : State) : ℝ :=
  ∑ index, weight degree index state.2 * if program.stop index then 1 else 0

theorem analyticAt_next (program : Program degree) (state : State) :
    AnalyticAt ℝ (next program) state := by
  exact Finset.analyticAt_fun_sum Finset.univ (fun index _ =>
    (((analyticAt_weight degree index _).comp analyticAt_snd).smul
      (analyticAt_word (program.table index) state)))

theorem analyticAt_halt (program : Program degree) (state : State) :
    AnalyticAt ℝ (halt program) state := by
  exact Finset.analyticAt_fun_sum Finset.univ (fun index _ =>
    (((analyticAt_weight degree index _).comp analyticAt_snd).mul analyticAt_const))

theorem weight_label (marked : Fin degree) (labels : Labels) :
    weight degree marked (labels.2 : ℝ) =
      if marked = Program.indexInt degree labels then 1 else 0 := by
  have result := weight_int_digit degree (labels.2 / (degree : ℤ)) marked
    (Program.indexInt degree labels)
  rw [Program.control_decomposition] at result
  exact result

theorem next_embed (program : Program degree) (labels : Labels) :
    next program (embed labels) = embed (program.nextInt labels) := by
  classical
  simp only [next, embed, weight_label]
  rw [Finset.sum_eq_single (Program.indexInt degree labels)]
  · simp only [ite_true, one_smul]
    exact word_embed _ labels
  · intro index _ different
    simp [different]
  · simp

theorem halt_embed (program : Program degree) (labels : Labels) :
    halt program (embed labels) = if program.haltInt labels then 1 else 0 := by
  classical
  simp only [halt, embed, weight_label]
  rw [Finset.sum_eq_single (Program.indexInt degree labels)]
  · simp [Program.haltInt]
    rfl
  · intro index _ different
    simp [different]
  · simp

def step (program : Program degree) (state : State) : Option State :=
  if halt program state = 1 then none else some (next program state)

def eval (program : Program degree) : State → Part State :=
  StateTransition.eval (step program)

theorem step_embed (program : Program degree) (labels : Labels) :
    step program (embed labels) = (program.stepInt labels).map embed := by
  unfold step Program.stepInt
  rw [halt_embed]
  cases program.haltInt labels <;> simp [next_embed]

/-- Direct analytic execution agrees on complete results and divergence, not only on one step. -/
theorem eval_embed (program : Program degree) (labels : Labels) :
    eval program (embed labels) = embed <$> program.evalInt labels := by
  have refinement : StateTransition.Respects program.stepInt (step program)
      (fun first second => embed first = second) := by
    apply StateTransition.fun_respects.mpr
    intro source
    cases result : program.stepInt source with
    | none =>
        change step program (embed source) = none
        simp [step_embed, result]
    | some successor =>
        apply Relation.TransGen.single
        simp [step_embed, result]
  exact StateTransition.tr_eval' program.stepInt (step program) embed refinement labels

theorem result_iff (program : Program degree) (initial final : Labels) :
    embed final ∈ eval program (embed initial) ↔
      Labels.prepare final ∈ program.eval (Labels.prepare initial) := by
  rw [eval_embed, Program.eval_prepareInt]
  simp only [Part.map_eq_map, Part.mem_map_iff]
  constructor
  · rintro ⟨found, reaches, same⟩
    exact ⟨found, reaches, congrArg Labels.prepare (embed_injective same)⟩
  · rintro ⟨found, reaches, same⟩
    have injective : Function.Injective Labels.prepare := by
      rintro ⟨⟨x, y⟩, z⟩ ⟨⟨x', y'⟩, z'⟩ same
      simpa [Labels.prepare] using prepare_injective same
    exact ⟨found, reaches, congrArg embed (injective same)⟩

theorem halting_iff (program : Program degree) (labels : Labels) :
    (eval program (embed labels)).Dom ↔ (program.eval (Labels.prepare labels)).Dom := by
  rw [eval_embed, Program.eval_prepareInt]
  rfl

/-- Undefined complete execution is preserved under the same exact initialization. -/
theorem divergence_iff (program : Program degree) (labels : Labels) :
    ¬ (eval program (embed labels)).Dom ↔ ¬ (program.eval (Labels.prepare labels)).Dom :=
  not_congr (halting_iff program labels)

end Monodromy.AnalyticComparison
