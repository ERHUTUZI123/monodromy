module

public import Monodromy.Choice
public import Mathlib.Data.Fin.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

namespace Monodromy.Radix

variable (B : ℕ) [NeZero B]

noncomputable def omega (digit : Fin B) : Circle :=
  Circle.exp (2 * Real.pi * (digit.val : ℝ) / (B : ℝ))

theorem primitive : IsPrimitiveRoot (Circle.exp (2 * Real.pi / (B : ℝ))) B := by
  have complex : IsPrimitiveRoot ((Circle.exp (2 * Real.pi / (B : ℝ)) : Circle) : ℂ) B := by
    convert Complex.isPrimitiveRoot_exp B (NeZero.ne B) using 1
    simp only [Circle.coe_exp]
    congr 1
    push_cast
    ring
  exact complex.of_map_of_injective (f := Circle.coeHom) Subtype.val_injective

omit [NeZero B] in
theorem omega_eq_pow (digit : Fin B) :
    omega B digit = Circle.exp (2 * Real.pi / (B : ℝ)) ^ digit.val := by
  rw [← Circle.exp_natCast_mul]
  unfold omega
  congr 1
  ring

theorem omega_injective : Function.Injective (omega B) := by
  intro first second same
  rw [omega_eq_pow, omega_eq_pow] at same
  exact Fin.ext ((primitive B).pow_inj first.isLt second.isLt same)

theorem omega_pow (digit : Fin B) : omega B digit ^ B = 1 := by
  rw [omega_eq_pow, ← pow_mul, Nat.mul_comm digit.val B, pow_mul,
    (primitive B).pow_eq_one, one_pow]

theorem omega_complex_pow (digit : Fin B) : (omega B digit : ℂ) ^ B = 1 := by
  simpa only [Circle.coe_pow, Circle.coe_one] using
    congrArg (fun point : Circle => (point : ℂ)) (omega_pow B digit)

/-- The logarithmic lift factors the exponential through the finite power cover. -/
noncomputable def readRoot (x : ℝ) : Circle := Circle.exp (x / (B : ℝ))

theorem readRoot_pow (x : ℝ) : readRoot B x ^ B = Circle.exp x := by
  unfold readRoot
  rw [← Circle.exp_natCast_mul]
  congr 1
  field_simp [show (B : ℝ) ≠ 0 by exact_mod_cast NeZero.ne B]

/-- The finite root reads the lowest radix digit, without a modulus in its definition. -/
theorem readRoot_digit (n : ℤ) (digit : Fin B) :
    readRoot B ((2 * Real.pi) * (((B : ℤ) * n + digit.val : ℤ) : ℝ)) = omega B digit := by
  have split :
      (2 * Real.pi) * (((B : ℤ) * n + digit.val : ℤ) : ℝ) / (B : ℝ) =
        (n : ℝ) * (2 * Real.pi) + 2 * Real.pi * (digit.val : ℝ) / (B : ℝ) := by
    push_cast
    field_simp [show (B : ℝ) ≠ 0 by exact_mod_cast NeZero.ne B]
  unfold readRoot
  rw [split, Circle.exp_add, Circle.exp_int_mul_two_pi, one_mul]
  rfl

theorem omega_regular (digit : Fin B) :
    deriv (fun z : ℂ => z ^ B) (omega B digit : ℂ) ≠ 0 := by
  rw [deriv_pow_field]
  exact mul_ne_zero (by exact_mod_cast NeZero.ne B)
    (pow_ne_zero _ (omega B digit).coe_ne_zero)

theorem kernel_root (marked digit : Fin B) :
    Choice.kernel (fun z : ℂ => z ^ B) (omega B marked : ℂ) (omega B digit : ℂ) =
      if marked = digit then 1 else 0 := by
  classical
  by_cases same : marked = digit
  · subst digit
    simpa using Choice.kernel_self (omega_regular B marked)
  · simp only [same, ↓reduceIte]
    apply Choice.kernel_other
    · intro equal
      exact same ((omega_injective B) (Subtype.ext equal)).symm
    · exact (omega_complex_pow B digit).trans (omega_complex_pow B marked).symm

end Monodromy.Radix

namespace Monodromy.Radix.Words


variable {a : ℕ}

/-- Nonzero digits, with the first letter in the least significant position. -/
def encode : List (Fin a) → ℕ
  | [] => 0
  | letter :: tail => (letter.val + 1) + (a + 1) * encode tail

@[simp] theorem encode_nil : encode ([] : List (Fin a)) = 0 := rfl

theorem digit_bounds (letter : Fin a) : 1 ≤ letter.val + 1 ∧ letter.val + 1 ≤ a := by
  have bound := letter.isLt
  omega

@[simp] theorem encode_cons_mod (letter : Fin a) (tail : List (Fin a)) :
    encode (letter :: tail) % (a + 1) = letter.val + 1 := by
  rw [encode, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (Nat.succ_lt_succ letter.isLt)]

@[simp] theorem encode_cons_div (letter : Fin a) (tail : List (Fin a)) :
    encode (letter :: tail) / (a + 1) = encode tail := by
  rw [encode, Nat.add_mul_div_left _ _ (Nat.succ_pos a),
    Nat.div_eq_of_lt (Nat.succ_lt_succ letter.isLt), Nat.zero_add]

@[simp] theorem encode_eq_zero_iff (word : List (Fin a)) :
    encode word = 0 ↔ word = [] := by
  cases word <;> simp [encode]

theorem encode_pos_iff (word : List (Fin a)) :
    0 < encode word ↔ word ≠ [] := by
  rw [Nat.pos_iff_ne_zero, ne_eq, encode_eq_zero_iff]

@[simp] theorem mod_eq_zero_iff (word : List (Fin a)) :
    encode word % (a + 1) = 0 ↔ word = [] := by
  cases word <;> simp

/-- The quotient decodes the tail, including the empty word. -/
theorem encode_tail (word : List (Fin a)) :
    encode word / (a + 1) = encode word.tail := by
  cases word <;> simp

/-- Remainder zero means empty; every other valid remainder names the head. -/
theorem encode_head (word : List (Fin a)) :
    encode word % (a + 1) = (word.head?.map (fun letter => letter.val + 1)).getD 0 := by
  cases word <;> simp

theorem encode_injective : Function.Injective (encode (a := a)) := by
  intro first
  induction first with
  | nil =>
      intro second same
      exact ((encode_eq_zero_iff second).mp same.symm).symm
  | cons letter tail previous =>
      intro second same
      cases second with
      | nil => cases ((encode_eq_zero_iff (letter :: tail)).mp same)
      | cons other rest =>
          have heads := congrArg (fun code => code % (a + 1)) same
          have tails := congrArg (fun code => code / (a + 1)) same
          simp only [encode_cons_mod] at heads
          simp only [encode_cons_div] at tails
          exact congrArg₂ List.cons (Fin.ext (Nat.add_right_cancel heads)) (previous tails)

end Monodromy.Radix.Words

namespace Monodromy.Radix


noncomputable def weight (B : ℕ) [NeZero B] (marked : Fin B) (x : ℝ) : ℝ :=
  (Choice.kernel (fun z : ℂ => z ^ B) (omega B marked : ℂ) (readRoot B x : ℂ)).re

noncomputable def choose (B : ℕ) [NeZero B] (values : Fin B → ℝ) (x : ℝ) : ℝ :=
  ∑ digit, weight B digit x * values digit

variable (B : ℕ) [NeZero B]

theorem weight_digit (n : ℤ) (marked digit : Fin B) :
    weight B marked ((2 * Real.pi) * (((B : ℤ) * n + digit.val : ℤ) : ℝ)) =
      if marked = digit then 1 else 0 := by
  unfold weight
  rw [readRoot_digit, kernel_root]
  split_ifs <;> simp

theorem choose_digit (values : Fin B → ℝ) (n : ℤ) (digit : Fin B) :
    choose B values ((2 * Real.pi) * (((B : ℤ) * n + digit.val : ℤ) : ℝ)) = values digit := by
  classical
  unfold choose
  simp_rw [weight_digit]
  simp

/-- The finite-cover observation is the real restriction of an entire function. -/
theorem analyticAt_weight (marked : Fin B) (x : ℝ) : AnalyticAt ℝ (weight B marked) x := by
  have root : AnalyticAt ℂ
      (fun z : ℂ => Complex.exp (z / (B : ℂ) * Complex.I)) (x : ℂ) :=
    analyticAt_cexp.comp ((analyticAt_id.div_const).mul analyticAt_const)
  have analytic : AnalyticAt ℂ
      (fun z : ℂ => Choice.kernel (fun w : ℂ => w ^ B) (omega B marked : ℂ)
        (Complex.exp (z / (B : ℂ) * Complex.I))) (x : ℂ) :=
    (Choice.analyticAt_kernel (fun _ => analyticAt_id.pow B)
      (omega B marked : ℂ) _).comp root
  change AnalyticAt ℝ (fun y : ℝ =>
    (Choice.kernel (fun z : ℂ => z ^ B) (omega B marked : ℂ) (readRoot B y : ℂ)).re) x
  simpa only [readRoot, Circle.coe_exp, Complex.ofReal_div, Complex.ofReal_natCast] using
    analytic.re_ofReal

theorem analyticAt_choose (values : Fin B → ℝ) (x : ℝ) : AnalyticAt ℝ (choose B values) x := by
  unfold choose
  exact Finset.analyticAt_fun_sum Finset.univ
    (fun digit _ => (analyticAt_weight B digit x).mul analyticAt_const)

end Monodromy.Radix

namespace Monodromy.Radix.Stack


variable {a : ℕ}

noncomputable def wordAngle (word : List (Fin a)) : ℝ :=
  (2 * Real.pi) * (Words.encode word : ℝ)

def headDigit : List (Fin a) → Fin (a + 1)
  | [] => 0
  | letter :: _ => letter.succ

private theorem encode_split (word : List (Fin a)) :
    Words.encode word = (a + 1) * Words.encode word.tail + (headDigit word).val := by
  cases word <;> simp [Words.encode, headDigit, Nat.add_comm]

theorem wordAngle_digit (word : List (Fin a)) :
    wordAngle word = (2 * Real.pi) *
      ((((a + 1 : ℕ) : ℤ) * (Words.encode word.tail : ℤ) + (headDigit word).val : ℤ) : ℝ) := by
  unfold wordAngle
  congr 1
  exact_mod_cast encode_split word

/-- The finite power root reads the head, including the empty digit zero. -/
theorem readRoot_word (word : List (Fin a)) :
    readRoot (a + 1) (wordAngle word) = omega (a + 1) (headDigit word) := by
  rw [wordAngle_digit]
  exact readRoot_digit (a + 1) (Words.encode word.tail : ℤ) (headDigit word)

noncomputable def push (letter : Fin a) (x : ℝ) : ℝ :=
  ((a + 1 : ℕ) : ℝ) * x + (2 * Real.pi) * (letter.val + 1)

theorem push_word (letter : Fin a) (word : List (Fin a)) :
    push letter (wordAngle word) = wordAngle (letter :: word) := by
  simp only [push, wordAngle, Words.encode]
  push_cast
  ring

theorem choose_word (values : Fin (a + 1) → ℝ) (word : List (Fin a)) :
    choose (a + 1) values (wordAngle word) = values (headDigit word) := by
  rw [wordAngle_digit]
  exact choose_digit (a + 1) values (Words.encode word.tail : ℤ) (headDigit word)

/-- Remove the digit supplied by the finite root observation, then rescale. -/
noncomputable def pop (a : ℕ) (x : ℝ) : ℝ :=
  (x - (2 * Real.pi) * choose (a + 1) (fun digit => (digit.val : ℝ)) x) /
    ((a + 1 : ℕ) : ℝ)

theorem pop_word (word : List (Fin a)) : pop a (wordAngle word) = wordAngle word.tail := by
  unfold pop
  rw [choose_word]
  apply (div_eq_iff (show ((a + 1 : ℕ) : ℝ) ≠ 0 by exact_mod_cast Nat.succ_ne_zero a)).mpr
  rw [wordAngle_digit]
  unfold wordAngle
  push_cast
  ring

theorem analyticAt_push (letter : Fin a) (x : ℝ) : AnalyticAt ℝ (push letter) x :=
  (analyticAt_const.mul analyticAt_id).add analyticAt_const

theorem analyticAt_pop (a : ℕ) (x : ℝ) : AnalyticAt ℝ (pop a) x :=
  (analyticAt_id.sub (analyticAt_const.mul
    (analyticAt_choose (a + 1) (fun digit => (digit.val : ℝ)) x))).div_const

end Monodromy.Radix.Stack

namespace Monodromy.Radix.Stack

/-- Popping exposes tail information absent from the present finite root observation. -/
theorem pop_not_projectable {a : ℕ} (letter : Fin a) :
    ¬ ∃ advance : Circle → Circle, ∀ word : List (Fin a),
      readRoot (a + 1) (pop a (wordAngle word)) =
        advance (readRoot (a + 1) (wordAngle word)) := by
  rintro ⟨advance, closed⟩
  have single := closed [letter]
  have double := closed [letter, letter]
  simp only [pop_word, readRoot_word, List.tail_cons, headDigit] at single double
  have impossible : (0 : Fin (a + 1)) = letter.succ :=
    omega_injective (a + 1) (single.trans double.symm)
  exact Fin.succ_ne_zero letter impossible.symm

end Monodromy.Radix.Stack

namespace Monodromy.Radix.Words

variable {a : ℕ}

/-- Concatenation is radix rescaling followed by addition. -/
theorem encode_append (first second : List (Fin a)) :
    encode (first ++ second) = encode first + (a + 1) ^ first.length * encode second := by
  induction first with
  | nil => simp
  | cons letter tail previous =>
      simp only [List.cons_append, encode, List.length_cons, previous, pow_succ]
      ring

/-- Word length requires exponential branch range in this exact radix representation. -/
theorem encode_growth (word : List (Fin a)) :
    (a + 1) ^ word.length ≤ a * encode word + 1 := by
  induction word with
  | nil => simp
  | cons letter tail previous =>
      simp only [List.length_cons, encode, pow_succ]
      nlinarith [Nat.zero_le (a * letter.val)]

end Monodromy.Radix.Words

namespace Monodromy.Radix.Stack

variable {a : ℕ}

/-- A finite prefix acts by the affine map determined by its word code. -/
noncomputable def prepend (word : List (Fin a)) (x : ℝ) : ℝ :=
  ((a + 1 : ℕ) : ℝ) ^ word.length * x + wordAngle word

theorem prepend_word (first second : List (Fin a)) :
    prepend first (wordAngle second) = wordAngle (first ++ second) := by
  simp only [prepend, wordAngle, Words.encode_append]
  push_cast
  ring

/-- Concatenating prefixes composes their affine memory actions. -/
theorem prepend_append (first second : List (Fin a)) (x : ℝ) :
    prepend (first ++ second) x = prepend first (prepend second x) := by
  simp only [prepend, List.length_append, wordAngle, Words.encode_append, pow_add]
  push_cast
  ring

end Monodromy.Radix.Stack
