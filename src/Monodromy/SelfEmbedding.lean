module

public import Mathlib.GroupTheory.Coset.Basic
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Algebra.Group.TypeTags.Hom

/-!
# Words in a group self-embedding

An injective endomorphism stores successive tails. Separated cosets reserve
one tag for the empty word and distinct tags for the letters.
-/

@[expose] public section

namespace Monodromy.SelfEmbedding

variable {G α : Type*} [Group G]

def encode (embedding : G →* G) (digit : α → G) : List α → G
  | [] => 1
  | letter :: tail => digit letter * embedding (encode embedding digit tail)

/-- The identity coset marks empty memory; letter cosets mark nonempty heads. -/
def tag (embedding : G →* G) (digit : α → G) : Option α → G ⧸ embedding.range
  | none => (1 : G)
  | some letter => digit letter

theorem tag_injective (embedding : G →* G) (digit : α → G)
    (outside : ∀ letter, digit letter ∉ embedding.range)
    (separated : Function.Injective (fun letter => (digit letter : G ⧸ embedding.range))) :
    Function.Injective (tag embedding digit) := by
  intro first second same
  cases first with
  | none =>
      cases second with
      | none => rfl
      | some letter =>
          exact (outside letter (by simpa [tag] using QuotientGroup.eq.mp same)).elim
  | some letter =>
      cases second with
      | none =>
          exact (outside letter (by simpa [tag] using QuotientGroup.eq.mp same.symm)).elim
      | some other => exact congrArg some (separated same)

theorem head_coset (embedding : G →* G) (digit : α → G) (word : List α) :
    ((encode embedding digit word : G) : G ⧸ embedding.range) =
      tag embedding digit word.head? := by
  cases word with
  | nil => rfl
  | cons letter tail =>
      exact QuotientGroup.mk_mul_of_mem (digit letter) ⟨encode embedding digit tail, rfl⟩

/-- Separation in one quotient and injective descent preserve every finite word. -/
theorem encode_injective (embedding : G →* G) (digit : α → G)
    (injective : Function.Injective embedding)
    (separated : Function.Injective (tag embedding digit)) :
    Function.Injective (encode embedding digit) := by
  intro first
  induction first with
  | nil =>
      intro second same
      have heads := separated ((head_coset embedding digit []).symm.trans
        ((congrArg (fun x : G => (x : G ⧸ embedding.range)) same).trans
          (head_coset embedding digit second)))
      cases second <;> simp_all
  | cons letter tail previous =>
      intro second same
      have heads := separated ((head_coset embedding digit (letter :: tail)).symm.trans
        ((congrArg (fun x : G => (x : G ⧸ embedding.range)) same).trans
          (head_coset embedding digit second)))
      cases second with
      | nil => cases heads
      | cons other rest =>
          have letters : letter = other := Option.some.inj heads
          subst other
          apply congrArg (List.cons letter)
          apply previous
          exact injective (mul_left_cancel same)

/-- Prefix composition is a twisted product, valid also in noncommutative groups. -/
theorem encode_append (embedding : G →* G) (digit : α → G) (first second : List α) :
    encode embedding digit (first ++ second) =
      encode embedding digit first * embedding^[first.length] (encode embedding digit second) := by
  induction first with
  | nil => simp [encode]
  | cons letter tail previous =>
      simp only [List.cons_append, encode, previous, map_mul, List.length_cons,
        Function.iterate_succ_apply', mul_assoc]

theorem infinite_memory [Nonempty α] (embedding : G →* G) (digit : α → G)
    (injective : Function.Injective embedding)
    (separated : Function.Injective (tag embedding digit)) : Infinite G :=
  Infinite.of_injective (encode embedding digit) (encode_injective embedding digit injective separated)

end Monodromy.SelfEmbedding

namespace Monodromy.SelfEmbedding

variable {G α : Type*} [Group G]

/-- The quotient reveals the head through the selected empty and letter cosets. -/
noncomputable def head (embedding : G →* G) (digit : α → G) (state : G) : Option α :=
  Function.invFun (tag embedding digit) (state : G ⧸ embedding.range)

theorem head_encode (embedding : G →* G) (digit : α → G)
    (separated : Function.Injective (tag embedding digit)) (word : List α) :
    head embedding digit (encode embedding digit word) = word.head? := by
  unfold head
  rw [head_coset]
  exact Function.leftInverse_invFun separated word.head?

/-- Remove the observed representative, then invert one level of the embedding. -/
noncomputable def pop (embedding : G →* G) (digit : α → G) (state : G) : G :=
  match head embedding digit state with
  | none => 1
  | some letter => Function.invFun embedding ((digit letter)⁻¹ * state)

/-- The quotient observation and the embedding inverse derive the complete pop law. -/
theorem pop_encode (embedding : G →* G) (digit : α → G)
    (injective : Function.Injective embedding)
    (separated : Function.Injective (tag embedding digit)) (word : List α) :
    pop embedding digit (encode embedding digit word) = encode embedding digit word.tail := by
  unfold pop
  rw [head_encode embedding digit separated]
  cases word with
  | nil => rfl
  | cons letter tail =>
      simp only [List.head?_cons, List.tail_cons, encode, inv_mul_cancel_left]
      exact Function.leftInverse_invFun injective (encode embedding digit tail)

theorem pop_closed (embedding : G →* G) (digit : α → G)
    (injective : Function.Injective embedding)
    (separated : Function.Injective (tag embedding digit))
    {state : G} (valid : state ∈ Set.range (encode embedding digit)) :
    pop embedding digit state ∈ Set.range (encode embedding digit) := by
  obtain ⟨word, rfl⟩ := valid
  exact ⟨word.tail, (pop_encode embedding digit injective separated word).symm⟩

end Monodromy.SelfEmbedding

namespace Monodromy.SelfEmbedding

variable {G α : Type*} [Group G]

/-- The quotient supports a correct word-head readout exactly when its tags separate. -/
theorem head_readout_iff (embedding : G →* G) (digit : α → G) :
    (∃ read : G ⧸ embedding.range → Option α, ∀ word : List α,
      read ((encode embedding digit word : G) : G ⧸ embedding.range) = word.head?) ↔
      Function.Injective (tag embedding digit) := by
  constructor
  · rintro ⟨read, correct⟩
    have left_inverse (letter : Option α) : read (tag embedding digit letter) = letter := by
      cases letter with
      | none => simpa [encode, tag] using correct []
      | some letter => simpa [encode, tag] using correct [letter]
    intro first second same
    exact (left_inverse first).symm.trans ((congrArg read same).trans (left_inverse second))
  · intro separated
    refine ⟨Function.invFun (tag embedding digit), ?_⟩
    intro word
    rw [head_coset]
    exact Function.leftInverse_invFun separated word.head?

/-- Faithful words force injective descent on all reachable tails. -/
theorem embedding_injective_on_codes (embedding : G →* G) (digit : α → G)
    (faithful : Function.Injective (encode embedding digit))
    (first second : List α)
    (same : embedding (encode embedding digit first) = embedding (encode embedding digit second)) :
    encode embedding digit first = encode embedding digit second := by
  have with_letter (letter : α) : encode embedding digit first = encode embedding digit second := by
    have identical : encode embedding digit (letter :: first) =
        encode embedding digit (letter :: second) := congrArg (fun state => digit letter * state) same
    exact congrArg (encode embedding digit) (List.cons.inj (faithful identical)).2
  cases first with
  | nil =>
      cases second with
      | nil => rfl
      | cons letter tail => exact with_letter letter
  | cons letter tail => exact with_letter letter

/-- Reachable injectivity suffices; behavior elsewhere in the group is unrestricted. -/
theorem encode_injective_of_reachable (embedding : G →* G) (digit : α → G)
    (reachable : ∀ first second : List α,
      embedding (encode embedding digit first) = embedding (encode embedding digit second) →
        encode embedding digit first = encode embedding digit second)
    (separated : Function.Injective (tag embedding digit)) :
    Function.Injective (encode embedding digit) := by
  intro first
  induction first with
  | nil =>
      intro second same
      have heads := separated ((head_coset embedding digit []).symm.trans
        ((congrArg (fun state : G => (state : G ⧸ embedding.range)) same).trans
          (head_coset embedding digit second)))
      cases second <;> simp_all
  | cons letter tail previous =>
      intro second same
      have heads := separated ((head_coset embedding digit (letter :: tail)).symm.trans
        ((congrArg (fun state : G => (state : G ⧸ embedding.range)) same).trans
          (head_coset embedding digit second)))
      cases second with
      | nil => cases heads
      | cons other rest =>
          have letters : letter = other := Option.some.inj heads
          subst other
          apply congrArg (List.cons letter)
          apply previous
          exact reachable tail rest (mul_left_cancel same)

/-- Under separated head tags, reachable injectivity is the exact remaining condition. -/
theorem encode_injective_iff_reachable (embedding : G →* G) (digit : α → G)
    (separated : Function.Injective (tag embedding digit)) :
    Function.Injective (encode embedding digit) ↔
      ∀ first second : List α,
        embedding (encode embedding digit first) = embedding (encode embedding digit second) →
          encode embedding digit first = encode embedding digit second :=
  ⟨fun faithful => embedding_injective_on_codes embedding digit faithful,
    fun reachable => encode_injective_of_reachable embedding digit reachable separated⟩

end Monodromy.SelfEmbedding

namespace Monodromy.SelfEmbedding

variable {G α : Type*} [Group G]

abbrev CodeMemory (embedding : G →* G) (digit : α → G) :=
  {state : G // state ∈ Set.range (encode embedding digit)}

def retain (embedding : G →* G) (digit : α → G) (word : List α) :
    CodeMemory embedding digit := ⟨encode embedding digit word, word, rfl⟩

instance codeMemory_inhabited (embedding : G →* G) (digit : α → G) :
    Inhabited (CodeMemory embedding digit) := ⟨retain embedding digit []⟩

def restrictedEmbedding (embedding : G →* G) (digit : α → G) :
    CodeMemory embedding digit → G := fun memory => embedding memory.val

theorem restrictedEmbedding_injective (embedding : G →* G) (digit : α → G)
    (reachable : ∀ first second : List α,
      embedding (encode embedding digit first) = embedding (encode embedding digit second) →
        encode embedding digit first = encode embedding digit second) :
    Function.Injective (restrictedEmbedding embedding digit) := by
  intro first second same
  apply Subtype.ext
  obtain ⟨first_word, first_code⟩ := first.property
  obtain ⟨second_word, second_code⟩ := second.property
  calc
    first.val = encode embedding digit first_word := first_code.symm
    _ = encode embedding digit second_word := reachable first_word second_word (by
      rw [first_code, second_code]
      exact same)
    _ = second.val := second_code

/-- Restricting inverse search to valid memories recovers the unique reachable tail. -/
theorem restricted_inverse_prefix (embedding : G →* G) (digit : α → G)
    (reachable : ∀ first second : List α,
      embedding (encode embedding digit first) = embedding (encode embedding digit second) →
        encode embedding digit first = encode embedding digit second)
    (letter : α) (tail : List α) :
    Function.invFun (restrictedEmbedding embedding digit)
      ((digit letter)⁻¹ * encode embedding digit (letter :: tail)) = retain embedding digit tail := by
  simp only [encode, inv_mul_cancel_left]
  exact Function.leftInverse_invFun
    (restrictedEmbedding_injective embedding digit reachable) (retain embedding digit tail)

/-- The reachable inverse always returns a legal code; quotient readout selects its branch. -/
noncomputable def popReachable (embedding : G →* G) (digit : α → G) (state : G) :
    CodeMemory embedding digit :=
  match head embedding digit state with
  | none => retain embedding digit []
  | some letter => Function.invFun (restrictedEmbedding embedding digit) ((digit letter)⁻¹ * state)

theorem popReachable_encode (embedding : G →* G) (digit : α → G)
    (reachable : ∀ first second : List α,
      embedding (encode embedding digit first) = embedding (encode embedding digit second) →
        encode embedding digit first = encode embedding digit second)
    (separated : Function.Injective (tag embedding digit)) (word : List α) :
    popReachable embedding digit (encode embedding digit word) = retain embedding digit word.tail := by
  unfold popReachable
  rw [head_encode embedding digit separated]
  cases word with
  | nil => rfl
  | cons letter tail => exact restricted_inverse_prefix embedding digit reachable letter tail

end Monodromy.SelfEmbedding
