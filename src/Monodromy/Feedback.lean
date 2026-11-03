module

public import Monodromy.Covering
public import Monodromy.BaseChange
public import Monodromy.Observation
public import Monodromy.Choice
public import Monodromy.Logarithm

/-!
# Continuation under internal feedback

A policy assigns a based path to each retained fiber state. Homotopy of
these paths and isomorphism of covers preserve complete stopping semantics.
Policies here are mathematical maps; effectiveness is an additional property.
-/

@[expose] public section

namespace Monodromy.Feedback

universe u v

variable {E E' : Type u} {X : Type v}
  [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace X]
  {p : E → X} {q : E' → X} {x : X}

abbrev Policy (projection : E → X) (base : X) :=
  Transport.Fiber projection base → Path base base

noncomputable def next (covering : IsCoveringMap p)
    (policy : Transport.Fiber p x → Path x x) (state : Transport.Fiber p x) :
    Transport.Fiber p x :=
  Transport.transport covering (policy state) state

noncomputable def step (covering : IsCoveringMap p)
    (policy : Transport.Fiber p x → Path x x) (halt : Transport.Fiber p x → Bool) :
    Transport.Fiber p x → Option (Transport.Fiber p x) :=
  Observation.stopped (next covering policy) halt

noncomputable def eval (covering : IsCoveringMap p)
    (policy : Transport.Fiber p x → Path x x) (halt : Transport.Fiber p x → Bool) :
    Transport.Fiber p x → Part (Transport.Fiber p x) :=
  StateTransition.eval (step covering policy halt)

section Homotopy

variable (covering : IsCoveringMap p)
  (first second : Transport.Fiber p x → Path x x)
  (halt : Transport.Fiber p x → Bool)

theorem next_eq_of_homotopic (homotopic : ∀ state, (first state).Homotopic (second state)) :
    next covering first = next covering second := by
  funext state
  exact Transport.transport_homotopic covering (homotopic state) state

/-- Pointwise path homotopy preserves every final state and the entire partial execution. -/
theorem eval_eq_of_homotopic (homotopic : ∀ state, (first state).Homotopic (second state)) :
    eval covering first halt = eval covering second halt := by
  unfold eval step
  rw [next_eq_of_homotopic covering first second homotopic]

theorem halting_iff_of_homotopic
    (homotopic : ∀ state, (first state).Homotopic (second state)) (state : Transport.Fiber p x) :
    (eval covering first halt state).Dom ↔ (eval covering second halt state).Dom := by
  rw [eval_eq_of_homotopic covering first second halt homotopic]

theorem divergence_iff_of_homotopic
    (homotopic : ∀ state, (first state).Homotopic (second state)) (state : Transport.Fiber p x) :
    ¬ (eval covering first halt state).Dom ↔ ¬ (eval covering second halt state).Dom :=
  not_congr (halting_iff_of_homotopic covering first second halt homotopic state)

end Homotopy

section Isomorphism

variable (covering : IsCoveringMap p) (covering' : IsCoveringMap q)
  (h : E ≃ₜ E') (square : q ∘ h = p)
  (policy : Transport.Fiber p x → Path x x)
  (policy' : Transport.Fiber q x → Path x x)
  (halt : Transport.Fiber p x → Bool) (halt' : Transport.Fiber q x → Bool)

/-- Covariant internal paths conjugate the state-dependent return maps. -/
theorem next_conjugate
    (covariant : ∀ state, (policy' (Transport.fiberEquiv h square x state)).Homotopic (policy state))
    (state : Transport.Fiber p x) :
    Transport.fiberEquiv h square x (next covering policy state) =
      next covering' policy' (Transport.fiberEquiv h square x state) := by
  unfold next
  rw [Transport.fiberEquiv_transport covering covering' h square]
  exact Transport.transport_homotopic covering' (covariant state).symm _

/-- A cover isomorphism transports the complete final state, halting, and divergence semantics. -/
theorem eval_conjugate
    (covariant : ∀ state, (policy' (Transport.fiberEquiv h square x state)).Homotopic (policy state))
    (halts : ∀ state, halt' (Transport.fiberEquiv h square x state) = halt state)
    (state : Transport.Fiber p x) :
    eval covering' policy' halt' (Transport.fiberEquiv h square x state) =
      Transport.fiberEquiv h square x <$> eval covering policy halt state := by
  have observed := Observation.observed_eval (Transport.fiberEquiv h square x)
    (next covering policy) (next covering' policy') halt'
    (next_conjugate covering covering' h square policy policy' covariant) state
  have halt_eq : (fun state => halt' (Transport.fiberEquiv h square x state)) = halt := funext halts
  rw [halt_eq] at observed
  exact observed

theorem halting_iff_conjugate
    (covariant : ∀ state, (policy' (Transport.fiberEquiv h square x state)).Homotopic (policy state))
    (halts : ∀ state, halt' (Transport.fiberEquiv h square x state) = halt state)
    (state : Transport.Fiber p x) :
    (eval covering' policy' halt' (Transport.fiberEquiv h square x state)).Dom ↔
      (eval covering policy halt state).Dom := by
  rw [eval_conjugate covering covering' h square policy policy' halt halt' covariant halts state]
  rfl

theorem divergence_iff_conjugate
    (covariant : ∀ state, (policy' (Transport.fiberEquiv h square x state)).Homotopic (policy state))
    (halts : ∀ state, halt' (Transport.fiberEquiv h square x state) = halt state)
    (state : Transport.Fiber p x) :
    ¬ (eval covering' policy' halt' (Transport.fiberEquiv h square x state)).Dom ↔
      ¬ (eval covering policy halt state).Dom :=
  not_congr (halting_iff_conjugate covering covering' h square policy policy' halt halt'
    covariant halts state)

end Isomorphism

end Monodromy.Feedback

namespace Monodromy.Feedback

universe u v

variable {E : Type u} {X : Type v} [TopologicalSpace E] [TopologicalSpace X]
  {projection : E → X} {base : X}

/-- A policy which descends through a covering symmetry induces an equivariant successor. -/
theorem commute_of_policy_invariant (covering : IsCoveringMap projection)
    (policy : Policy projection base) (symmetry : C(E, E))
    (square : projection ∘ symmetry = projection)
    (invariant : ∀ state,
      (policy (Transport.mapFiber symmetry square state)).Homotopic (policy state)) :
    Function.Commute (Transport.mapFiber symmetry square) (next covering policy) := by
  intro state
  change Transport.mapFiber symmetry square
    (Transport.transport covering (policy state) state) =
      Transport.transport covering (policy (Transport.mapFiber symmetry square state))
        (Transport.mapFiber symmetry square state)
  exact (Transport.selfmap_commutes covering symmetry square (policy state) state).trans
    (Transport.transport_homotopic covering (invariant state).symm _)

/-- On a transitive family of policy symmetries, fixing one state fixes every state. -/
theorem fixed_of_transitive_policy_symmetries (covering : IsCoveringMap projection)
    (policy : Policy projection base)
    (transitive : ∀ source target : Transport.Fiber projection base,
      ∃ symmetry : C(E, E), ∃ square : projection ∘ symmetry = projection,
        (∀ state,
          (policy (Transport.mapFiber symmetry square state)).Homotopic (policy state)) ∧
        Transport.mapFiber symmetry square source = target)
    {source : Transport.Fiber projection base} (fixed : next covering policy source = source) :
    ∀ target, next covering policy target = target := by
  apply Choice.fixed_of_transitive_commutants (next covering policy) ?_ fixed
  intro first second
  obtain ⟨symmetry, square, invariant, sends⟩ := transitive first second
  exact ⟨Transport.mapFiber symmetry square,
    commute_of_policy_invariant covering policy symmetry square invariant, sends⟩

theorem not_selective_of_transitive_policy_symmetries (covering : IsCoveringMap projection)
    (policy : Policy projection base)
    (transitive : ∀ source target : Transport.Fiber projection base,
      ∃ symmetry : C(E, E), ∃ square : projection ∘ symmetry = projection,
        (∀ state,
          (policy (Transport.mapFiber symmetry square state)).Homotopic (policy state)) ∧
        Transport.mapFiber symmetry square source = target) :
    ¬ Choice.Selective (next covering policy) := by
  rintro ⟨source, target, fixed, moved⟩
  exact moved (fixed_of_transitive_policy_symmetries covering policy transitive fixed target)

/-- Selective feedback on a transitive covering requires asymmetry of the generated path classes. -/
theorem policy_asymmetry_of_selective (covering : IsCoveringMap projection)
    (policy : Policy projection base)
    (transitive : ∀ source target : Transport.Fiber projection base,
      ∃ symmetry : C(E, E), ∃ square : projection ∘ symmetry = projection,
        Transport.mapFiber symmetry square source = target)
    (selective : Choice.Selective (next covering policy)) :
    ∃ symmetry : C(E, E), ∃ square : projection ∘ symmetry = projection,
      ∃ state, ¬ (policy (Transport.mapFiber symmetry square state)).Homotopic (policy state) := by
  classical
  by_contra absent
  apply not_selective_of_transitive_policy_symmetries covering policy ?_ selective
  intro source target
  obtain ⟨symmetry, square, sends⟩ := transitive source target
  refine ⟨symmetry, square, ?_, sends⟩
  intro state
  by_contra different
  exact absent ⟨symmetry, square, state, different⟩

namespace Circle

noncomputable def stay : Policy Circle.exp 1 := fun _ => Path.refl 1

noncomputable def turnOne : Policy Circle.exp 1 := fun _ => Logarithm.turn 1

theorem next_stay (state : Logarithm.Memory) :
    next Circle.isCoveringMap_exp stay state = state := Transport.transport_refl _ _

theorem next_turnOne (k : ℤ) :
    next Circle.isCoveringMap_exp turnOne (Logarithm.sheet k) = Logarithm.sheet (k + 1) :=
  Logarithm.transport_turn k 1

/-- The same covering supports distinct return laws, before any state-dependent selection. -/
theorem same_cover_different_returns :
    next Circle.isCoveringMap_exp stay ≠ next Circle.isCoveringMap_exp turnOne := by
  intro same
  have shifted := congrFun same (Logarithm.sheet 0)
  rw [next_stay, next_turnOne] at shifted
  have impossible := Logarithm.integers.injective shifted
  norm_num at impossible

noncomputable def deck (k : ℤ) : C(ℝ, ℝ) :=
  ⟨fun x => x + (k : ℝ) * (2 * Real.pi), continuous_id.add continuous_const⟩

theorem deck_square (k : ℤ) : Circle.exp ∘ deck k = Circle.exp := by
  funext x
  simp [deck, Circle.exp_add]

theorem deck_sheet (k j : ℤ) :
    Transport.mapFiber (deck k) (deck_square k) (Logarithm.sheet j) =
      Logarithm.sheet (j + k) := by
  apply Subtype.ext
  simp [Transport.mapFiber, deck, Logarithm.sheet, add_mul]

/-- Full deck-invariance of the generated path class leaves only a uniform branch translation. -/
theorem translation_of_policy_invariant (policy : Policy Circle.exp 1)
    (invariant : ∀ (k : ℤ) (state : Logarithm.Memory),
      (policy (Transport.mapFiber (deck k) (deck_square k) state)).Homotopic (policy state))
    (k : ℤ) :
    next Circle.isCoveringMap_exp policy (Logarithm.sheet k) =
      Logarithm.sheet (k + Logarithm.integers.symm
        (next Circle.isCoveringMap_exp policy (Logarithm.sheet 0))) := by
  let shift := Logarithm.integers.symm
    (next Circle.isCoveringMap_exp policy (Logarithm.sheet 0))
  have recorded : Logarithm.sheet shift =
      next Circle.isCoveringMap_exp policy (Logarithm.sheet 0) :=
    Logarithm.integers.apply_symm_apply _
  have commutes := commute_of_policy_invariant Circle.isCoveringMap_exp policy
    (deck k) (deck_square k) (invariant k) (Logarithm.sheet 0)
  rw [← recorded, deck_sheet, deck_sheet, zero_add] at commutes
  simpa only [add_comm] using commutes.symm

end Circle

end Monodromy.Feedback

namespace Monodromy.Feedback

universe u v w

variable {E E' : Type u} {X : Type v} {Y : Type w}
  [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace X] [TopologicalSpace Y]
  {p : E → X} {q : E' → Y} {x : X}
  (covering : IsCoveringMap p) (covering' : IsCoveringMap q)
  (h : E ≃ₜ E') (b : X ≃ₜ Y) (square : q ∘ h = b ∘ p)
  (policy : Transport.Fiber p x → Path x x)
  (policy' : Transport.Fiber q (b x) → Path (b x) (b x))
  (halt : Transport.Fiber p x → Bool) (halt' : Transport.Fiber q (b x) → Bool)

/-- Internal feedback follows a change of both base and total-space coordinates. -/
theorem next_conjugate_baseChange
    (covariant : ∀ state,
      (policy' (BaseChange.fiberEquiv h b square x state)).Homotopic
        ((policy state).map b.continuous)) (state : Transport.Fiber p x) :
    BaseChange.fiberEquiv h b square x (next covering policy state) =
      next covering' policy' (BaseChange.fiberEquiv h b square x state) := by
  unfold next
  rw [BaseChange.transport covering covering' h b square]
  exact Transport.transport_homotopic covering' (covariant state).symm _

/-- The corresponding policies preserve the complete partial execution across base coordinates. -/
theorem eval_conjugate_baseChange
    (covariant : ∀ state,
      (policy' (BaseChange.fiberEquiv h b square x state)).Homotopic
        ((policy state).map b.continuous))
    (halts : ∀ state, halt' (BaseChange.fiberEquiv h b square x state) = halt state)
    (state : Transport.Fiber p x) :
    eval covering' policy' halt' (BaseChange.fiberEquiv h b square x state) =
      BaseChange.fiberEquiv h b square x <$> eval covering policy halt state := by
  have observed := Observation.observed_eval (BaseChange.fiberEquiv h b square x)
    (next covering policy) (next covering' policy') halt'
    (next_conjugate_baseChange covering covering' h b square policy policy' covariant) state
  have halt_eq : (fun state => halt' (BaseChange.fiberEquiv h b square x state)) = halt := funext halts
  rw [halt_eq] at observed
  exact observed

end Monodromy.Feedback

namespace Monodromy.Feedback

universe u v

variable {E : Type u} {X : Type v} [TopologicalSpace E] [TopologicalSpace X]
  {projection : E → X} {base : X}

noncomputable def identity : Policy projection base := fun _ => Path.refl base

noncomputable def sequence (covering : IsCoveringMap projection)
    (first second : Policy projection base) : Policy projection base :=
  fun state => (first state).trans (second (next covering first state))

theorem next_identity (covering : IsCoveringMap projection) :
    next covering (identity (base := base)) = id := by
  funext state
  exact Transport.transport_refl covering state

/-- The actual updated state supplies the input to the second policy. -/
theorem next_sequence (covering : IsCoveringMap projection)
    (first second : Policy projection base) :
    next covering (sequence covering first second) = next covering second ∘ next covering first := by
  funext state
  exact Transport.transport_trans covering (first state) (second (next covering first state)) state

theorem identity_sequence_homotopic (covering : IsCoveringMap projection)
    (policy : Policy projection base) (state : Transport.Fiber projection base) :
    (sequence covering identity policy state).Homotopic (policy state) := by
  simpa [sequence, identity, next] using Path.Homotopic.refl_trans (policy state)

theorem sequence_identity_homotopic (covering : IsCoveringMap projection)
    (policy : Policy projection base) (state : Transport.Fiber projection base) :
    (sequence covering policy identity state).Homotopic (policy state) := by
  exact Path.Homotopic.trans_refl (policy state)

/-- Sequential grouping changes the path parametrization while preserving its homotopy class. -/
theorem sequence_assoc_homotopic (covering : IsCoveringMap projection)
    (first second third : Policy projection base) (state : Transport.Fiber projection base) :
    (sequence covering (sequence covering first second) third state).Homotopic
      (sequence covering first (sequence covering second third) state) := by
  have reached := congrFun (next_sequence covering first second) state
  change
    (((first state).trans (second (next covering first state))).trans
      (third (next covering (sequence covering first second) state))).Homotopic
    ((first state).trans ((second (next covering first state)).trans
      (third (next covering second (next covering first state)))))
  rw [reached]
  exact Path.Homotopic.trans_assoc _ _ _

theorem next_sequence_assoc (covering : IsCoveringMap projection)
    (first second third : Policy projection base) :
    next covering (sequence covering (sequence covering first second) third) =
      next covering (sequence covering first (sequence covering second third)) :=
  next_eq_of_homotopic covering _ _ (sequence_assoc_homotopic covering first second third)

end Monodromy.Feedback

namespace Monodromy.Feedback.Circle

/-- The branch displacement is the entire observable effect of one based loop. -/
noncomputable def winding (path : Path (1 : Circle) 1) : ℤ :=
  Logarithm.integers.symm
    (Transport.transport Circle.isCoveringMap_exp path (Logarithm.sheet 0))

theorem next_sheet (policy : Policy Circle.exp 1) (k : ℤ) :
    next Circle.isCoveringMap_exp policy (Logarithm.sheet k) =
      Logarithm.sheet (k + winding (policy (Logarithm.sheet k))) :=
  Logarithm.transport_translation (policy (Logarithm.sheet k)) k

/-- The state-indexed winding function completely determines the return law. -/
theorem next_eq_iff_winding (first second : Policy Circle.exp 1) :
    next Circle.isCoveringMap_exp first = next Circle.isCoveringMap_exp second ↔
      ∀ k : ℤ, winding (first (Logarithm.sheet k)) = winding (second (Logarithm.sheet k)) := by
  constructor
  · intro same k
    have values := congrFun same (Logarithm.sheet k)
    rw [next_sheet, next_sheet] at values
    exact add_left_cancel (Logarithm.integers.injective values)
  · intro same
    funext state
    obtain ⟨k, rfl⟩ := Logarithm.integers.surjective state
    change next Circle.isCoveringMap_exp first (Logarithm.sheet k) =
      next Circle.isCoveringMap_exp second (Logarithm.sheet k)
    rw [next_sheet, next_sheet, same k]

/-- An unrestricted policy may encode any set-theoretic integer return law. -/
noncomputable def policyFor (operation : ℤ → ℤ) : Policy Circle.exp 1 := fun state =>
  Logarithm.turn (operation (Logarithm.integers.symm state) - Logarithm.integers.symm state)

theorem next_policyFor (operation : ℤ → ℤ) (k : ℤ) :
    next Circle.isCoveringMap_exp (policyFor operation) (Logarithm.sheet k) =
      Logarithm.sheet (operation k) := by
  change Transport.transport Circle.isCoveringMap_exp
    (Logarithm.turn (operation (Logarithm.integers.symm (Logarithm.sheet k)) -
      Logarithm.integers.symm (Logarithm.sheet k))) (Logarithm.sheet k) = _
  rw [show Logarithm.integers.symm (Logarithm.sheet k) = k from
    Logarithm.integers.symm_apply_apply k, Logarithm.transport_turn]
  congr 1
  omega

/-- Topological realization alone imposes no restriction on arbitrary feedback maps. -/
theorem realizes_every_return (operation : Logarithm.Memory → Logarithm.Memory) :
    ∃ policy : Policy Circle.exp 1, next Circle.isCoveringMap_exp policy = operation := by
  refine ⟨policyFor (fun k => Logarithm.integers.symm (operation (Logarithm.sheet k))), ?_⟩
  funext state
  obtain ⟨k, rfl⟩ := Logarithm.integers.surjective state
  change next Circle.isCoveringMap_exp
    (policyFor (fun k => Logarithm.integers.symm (operation (Logarithm.sheet k))))
    (Logarithm.sheet k) = operation (Logarithm.sheet k)
  rw [next_policyFor]
  exact Logarithm.integers.apply_symm_apply _

end Monodromy.Feedback.Circle

namespace Monodromy.Feedback.Circle

theorem winding_trans (first second : Path (1 : Circle) 1) :
    winding (first.trans second) = winding first + winding second := by
  have first_end : Transport.transport Circle.isCoveringMap_exp first (Logarithm.sheet 0) =
      Logarithm.sheet (winding first) := (Logarithm.integers.apply_symm_apply _).symm
  change Logarithm.integers.symm (Transport.transport Circle.isCoveringMap_exp
    (first.trans second) (Logarithm.sheet 0)) = winding first + winding second
  rw [Transport.transport_trans, first_end, Logarithm.transport_translation]
  exact Logarithm.integers.symm_apply_apply _

/-- Sequential feedback adds the second displacement at the updated branch. -/
theorem winding_sequence (first second : Policy Circle.exp 1) (k : ℤ) :
    winding (sequence Circle.isCoveringMap_exp first second (Logarithm.sheet k)) =
      winding (first (Logarithm.sheet k)) +
        winding (second (Logarithm.sheet (k + winding (first (Logarithm.sheet k))))) := by
  unfold sequence
  rw [winding_trans, next_sheet]

end Monodromy.Feedback.Circle

namespace Monodromy.Feedback

universe u v

variable {E E' : Type u} {X : Type v}
  [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace X]
  {p : E → X} {q : E' → X} {x : X}
  (covering : IsCoveringMap p) (covering' : IsCoveringMap q)
  (observe : C(E, E')) (square : q ∘ observe = p)
  (policy : Policy p x) (policy' : Policy q x)
  (halt : Transport.Fiber p x → Bool) (halt' : Transport.Fiber q x → Bool)

/-- A commuting cover map preserves returns when the internal path classes descend. -/
theorem next_refinement
    (covariant : ∀ state, (policy' (Transport.mapFiber observe square state)).Homotopic (policy state))
    (state : Transport.Fiber p x) :
    Transport.mapFiber observe square (next covering policy state) =
      next covering' policy' (Transport.mapFiber observe square state) := by
  unfold next
  rw [← Transport.transport_naturality covering covering' observe square]
  exact Transport.transport_homotopic covering' (covariant state).symm _

/-- A refined branch memory preserves complete coarse computation, including divergence. -/
theorem eval_refinement
    (covariant : ∀ state, (policy' (Transport.mapFiber observe square state)).Homotopic (policy state))
    (halts : ∀ state, halt' (Transport.mapFiber observe square state) = halt state)
    (state : Transport.Fiber p x) :
    eval covering' policy' halt' (Transport.mapFiber observe square state) =
      Transport.mapFiber observe square <$> eval covering policy halt state := by
  have observed := Observation.observed_eval (Transport.mapFiber observe square)
    (next covering policy) (next covering' policy') halt'
    (next_refinement covering covering' observe square policy policy' covariant) state
  have same_halt : (fun state => halt' (Transport.mapFiber observe square state)) = halt := funext halts
  rw [same_halt] at observed
  exact observed

theorem halting_iff_refinement
    (covariant : ∀ state, (policy' (Transport.mapFiber observe square state)).Homotopic (policy state))
    (halts : ∀ state, halt' (Transport.mapFiber observe square state) = halt state)
    (state : Transport.Fiber p x) :
    (eval covering policy halt state).Dom ↔
      (eval covering' policy' halt' (Transport.mapFiber observe square state)).Dom := by
  rw [eval_refinement covering covering' observe square policy policy' halt halt' covariant halts state]
  rfl

end Monodromy.Feedback

namespace Monodromy.Feedback

universe u v

variable {E E' : Type u} {X : Type v}
  [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace X]
  {p : E → X} {q : E' → X} {x : X}
  (observe : C(E, E')) (square : q ∘ observe = p)

/-- An old policy reads the coarse branch carried by the refined memory. -/
def pullback (policy : Policy q x) : Policy p x :=
  fun state => policy (Transport.mapFiber observe square state)

omit [TopologicalSpace X] in
theorem fiber_surjective (onto : Function.Surjective observe) :
    Function.Surjective (Transport.mapFiber observe square : Transport.Fiber p x → Transport.Fiber q x) := by
  intro state
  obtain ⟨source, same⟩ := onto state.val
  refine ⟨⟨source, ?_⟩, Subtype.ext same⟩
  calc
    p source = q (observe source) := (congrFun square source).symm
    _ = q state.val := congrArg q same
    _ = x := state.property

/-- Pullback constructs the path and halt covariance required for full program preservation. -/
theorem eval_pullback (covering : IsCoveringMap p) (covering' : IsCoveringMap q)
    (policy : Policy q x) (halt : Transport.Fiber q x → Bool) (state : Transport.Fiber p x) :
    eval covering' policy halt (Transport.mapFiber observe square state) =
      Transport.mapFiber observe square <$>
        eval covering (pullback observe square policy)
          (fun source => halt (Transport.mapFiber observe square source)) state :=
  eval_refinement covering covering' observe square _ policy _ halt
    (fun source => Path.Homotopic.refl (policy (Transport.mapFiber observe square source)))
    (fun _ => rfl) state

/-- A surjective refinement lifts every old initial branch and its complete execution. -/
theorem every_coarse_run (covering : IsCoveringMap p) (covering' : IsCoveringMap q)
    (onto : Function.Surjective observe) (policy : Policy q x) (halt : Transport.Fiber q x → Bool)
    (state : Transport.Fiber q x) :
    ∃ source : Transport.Fiber p x,
      Transport.mapFiber observe square source = state ∧
      eval covering' policy halt state =
        Transport.mapFiber observe square <$>
          eval covering (pullback observe square policy)
            (fun current => halt (Transport.mapFiber observe square current)) source := by
  obtain ⟨source, same⟩ := fiber_surjective observe square onto state
  exact ⟨source, same, same ▸ eval_pullback observe square covering covering' policy halt source⟩

theorem pullback_comp {E'' : Type u} [TopologicalSpace E''] {r : E'' → X}
    (observe' : C(E', E'')) (square' : r ∘ observe' = q) (policy : Policy r x) :
    pullback observe square (pullback observe' square' policy) =
      pullback (observe'.comp observe) (by
        funext state
        exact (congrFun square' (observe state)).trans (congrFun square state)) policy := rfl

theorem pullback_identity (policy : Policy p x) :
    pullback (ContinuousMap.id E) rfl policy = policy := rfl

end Monodromy.Feedback

namespace Monodromy.Feedback.Circle

/-- State-dependent paths can compose noncommutatively in the same logarithmic cover. -/
theorem exists_noncommuting_returns :
    ∃ first second : Policy Circle.exp 1,
      ¬ Function.Commute (next Circle.isCoveringMap_exp first)
        (next Circle.isCoveringMap_exp second) := by
  refine ⟨policyFor (fun k => k + 1), policyFor (fun k => 3 * k), ?_⟩
  intro commuting
  have same := commuting (Logarithm.sheet 0)
  simp only [next_policyFor] at same
  have impossible := Logarithm.integers.injective same
  norm_num at impossible

end Monodromy.Feedback.Circle
