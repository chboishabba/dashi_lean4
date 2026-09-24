import Integration.Marginalisation

/-!
# The interaction owner: separability, weighted contrasts and reversal

Simpson-type reversals, contextual/intersectional products, provisioning
heterogeneity and threshold trajectories all reduce to one statement about a
two-coordinate consumer:

> for a **separable** consumer the contrast in one coordinate is the same under
> **every** weighting of the other coordinate; hence a contrast that reverses
> when the weighting changes is a proof of interaction.

`Integration.Marginalisation` proves this for `Bool`-indexed consumers valued in
`ℚ` under a convex weighting.  That is one instance.  This file owns the
statement in the general form the other lanes need: an arbitrary first
coordinate, an arbitrary finite second coordinate, values in an arbitrary field,
and weightings required only to sum to one — no non-negativity, so the theorem
covers signed reweightings as well.

Separability itself is *not* redefined: it is
`Integration.CoordinateSufficiency.Separable`, the existing owner.

## Contents

* `marginal`, `contrast` — the second coordinate averaged out, and the
  first-coordinate contrast that survives;
* `separable_marginal`, `separable_contrast_invariant` — **the owner theorem**;
* `not_separable_of_contrast_ne`, `not_separable_of_contrast_reversal` — its
  contrapositives: differing contrasts, and in particular a sign reversal,
  refute separability;
* `separable_iff_rectangle` — the pointwise characterisation, so a lane may
  supply either a rectangle violation or a reversal;
* `separable_no_reversal` — the positive companion: under separability no
  reweighting can reverse the sign of a contrast;
* `marginalisation_contrast_is_instance`,
  `marginalisation_invariance_is_instance` — the identification of the existing
  `Integration.Marginalisation` development as the `Bool`/`ℚ` instance, so the
  two are not parallel families;
* `simpsonInstance`, `thresholdInstance`, `productInstance` — three witnesses in
  different shapes (a pooled reversal, a trajectory whose ordering flips with
  the horizon, and a multiplicative interaction), each closed by the *same*
  owner theorem.

The carriers are `Bool`, `Fin n` and `ℚ`.  Nothing here is a claim about
populations, provisioning, learning or any empirical process.
-/

namespace Integration.SeparabilityContrast

open Integration.CoordinateSufficiency
open scoped BigOperators

/-! ## The owner -/

variable {A B : Type} [Fintype B] {K : Type} [Field K]

/-- The consumer with its second coordinate averaged out against the weighting
`w`. -/
def marginal (C : A → B → K) (w : B → K) (a : A) : K := ∑ b, w b * C a b

/-- The contrast between two values of the first coordinate, after the second
has been averaged out. -/
def contrast (C : A → B → K) (w : B → K) (a a' : A) : K :=
  marginal C w a - marginal C w a'

/-- For a separable consumer the marginal splits into its own first-coordinate
term plus a term that does not depend on the first coordinate at all. -/
theorem separable_marginal {C : A → B → K} {f : A → K} {g : B → K}
    (hC : ∀ a b, C a b = f a + g b) {w : B → K} (hw : ∑ b, w b = 1) (a : A) :
    marginal C w a = f a + ∑ b, w b * g b := by
  simp only [marginal, hC, mul_add]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, hw, one_mul]

/-- **The owner theorem.**  A separable consumer has a weighting-independent
contrast: averaging out the second coordinate loses nothing about the
first-coordinate effect, however the average is taken. -/
theorem separable_contrast_invariant {C : A → B → K} (h : Separable C)
    {w v : B → K} (hw : ∑ b, w b = 1) (hv : ∑ b, v b = 1) (a a' : A) :
    contrast C w a a' = contrast C v a a' := by
  obtain ⟨f, g, hfg⟩ := h
  simp only [contrast, separable_marginal hfg hw, separable_marginal hfg hv]
  ring

/-- **Differing contrasts refute separability.** -/
theorem not_separable_of_contrast_ne {C : A → B → K} {w v : B → K}
    (hw : ∑ b, w b = 1) (hv : ∑ b, v b = 1) {a a' : A}
    (h : contrast C w a a' ≠ contrast C v a a') : ¬ Separable C :=
  fun hsep => h (separable_contrast_invariant hsep hw hv a a')

section Ordered

variable {F : Type} [Field F] [LinearOrder F]

/-- **A contrast reversal is a proof of interaction.**  If one weighting of the
second coordinate makes the first-coordinate contrast positive and another makes
it negative, the consumer is not a sum of coordinatewise effects. -/
theorem not_separable_of_contrast_reversal {C : A → B → F} {w v : B → F}
    (hw : ∑ b, w b = 1) (hv : ∑ b, v b = 1) {a a' : A}
    (hpos : 0 < contrast C w a a') (hneg : contrast C v a a' < 0) : ¬ Separable C :=
  not_separable_of_contrast_ne hw hv (ne_of_gt (lt_trans hneg hpos))

/-- **The positive companion.**  Under separability no reweighting can reverse
the sign of a contrast: if it is positive for one weighting it is positive for
every weighting. -/
theorem separable_no_reversal {C : A → B → F} (h : Separable C) {w v : B → F}
    (hw : ∑ b, w b = 1) (hv : ∑ b, v b = 1) {a a' : A} (hpos : 0 < contrast C w a a') :
    0 < contrast C v a a' := by
  rwa [← separable_contrast_invariant h hw hv a a']

end Ordered

/-! ## The pointwise characterisation -/

omit [Fintype B] in
/-- **Separability is exactly the rectangle identity.**  A lane may therefore
supply either a rectangle violation or a contrast reversal; both are refutations
of the same property. -/
theorem separable_iff_rectangle [Nonempty A] [Nonempty B] {M : Type} [AddCommGroup M]
    (C : A → B → M) :
    Separable C ↔ ∀ a a' b b', C a b + C a' b' = C a b' + C a' b := by
  classical
  refine ⟨fun h a a' b b' => separable_rectangle h a a' b b', fun h => ?_⟩
  obtain ⟨a₀⟩ := ‹Nonempty A›
  obtain ⟨b₀⟩ := ‹Nonempty B›
  refine ⟨fun a => C a b₀, fun b => C a₀ b - C a₀ b₀, fun a b => ?_⟩
  have hr := h a a₀ b b₀
  rw [eq_sub_of_add_eq hr]
  abel_nf

/-! ## The `Bool`/`ℚ` development is an instance -/

open Integration.Marginalisation in
/-- The existing convex weighting, read as a function on `Bool`. -/
def ofWeights (w : Integration.Marginalisation.Weights) : Bool → ℚ :=
  fun b => if b then w.w₁ else w.w₀

open Integration.Marginalisation in
theorem ofWeights_sum (w : Integration.Marginalisation.Weights) :
    ∑ b, ofWeights w b = 1 := by
  simp [ofWeights, w.sum_one, add_comm]

open Integration.Marginalisation in
/-- **The identification.**  The `Bool`/`ℚ` marginal of `Integration.Marginalisation`
is this file's `marginal` at the corresponding weighting. -/
theorem marginalisation_marginal_is_instance (C : Bool → Bool → ℚ)
    (w : Integration.Marginalisation.Weights) (a : Bool) :
    Integration.Marginalisation.marginal C w a = marginal C (ofWeights w) a := by
  simp [Integration.Marginalisation.marginal, marginal, ofWeights, add_comm]

open Integration.Marginalisation in
/-- Hence its contrast is this file's contrast. -/
theorem marginalisation_contrast_is_instance (C : Bool → Bool → ℚ)
    (w : Integration.Marginalisation.Weights) :
    Integration.Marginalisation.contrast C w = contrast C (ofWeights w) true false := by
  simp [Integration.Marginalisation.contrast, contrast,
    marginalisation_marginal_is_instance]

open Integration.Marginalisation in
/-- And its invariance theorem is this file's, specialised: the corpus lane is
an instance of the owner, not a parallel result. -/
theorem marginalisation_invariance_is_instance {C : Bool → Bool → ℚ} (h : Separable C)
    (w v : Integration.Marginalisation.Weights) :
    Integration.Marginalisation.contrast C w = Integration.Marginalisation.contrast C v := by
  rw [marginalisation_contrast_is_instance, marginalisation_contrast_is_instance]
  exact separable_contrast_invariant h (ofWeights_sum w) (ofWeights_sum v) true false

/-! ## Three instances in three shapes -/

/-! ### A pooled reversal -/

/-- The two extreme weightings of a `Bool` second coordinate. -/
def atFalse : Bool → ℚ := fun b => if b then 0 else 1

/-- The other extreme weighting. -/
def atTrue : Bool → ℚ := fun b => if b then 1 else 0

theorem atFalse_sum : ∑ b, atFalse b = 1 := by simp [atFalse]

theorem atTrue_sum : ∑ b, atTrue b = 1 := by simp [atTrue]

/-- **Simpson shape.**  The parity consumer's first-coordinate contrast is `+1`
under one weighting of the second coordinate and `-1` under the other, so it
interacts. -/
theorem simpsonInstance :
    contrast Integration.Marginalisation.parityQ atFalse true false = 1 ∧
      contrast Integration.Marginalisation.parityQ atTrue true false = -1 ∧
      ¬ Separable Integration.Marginalisation.parityQ := by
  refine ⟨?_, ?_, ?_⟩
  · simp [contrast, marginal, atFalse, Integration.Marginalisation.parityQ]
  · simp [contrast, marginal, atTrue, Integration.Marginalisation.parityQ]
  · refine not_separable_of_contrast_reversal atFalse_sum atTrue_sum
      (a := true) (a' := false) ?_ ?_
    · simp [contrast, marginal, atFalse, Integration.Marginalisation.parityQ]
    · simp [contrast, marginal, atTrue, Integration.Marginalisation.parityQ]

/-! ### A trajectory whose ordering flips with the horizon -/

/-- Two trajectories on a two-point horizon: the first is ahead early, the
second is ahead late. -/
def trajectory (a : Bool) (b : Bool) : ℚ :=
  if a then (if b then 3 else 0) else (if b then 0 else 2)

/-- **Threshold/trajectory shape.**  Weighting the horizon towards the early
point makes the second trajectory ahead; weighting it towards the late point
reverses the comparison.  Hence "which trajectory is ahead" is not a property of
the trajectory pair alone: it interacts with the horizon. -/
theorem thresholdInstance :
    contrast trajectory atFalse true false = -2 ∧
      contrast trajectory atTrue true false = 3 ∧
      ¬ Separable trajectory := by
  refine ⟨?_, ?_, ?_⟩
  · simp [contrast, marginal, atFalse, trajectory]
  · simp [contrast, marginal, atTrue, trajectory]
  · refine not_separable_of_contrast_reversal atTrue_sum atFalse_sum
      (a := true) (a' := false) ?_ ?_
    · simp [contrast, marginal, atTrue, trajectory]
    · simp [contrast, marginal, atFalse, trajectory]

/-! ### A multiplicative interaction -/

/-- A product of two `Bool` coordinates, valued in `ℚ`. -/
def product (a b : Bool) : ℚ := if a && b then 1 else 0

/-- **Contextual/intersectional product shape.**  A product of indicators is not
a sum of coordinatewise effects: the contrast in the first coordinate is `1`
when the second is weighted onto `true` and `0` when it is weighted onto
`false`. -/
theorem productInstance :
    contrast product atTrue true false = 1 ∧
      contrast product atFalse true false = 0 ∧
      ¬ Separable product := by
  refine ⟨?_, ?_, ?_⟩
  · simp [contrast, marginal, atTrue, product]
  · simp [contrast, marginal, atFalse, product]
  · refine not_separable_of_contrast_ne atTrue_sum atFalse_sum (a := true) (a' := false) ?_
    simp [contrast, marginal, atTrue, atFalse, product]

/-- **One owner, three shapes.**  The three instances above are refuted by the
same theorem; only their weightings and carriers differ. -/
theorem three_shapes_one_owner :
    ¬ Separable Integration.Marginalisation.parityQ ∧ ¬ Separable trajectory ∧
      ¬ Separable product :=
  ⟨simpsonInstance.2.2, thresholdInstance.2.2, productInstance.2.2⟩

end Integration.SeparabilityContrast
