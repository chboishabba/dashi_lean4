import Integration.CoordinateSufficiency

/-!
# Marginalisation, interaction, and reversal

`Integration.CoordinateSufficiency` separates *coordinate dependence* from
*interaction*: `sumPair` depends on both coordinates and decomposes additively,
`parityPair` depends on both and does not.  This file adds the layer above it,
which is where the corpus's statistical lanes actually operate: what happens to
a coordinate contrast when the other coordinate is **averaged out**.

The two results worth owning are complementary.

* If the consumer is separable, the contrast in one coordinate is the *same* for
  every convex weighting of the other (`separable_contrast_weight_invariant`).
  Marginalising loses nothing about that contrast.
* If it is not separable, the contrast can depend on the weighting so strongly
  that it **changes sign** (`interaction_contrast_can_reverse`).  So a reversal
  between two marginal analyses is a proof of interaction
  (`reversal_implies_interaction`), not a paradox.

The finite-count version of the same mechanism is the familiar reversal of a
pooled comparison, which the file exhibits with explicit integers
(`pooled_reversal`), together with the theorem that says exactly why it can
happen: the two groups are pooled with **different stratum weights**.  When the
weights agree, no reversal is possible (`common_weights_no_reversal`).

Nothing here is a claim about any study, dataset or population.  The carriers
are `Bool`, `Fin 2` and `ℚ`; no probability space, sampling model or estimator
appears, and none of these statements is about estimation error.  The
complementary deterministic statement — that no statistic of any sample size
reopens a distinction the observation map has already destroyed — is
`Integration.CoordinateSufficiency.no_sample_statistic_separates`.
-/

namespace Integration.Marginalisation

open Integration.CoordinateSufficiency

/-! ## Contrasts under a weighting -/

/-- A convex weighting of the two levels of the second coordinate. -/
structure Weights where
  /-- The weight of the `false` level. -/
  w₀ : ℚ
  /-- The weight of the `true` level. -/
  w₁ : ℚ
  /-- Weights are non-negative. -/
  nonneg₀ : 0 ≤ w₀
  /-- Weights are non-negative. -/
  nonneg₁ : 0 ≤ w₁
  /-- Weights sum to one. -/
  sum_one : w₀ + w₁ = 1

/-- The marginal of a two-coordinate consumer at a value of the first
coordinate, averaging the second coordinate against a weighting. -/
def marginal (C : Bool → Bool → ℚ) (w : Weights) (a : Bool) : ℚ :=
  w.w₀ * C a false + w.w₁ * C a true

/-- The marginal contrast between the two levels of the first coordinate. -/
def contrast (C : Bool → Bool → ℚ) (w : Weights) : ℚ :=
  marginal C w true - marginal C w false

/-- **A separable consumer has a weighting-independent contrast.**  Averaging
out the second coordinate loses nothing about the first-coordinate effect, no
matter how the average is taken. -/
theorem separable_contrast_weight_invariant {C : Bool → Bool → ℚ}
    (h : Separable C) (w v : Weights) : contrast C w = contrast C v := by
  obtain ⟨f, g, hfg⟩ := h
  have hw := w.sum_one
  have hv := v.sum_one
  simp only [contrast, marginal, hfg]
  linear_combination (f true - f false) * hw - (f true - f false) * hv

/-- The parity consumer, valued in `ℚ`. -/
def parityQ (a b : Bool) : ℚ := if a = b then 0 else 1

/-- The two extreme weightings. -/
def allFalse : Weights := ⟨1, 0, by norm_num, le_refl 0, by norm_num⟩

/-- The other extreme weighting. -/
def allTrue : Weights := ⟨0, 1, le_refl 0, by norm_num, by norm_num⟩

/-- **An interacting consumer can have its contrast reversed by the
weighting.**  Averaging the second coordinate one way makes the first-coordinate
effect positive; averaging it the other way makes it negative.  Nothing in
either marginal records that the other exists. -/
theorem interaction_contrast_can_reverse :
    contrast parityQ allFalse = 1 ∧ contrast parityQ allTrue = -1 := by
  constructor <;> simp [contrast, marginal, parityQ, allFalse, allTrue]

/-- **A reversal is a proof of interaction.**  If two convex weightings give
different contrasts, the consumer is not a sum of coordinatewise effects.  This
is the contrapositive of `separable_contrast_weight_invariant`, and it is the
whole content of a "paradoxical" reversal: it is evidence about the consumer,
not about the arithmetic. -/
theorem reversal_implies_interaction {C : Bool → Bool → ℚ} {w v : Weights}
    (h : contrast C w ≠ contrast C v) : ¬ Separable C :=
  fun hsep => h (separable_contrast_weight_invariant hsep w v)

/-- In particular the parity consumer is not separable, obtained here from the
reversal rather than from the rectangle identity. -/
theorem parityQ_not_separable : ¬ Separable parityQ :=
  reversal_implies_interaction (w := allFalse) (v := allTrue) (by
    rw [interaction_contrast_can_reverse.1, interaction_contrast_can_reverse.2]
    norm_num)

/-! ## The finite-count version -/

/-- A stratum: successes and totals in the two groups. -/
structure Stratum where
  /-- Successes in the first group. -/
  aHit : ℕ
  /-- Total in the first group. -/
  aTot : ℕ
  /-- Successes in the second group. -/
  bHit : ℕ
  /-- Total in the second group. -/
  bTot : ℕ
  deriving DecidableEq, Repr

/-- The first group's rate in a stratum. -/
def rateA (s : Stratum) : ℚ := (s.aHit : ℚ) / (s.aTot : ℚ)

/-- The second group's rate in a stratum. -/
def rateB (s : Stratum) : ℚ := (s.bHit : ℚ) / (s.bTot : ℚ)

/-- The pooled first-group rate over two strata. -/
def pooledA (s t : Stratum) : ℚ :=
  ((s.aHit + t.aHit : ℕ) : ℚ) / ((s.aTot + t.aTot : ℕ) : ℚ)

/-- The pooled second-group rate over two strata. -/
def pooledB (s t : Stratum) : ℚ :=
  ((s.bHit + t.bHit : ℕ) : ℚ) / ((s.bTot + t.bTot : ℕ) : ℚ)

/-- The first stratum of the witness. -/
def stratum₁ : Stratum := ⟨81, 87, 234, 270⟩

/-- The second stratum of the witness. -/
def stratum₂ : Stratum := ⟨192, 263, 55, 80⟩

/-- **Pooled reversal.**  The first group does better in each stratum
separately, and worse once the strata are pooled.  The totals are equal
(`350` each), so the reversal is not an artefact of unequal group sizes. -/
theorem pooled_reversal :
    rateB stratum₁ < rateA stratum₁ ∧ rateB stratum₂ < rateA stratum₂ ∧
      pooledA stratum₁ stratum₂ < pooledB stratum₁ stratum₂ := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [rateA, rateB, pooledA, pooledB, stratum₁, stratum₂] <;> norm_num

/-- **And the mechanism.**  The first group's pooled rate averages the stratum
rates with weights `87/350, 263/350`; the second group's averages them with
weights `270/350, 80/350`.  The two weightings are different, so the two pooled
numbers are contrasts of the *same* stratum rates taken against *different*
weightings — exactly the situation `interaction_contrast_can_reverse`
describes. -/
theorem pooling_weights_differ :
    ((stratum₁.aTot : ℚ) / ((stratum₁.aTot + stratum₂.aTot : ℕ) : ℚ))
      ≠ ((stratum₁.bTot : ℚ) / ((stratum₁.bTot + stratum₂.bTot : ℕ) : ℚ)) := by
  simp only [stratum₁, stratum₂]
  norm_num

/-- A weighted average of two values. -/
def avg (w : Weights) (v₀ v₁ : ℚ) : ℚ := w.w₀ * v₀ + w.w₁ * v₁

/-- **With a common weighting there is no reversal.**  If one group beats the
other in every stratum and the two pooled numbers use the same stratum weights,
the pooled comparison agrees with the stratum comparisons.  So a reversal is
always a statement about the weightings, never about the strata. -/
theorem common_weights_no_reversal (w : Weights) {u₀ u₁ v₀ v₁ : ℚ}
    (h₀ : u₀ < v₀) (h₁ : u₁ < v₁) : avg w u₀ u₁ < avg w v₀ v₁ := by
  have hw := w.sum_one
  have h0 := w.nonneg₀
  have h1 := w.nonneg₁
  simp only [avg]
  rcases lt_or_eq_of_le h0 with hp0 | hp0
  · nlinarith
  · have : w.w₁ = 1 := by rw [← hw, ← hp0]; ring
    rw [← hp0, this]
    nlinarith

end Integration.Marginalisation
