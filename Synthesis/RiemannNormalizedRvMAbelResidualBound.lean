import Synthesis.RiemannNormalizedBaseTransformVariation
import Synthesis.RiemannNormalizedRvMLeftDiscrepancy

/-!
# Abel bounds for the exact zeta-minus-mu normalized residual

The preceding files now provide both ingredients on the literal carrier:

1. cumulative actual-minus-mu RvM discrepancy prefixes of size O(log t);
2. a t-uniform finite Abel variation bound for the exact normalized base
   transform Phi_t on bounded q-grids.

This file composes them.

For the right side q >= 0 and the high positive left side q=-p, the weighted
discrete residual is bounded by

  B_RvM(t,Q) * (PhiAbsUpper + PhiLipUpper * Q),

independently of the number of grid points.

The literal centered-Off normalization contributes the separate external 1/t,
so these O(log t) pre-normalized bounds are the exact shape needed for an
O(log t / t) high residual after the final same-object finite-grid attachment.
-/

noncomputable section

open scoped BigOperators Real

namespace Synthesis

theorem normalizedCenteredBaseTransform_neg
    (t q : ℝ) :
    normalizedCenteredBaseTransform t (-q)
      =
    normalizedCenteredBaseTransform t q := by
  unfold normalizedCenteredBaseTransform
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun v => by
    rw [neg_mul, Real.cos_neg]

/-- Right-side actual-minus-mu Abel pair. -/
def normalizedRightRvMResidualPair
    (t : ℝ) (q : ℕ -> ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    normalizedRightMuIncrement t q i
      * normalizedCenteredBaseTransform t (q i)

/-- Left-side actual-minus-mu Abel pair, evaluated at the literal q=-p gap. -/
def normalizedLeftRvMResidualPair
    (t : ℝ) (p : ℕ -> ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    normalizedLeftMuIncrement t p i
      * normalizedCenteredBaseTransform t (- p i)

theorem exists_normalizedRightRvMResidualPair_bound :
    ∃ C T0 : ℝ, 0 <= C ∧
      ∀ (t Q : ℝ) (q : ℕ -> ℝ) (n : ℕ),
        max T0 18 <= t ->
        q 0 = 0 ->
        (∀ k, k <= n -> 0 <= q k) ->
        (∀ k, k <= n -> q k <= Q) ->
        (∀ i, i < n -> q i <= q (i + 1)) ->
        |normalizedRightRvMResidualPair t q n|
          <=
        (C * (Real.log (t + 3)
          + Real.log (t * (1 + Q) + 4)))
          *
        (normalizedBaseTransformAbsUpper
          + normalizedBaseTransformLipschitzUpper * Q) := by
  obtain ⟨C, T0, hC, hprefix⟩ :=
    exists_normalizedRightMuIncrement_prefix_bound
  refine ⟨C, T0, hC, ?_⟩
  intro t Q q n ht hq0 hqnonneg hqQ hmono
  have ht18 : 18 <= t := (le_max_right T0 18).trans ht
  have ht4 : max T0 4 <= t := by
    apply max_le
    · exact (le_max_left T0 18).trans ht
    · linarith
  have hQ0 : 0 <= Q := le_trans (hqnonneg n le_rfl) (hqQ n le_rfl)
  let B : ℝ :=
    C * (Real.log (t + 3)
      + Real.log (t * (1 + Q) + 4))
  have hlogt : 0 <= Real.log (t + 3) :=
    Real.log_nonneg (by linarith)
  have hlogQ : 0 <= Real.log (t * (1 + Q) + 4) := by
    apply Real.log_nonneg
    nlinarith
  have hB : 0 <= B := by
    dsimp [B]
    positivity
  have hpref : ∀ k, k <= n ->
      |abelPrefix (normalizedRightMuIncrement t q) k| <= B := by
    intro k hk
    have hkraw :=
      hprefix t q n ht4 hq0 hqnonneg k hk
    have hargpos : 0 < t * (1 + q k) + 4 := by
      have hqk := hqnonneg k hk
      nlinarith
    have hargle :
        t * (1 + q k) + 4
          <= t * (1 + Q) + 4 := by
      have hqkQ := hqQ k hk
      nlinarith
    have hlogle :
        Real.log (t * (1 + q k) + 4)
          <= Real.log (t * (1 + Q) + 4) :=
      Real.log_le_log hargpos hargle
    exact hkraw.trans (by
      dsimp [B]
      have := mul_le_mul_of_nonneg_left
        (add_le_add_left hlogle (Real.log (t + 3))) hC
      simpa [add_assoc] using this)
  have hab :=
    abs_weighted_sum_le_prefix_bound_mul_variation
      (w := normalizedRightMuIncrement t q)
      (phi := fun i => normalizedCenteredBaseTransform t (q i))
      (n := n) (B := B) hB hpref
  have hvar :=
    normalizedBaseTransform_abelVariation_le
      (t := t) (Q := Q) ht18 q n hq0 hmono (hqQ n le_rfl)
  unfold normalizedRightRvMResidualPair
  exact hab.trans
    (mul_le_mul_of_nonneg_left hvar hB)

theorem exists_normalizedLeftRvMResidualPair_bound :
    ∃ C T0 : ℝ, 0 <= C ∧
      ∀ (t P : ℝ) (p : ℕ -> ℝ) (n : ℕ),
        18 <= t ->
        p 0 = 0 ->
        (∀ k, k <= n -> 0 <= p k) ->
        (∀ k, k <= n -> p k <= P) ->
        (∀ k, k <= n -> p k < 1) ->
        (∀ k, k <= n -> max T0 4 <= t * (1 - p k)) ->
        (∀ i, i < n -> p i <= p (i + 1)) ->
        |normalizedLeftRvMResidualPair t p n|
          <=
        (C * (Real.log (t + 3) + Real.log (t + 4)))
          *
        (normalizedBaseTransformAbsUpper
          + normalizedBaseTransformLipschitzUpper * P) := by
  obtain ⟨C, T0, hC, hprefix⟩ :=
    exists_normalizedLeftMuIncrement_prefix_bound
  refine ⟨C, T0, hC, ?_⟩
  intro t P p n ht hp0 hpnonneg hpP hpone hhigh hmono
  have hP0 : 0 <= P := le_trans (hpnonneg n le_rfl) (hpP n le_rfl)
  let B : ℝ :=
    C * (Real.log (t + 3) + Real.log (t + 4))
  have ht0 : 0 < t := by linarith
  have hlog1 : 0 <= Real.log (t + 3) :=
    Real.log_nonneg (by linarith)
  have hlog2 : 0 <= Real.log (t + 4) :=
    Real.log_nonneg (by linarith)
  have hB : 0 <= B := by
    dsimp [B]
    positivity
  have hpref : ∀ k, k <= n ->
      |abelPrefix (normalizedLeftMuIncrement t p) k| <= B := by
    intro k hk
    have hkraw :=
      hprefix t p n hp0 hpnonneg hpone hhigh k hk
    have hpk := hpnonneg k hk
    have hleftpos : 0 < t * (1 - p k) + 3 := by
      have hh := hhigh k hk
      linarith
    have hleftle :
        t * (1 - p k) + 3 <= t + 3 := by
      nlinarith
    have hlogle :
        Real.log (t * (1 - p k) + 3)
          <= Real.log (t + 3) :=
      Real.log_le_log hleftpos hleftle
    exact hkraw.trans (by
      dsimp [B]
      have := mul_le_mul_of_nonneg_left
        (add_le_add_right hlogle (Real.log (t + 4))) hC
      simpa [add_comm, add_left_comm, add_assoc] using this)
  have hab :=
    abs_weighted_sum_le_prefix_bound_mul_variation
      (w := normalizedLeftMuIncrement t p)
      (phi := fun i => normalizedCenteredBaseTransform t (p i))
      (n := n) (B := B) hB hpref
  have hvar :=
    normalizedBaseTransform_abelVariation_le
      (t := t) (Q := P) ht p n hp0 hmono (hpP n le_rfl)
  have heq :
      normalizedLeftRvMResidualPair t p n
        =
      ∑ i ∈ Finset.range (n + 1),
        normalizedLeftMuIncrement t p i
          * normalizedCenteredBaseTransform t (p i) := by
    unfold normalizedLeftRvMResidualPair
    apply Finset.sum_congr rfl
    intro i hi
    rw [normalizedCenteredBaseTransform_neg]
  rw [heq]
  exact hab.trans
    (mul_le_mul_of_nonneg_left hvar hB)

end Synthesis
