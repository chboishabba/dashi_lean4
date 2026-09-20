import Synthesis.RiemannNormalizedProjectiveBaseTransformVariation
import Synthesis.RiemannNormalizedRvMLeftDiscrepancy

/-!
# Abel bounds for the exact projective zeta-minus-mu base residual

The literal Zeta23 package already supplies cumulative actual-minus-mu
discrepancy prefixes.  The projective base transform now has its own exact
finite Abel variation compiler.  This file composes the two without routing
through the older one-radius centered observable.

These are still finite-grid Stieltjes bounds.  The remaining same-object
obligation is the continuum/atomic Stieltjes attachment identifying the actual
projective base pairing against dN-mu dt with the limit of these finite
increments.
-/

noncomputable section

open scoped BigOperators Real

namespace Synthesis

theorem normalizedProjectiveBaseTransform_neg
    (t q : ℝ) :
    normalizedProjectiveBaseTransform t (-q)
      =
    normalizedProjectiveBaseTransform t q := by
  rw [normalizedProjectiveBaseTransform_eq_physicalCosine,
      normalizedProjectiveBaseTransform_eq_physicalCosine]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun v => by
    rw [neg_mul, Real.cos_neg]

def normalizedProjectiveRightRvMResidualPair
    (t : ℝ) (q : ℕ -> ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    normalizedRightMuIncrement t q i
      * normalizedProjectiveBaseTransform t (q i)

def normalizedProjectiveLeftRvMResidualPair
    (t : ℝ) (p : ℕ -> ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    normalizedLeftMuIncrement t p i
      * normalizedProjectiveBaseTransform t (- p i)

theorem exists_normalizedProjectiveRightRvMResidualPair_bound :
    ∃ C T0 : ℝ, 0 <= C ∧
      ∀ (t Q : ℝ) (q : ℕ -> ℝ) (n : ℕ),
        max T0 18 <= t ->
        q 0 = 0 ->
        (∀ k, k <= n -> 0 <= q k) ->
        (∀ k, k <= n -> q k <= Q) ->
        (∀ i, i < n -> q i <= q (i + 1)) ->
        |normalizedProjectiveRightRvMResidualPair t q n|
          <=
        (C * (Real.log (t + 3)
          + Real.log (t * (1 + Q) + 4)))
          *
        (normalizedProjectiveProfileL1 t
          + normalizedProjectiveProfileFirstMoment t * Q) := by
  obtain ⟨C, T0, hC, hprefix⟩ :=
    exists_normalizedRightMuIncrement_prefix_bound
  refine ⟨C, T0, hC, ?_⟩
  intro t Q q n ht hq0 hqnonneg hqQ hmono
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
      (phi := fun i => normalizedProjectiveBaseTransform t (q i))
      (n := n) (B := B) hB hpref
  have hvar :=
    normalizedProjectiveBaseTransform_abelVariation_le
      (t := t) (Q := Q) q n hq0 hmono (hqQ n le_rfl)
  unfold normalizedProjectiveRightRvMResidualPair
  exact hab.trans
    (mul_le_mul_of_nonneg_left hvar hB)

theorem exists_normalizedProjectiveLeftRvMResidualPair_bound :
    ∃ C T0 : ℝ, 0 <= C ∧
      ∀ (t P : ℝ) (p : ℕ -> ℝ) (n : ℕ),
        18 <= t ->
        p 0 = 0 ->
        (∀ k, k <= n -> 0 <= p k) ->
        (∀ k, k <= n -> p k <= P) ->
        (∀ k, k <= n -> p k < 1) ->
        (∀ k, k <= n -> max T0 4 <= t * (1 - p k)) ->
        (∀ i, i < n -> p i <= p (i + 1)) ->
        |normalizedProjectiveLeftRvMResidualPair t p n|
          <=
        (C * (Real.log (t + 3) + Real.log (t + 4)))
          *
        (normalizedProjectiveProfileL1 t
          + normalizedProjectiveProfileFirstMoment t * P) := by
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
      (phi := fun i => normalizedProjectiveBaseTransform t (- p i))
      (n := n) (B := B) hB hpref
  have heven :
      (fun i => normalizedProjectiveBaseTransform t (- p i))
        =
      fun i => normalizedProjectiveBaseTransform t (p i) := by
    funext i
    exact normalizedProjectiveBaseTransform_neg t (p i)
  rw [heven] at hab
  have hvar :=
    normalizedProjectiveBaseTransform_abelVariation_le
      (t := t) (Q := P) p n hp0 hmono (hpP n le_rfl)
  unfold normalizedProjectiveLeftRvMResidualPair
  rw [heven]
  exact hab.trans
    (mul_le_mul_of_nonneg_left hvar hB)

end Synthesis
