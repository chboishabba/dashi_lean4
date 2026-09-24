import Synthesis.RiemannNormalizedProjectiveFullCarrier
import Synthesis.RiemannNormalizedProjectiveBaseZeroAtSameOrd
import Synthesis.RiemannNormalizedProjectiveHorizontalQuadraticFactor
import Zeta23Bridge.LiteralWeilClusterTwoRadiusProfile

/-!
# Same-ordinate normalized projective atoms are exactly the negative height defect

The completed full-carrier cancellation becomes informative only after auditing
what is removed when the off-ordinate carrier is selected.

For rho with Im rho = t, the literal projective reflection-pair channel has the
opposite determinant orientation to the positive cluster height detector.  The
exact pointwise identity is

  A_rho^proj = - 2 t * zeroHeightDefect(g_t,r_t,rho).

At the same time q_rho = 0 and the projective base transform vanishes exactly,
so the same normalized atom is purely the horizontal-square contribution.

Summing over the literal same-ordinate fibre gives

  sum'_{Im rho=t} A_rho^proj = -2 t * D_cluster.

This is an accounting firewall: using the full explicit formula to cancel the
completed smooth density and then subtracting the off-ordinate carrier recovers
the positive cluster identically.  A prize-facing contradiction must therefore
obtain a strict signed estimate before that tautological full-carrier
replacement.
-/

noncomputable section

open MeasureTheory Complex Set
open scoped Real

namespace Synthesis

open Zeta23
open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilClusterTwoRadiusProfile
open Zeta23Bridge.LiteralWeilOffOrdinateReflectionPair
open Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition

/-- Even response is even in horizontal height. -/
theorem evenResp_height_neg
    (g : ℝ → ℝ) (a s : ℝ) :
    evenResp g (-a) s = evenResp g a s := by
  unfold evenResp
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun u => by
    rw [show (-a) * u = -(a*u) by ring, Real.cosh_neg]

/-- Reflection preserves the cone weight at a fixed sampling radius. -/
theorem coneWeight_reflectZero
    (g : ℝ → ℝ) (s : ℝ) (rho : Zeros) :
    coneWeight g s (reflectZero rho) = coneWeight g s rho := by
  unfold coneWeight
  rw [reflectZero_mult, heightOf_reflectZero, evenResp_height_neg]

/-- On the target ordinate the two-sample cone value of one literal zero is
exactly its positive cone weight. -/
theorem zeroConeValue_eq_coneWeight_of_sameOrd
    {g : ℝ → ℝ}
    (hg : Continuous g)
    (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u)
    {t : ℝ} {rho : Zeros}
    (him : (rho : ℂ).im = t)
    (s : ℝ) :
    zeroConeValue g t s rho = coneWeight g s rho := by
  unfold zeroConeValue
  exact reim_zeroTerm_cone hg hgc heven him s

/-- The reflection partner remains on the same target ordinate. -/
theorem reflectZero_sameOrd
    {t : ℝ} {rho : Zeros}
    (him : (rho : ℂ).im = t) :
    ((reflectZero rho : Zeros) : ℂ).im = t := by
  rw [im_reflectZero, him]

/-- Pointwise sign audit: on the same-ordinate fibre the literal reflection-pair
projective defect is minus twice the positive per-zero height defect. -/
theorem literalPairProjectiveDefect_sameOrd_eq_neg_two_zeroHeightDefect
    {g : ℝ → ℝ}
    (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u)
    {t : ℝ} {rho : Zeros}
    (him : (rho : ℂ).im = t)
    (r : ℝ) :
    literalPairProjectiveDefect g t r rho
      = -2 * zeroHeightDefect g r rho := by
  have h1 :=
    zeroConeValue_eq_coneWeight_of_sameOrd
      hgs.continuous hgc heven him r
  have h2 :=
    zeroConeValue_eq_coneWeight_of_sameOrd
      hgs.continuous hgc heven him (2*r)
  have himR := reflectZero_sameOrd him
  have h1R :=
    zeroConeValue_eq_coneWeight_of_sameOrd
      hgs.continuous hgc heven himR r
  have h2R :=
    zeroConeValue_eq_coneWeight_of_sameOrd
      hgs.continuous hgc heven himR (2*r)
  have href1 := coneWeight_reflectZero g r rho
  have href2 := coneWeight_reflectZero g (2*r) rho
  have hz := coneWeight_mul_sub (g := g) r rho
  unfold literalPairProjectiveDefect literalPairRadiusChannel
    channelProjectiveDefect
  rw [h1, h2, h1R, h2R, href1, href2]
  linarith

/-- Canonical normalized atom on the same-ordinate fibre:
A_rho^proj = -2 t D_rho. -/
theorem normalizedProjectiveOffZeroAtom_sameOrd_eq_neg_two_t_mul_heightDefect
    {t : ℝ} (ht : 18 ≤ t)
    {rho : Zeros}
    (him : (rho : ℂ).im = t) :
    normalizedProjectiveOffZeroAtom t rho
      =
    -2 * t *
      zeroHeightDefect
        (quantitativeCanonicalTaper t)
        (quantitativeSampleRadius t)
        rho := by
  have ht0 : t ≠ 0 := by linarith
  have hpair :=
    literalPairProjectiveDefect_sameOrd_eq_neg_two_zeroHeightDefect
      (quantitativeCanonicalTaper_contDiff ht)
      (quantitativeCanonicalTaper_compact ht)
      quantitativeCanonicalTaper_even
      him
      (quantitativeSampleRadius t)
  have hnorm :=
    literalPairProjectiveDefect_eq_one_div_t_mul_normalizedAtom
      ht rho
  rw [hpair] at hnorm
  field_simp [ht0] at hnorm
  linarith

/-- Same-ordinate normalized gap is exactly zero. -/
theorem normalizedGap_eq_zero_of_sameOrd
    {t : ℝ} (ht : t ≠ 0)
    {rho : Zeros}
    (him : (rho : ℂ).im = t) :
    normalizedGap t rho = 0 := by
  unfold normalizedGap
  rw [him]
  field_simp [ht]

/-- The same-ordinate projective atom has no q-only base component; it is exactly
the already-factorized horizontal-square term. -/
theorem normalizedProjectiveOffZeroAtom_sameOrd_eq_heightSq_horizontal
    {t : ℝ} (ht18 : 18 ≤ t)
    {rho : Zeros}
    (him : (rho : ℂ).im = t) :
    normalizedProjectiveOffZeroAtom t rho
      =
    ((zetaZeroConfig).mult (rho : ℂ) : ℝ)
      * ((heightOf rho) ^ 2 / t ^ 2)
      * normalizedProjectiveHorizontalQuadratic t
          (normalizedHorizontalHeight t rho) 0 := by
  have ht0 : t ≠ 0 := by linarith
  rw [normalizedProjectiveOffZeroAtom_eq_base_add_heightSq_horizontal
      ht0 rho]
  have hq := normalizedGap_eq_zero_of_sameOrd ht0 him
  rw [hq, normalizedProjectiveBaseTransform_zero (by linarith : 0 < t)]
  ring

/-- Same-ordinate normalized atoms are summable, by restriction of the full
carrier summability theorem. -/
theorem normalizedProjectiveOffZeroAtom_summable_sameOrd
    {t : ℝ} (ht : 18 ≤ t) :
    Summable fun rho : SameOrd t =>
      normalizedProjectiveOffZeroAtom t (rho : Zeros) :=
  (normalizedProjectiveOffZeroAtom_summable_full ht).subtype _

/-- Exact summed sign identity:
the same-ordinate normalized projective carrier is -2t times the positive
literal cluster height defect. -/
theorem tsum_sameOrd_normalizedProjectiveOffZeroAtom_eq_neg_two_t_cluster
    {t : ℝ} (ht : 18 ≤ t) :
    (∑' rho : SameOrd t,
      normalizedProjectiveOffZeroAtom t (rho : Zeros))
      =
    -2 * t *
      clusterHeightDefect
        (quantitativeCanonicalTaper t)
        t (quantitativeSampleRadius t) := by
  have hatom :=
    normalizedProjectiveOffZeroAtom_summable_sameOrd ht
  have hdef :=
    summable_zeroHeightDefect
      (quantitativeCanonicalTaper_contDiff ht)
      (quantitativeCanonicalTaper_compact ht)
      quantitativeCanonicalTaper_even
      t (quantitativeSampleRadius t)
  calc
    (∑' rho : SameOrd t,
      normalizedProjectiveOffZeroAtom t (rho : Zeros))
      =
    ∑' rho : SameOrd t,
      (-2 * t) *
        zeroHeightDefect
          (quantitativeCanonicalTaper t)
          (quantitativeSampleRadius t)
          (rho : Zeros) := by
      apply tsum_congr
      intro rho
      have him : (((rho : SameOrd t) : Zeros) : ℂ).im = t := rho.property
      simpa [mul_assoc] using
        normalizedProjectiveOffZeroAtom_sameOrd_eq_neg_two_t_mul_heightDefect
          ht him
    _ =
    (-2 * t) *
      ∑' rho : SameOrd t,
        zeroHeightDefect
          (quantitativeCanonicalTaper t)
          (quantitativeSampleRadius t)
          (rho : Zeros) := by
      rw [tsum_mul_left]
    _ =
    -2 * t *
      clusterHeightDefect
        (quantitativeCanonicalTaper t)
        t (quantitativeSampleRadius t) := by
      rw [clusterHeightDefect_eq_tsum
        (quantitativeCanonicalTaper_contDiff ht)
        (quantitativeCanonicalTaper_compact ht)
        quantitativeCanonicalTaper_even
        t (quantitativeSampleRadius t)]

end Synthesis
