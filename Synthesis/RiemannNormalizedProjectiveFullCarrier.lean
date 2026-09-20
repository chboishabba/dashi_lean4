import Synthesis.RiemannProjectiveFullCompletedCancellation
import Synthesis.RiemannNormalizedProjectiveOffTsumAttachment
import Zeta23Bridge.LiteralWeilOffOrdinateReflectionSymmetrization

/-!
# Full normalized projective reflection-pair carrier

The off-ordinate attachment already proved

  D_off^proj = (1/(2t)) * sum'_{rho notin SameOrd(t)} A_rho^proj.

For the completed-density cancellation we also need the corresponding identity
on the full literal zero carrier.  Reflection is an involution on all zeros, so
the same no-representatives symmetrization applies without the ordinate
restriction:

  2 Re sum_rho Z_rho
    = (1/2) sum_rho [2 Re Z_rho + 2 Re Z_{R rho}]
    = (1/(2t)) sum_rho A_rho^proj.

This file proves that identity and the required summability.  It introduces no
new analytic estimate.
-/

noncomputable section

open MeasureTheory Complex Set
open scoped Real

namespace Synthesis

open Zeta23
open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilOffOrdinateReflectionPair
open Zeta23Bridge.LiteralWeilOffOrdinateReflectionSymmetrization

/-- Functional-equation reflection as an equivalence of the full literal zero
carrier. -/
def reflectZeroEquiv : Zeros ≃ Zeros where
  toFun := reflectZero
  invFun := reflectZero
  left_inv := reflectZero_involutive
  right_inv := reflectZero_involutive

/-- The doubled-real projective per-zero family is summable on the full carrier. -/
theorem projectiveZeroSummable_full
    {g : ℝ → ℝ}
    (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g)
    (t r : ℝ) :
    Summable fun rho : Zeros =>
      2 * reim
        (zeroTerm (sampleTest (projTaper g r) t 0) rho) := by
  have hpd : ContDiff ℝ 2 (projTaper g r) :=
    projTaper_contDiff hgs r
  have hpk : HasCompactSupport (projTaper g r) :=
    projTaper_hasCompactSupport hgc r
  have hsum :
      Summable fun rho : Zeros =>
        zeroTerm (sampleTest (projTaper g r) t 0) rho :=
    zeroTerm_summable
      (sampleTest_contDiff hpd t 0)
      (sampleTest_hasCompactSupport hpk t 0)
  have hre :
      Summable fun rho : Zeros =>
        reim (zeroTerm (sampleTest (projTaper g r) t 0) rho) := by
    have hR := (Complex.hasSum_re hsum.hasSum).summable
    have hI := (Complex.hasSum_im hsum.hasSum).summable
    exact hR.add hI
  simpa [mul_comm] using hre.mul_left 2

/-- Full-carrier reflection-pair projective defects are summable. -/
theorem literalPairProjectiveDefect_summable_full
    {g : ℝ → ℝ}
    (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u)
    (t r : ℝ) :
    Summable fun rho : Zeros =>
      literalPairProjectiveDefect g t r rho := by
  let f : Zeros → ℝ := fun rho =>
    2 * reim (zeroTerm (sampleTest (projTaper g r) t 0) rho)
  have hf : Summable f := projectiveZeroSummable_full hgs hgc t r
  have hfe : Summable (fun rho => f (reflectZeroEquiv rho)) := by
    exact reflectZeroEquiv.summable_iff.mpr hf
  have hp := hf.add hfe
  refine hp.congr ?_
  intro rho
  change
    f rho + f (reflectZero rho)
      = literalPairProjectiveDefect g t r rho
  exact
    (literalPairProjectiveDefect_eq_projectiveZero_add_reflect
      hgs hgc heven t r rho).symm

/-- Exact full-carrier symmetrization: the doubled-real literal zero pairing is
one half of the reflection-pair defect sum. -/
theorem projectiveFullZeroSignedPair_eq_half_literalPair_tsum
    {g : ℝ → ℝ}
    (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u)
    (t r : ℝ) :
    projectiveFullZeroSignedPair g t r
      =
    (1 / 2 : ℝ) *
      ∑' rho : Zeros,
        literalPairProjectiveDefect g t r rho := by
  let f : Zeros → ℝ := fun rho =>
    2 * reim (zeroTerm (sampleTest (projTaper g r) t 0) rho)
  have hf : Summable f := projectiveZeroSummable_full hgs hgc t r
  have hfe : Summable (fun rho => f (reflectZeroEquiv rho)) := by
    exact reflectZeroEquiv.summable_iff.mpr hf
  have hsym :=
    tsum_eq_half_tsum_add_equiv reflectZeroEquiv f hf hfe
  have hpair :
      (∑' rho : Zeros, f rho + f (reflectZeroEquiv rho))
        =
      ∑' rho : Zeros,
        literalPairProjectiveDefect g t r rho := by
    apply tsum_congr
    intro rho
    change
      f rho + f (reflectZero rho)
        = literalPairProjectiveDefect g t r rho
    exact
      (literalPairProjectiveDefect_eq_projectiveZero_add_reflect
        hgs hgc heven t r rho).symm
  unfold projectiveFullZeroSignedPair
  have hreim :
      2 * reim
        (∑' rho : Zeros,
          zeroTerm (sampleTest (projTaper g r) t 0) rho)
        =
      ∑' rho : Zeros, f rho := by
    have hsum :
        Summable fun rho : Zeros =>
          zeroTerm (sampleTest (projTaper g r) t 0) rho := by
      have hpd : ContDiff ℝ 2 (projTaper g r) :=
        projTaper_contDiff hgs r
      have hpk : HasCompactSupport (projTaper g r) :=
        projTaper_hasCompactSupport hgc r
      exact zeroTerm_summable
        (sampleTest_contDiff hpd t 0)
        (sampleTest_hasCompactSupport hpk t 0)
    have hR := Complex.tsum_re hsum
    have hI := Complex.tsum_im hsum
    unfold f reim
    rw [tsum_mul_left]
    rw [show
      (∑' rho : Zeros,
        ((zeroTerm (sampleTest (projTaper g r) t 0) rho).re
          + (zeroTerm (sampleTest (projTaper g r) t 0) rho).im))
      =
      (∑' rho : Zeros,
        (zeroTerm (sampleTest (projTaper g r) t 0) rho).re)
      +
      (∑' rho : Zeros,
        (zeroTerm (sampleTest (projTaper g r) t 0) rho).im) by
        rw [((Complex.hasSum_re hsum.hasSum).summable).tsum_add
          ((Complex.hasSum_im hsum.hasSum).summable)]]
    rw [← hR, ← hI]
    ring
  rw [hreim, hsym, hpair]

/-- The normalized projective atoms are summable on the full literal carrier. -/
theorem normalizedProjectiveOffZeroAtom_summable_full
    {t : ℝ} (ht : 18 ≤ t) :
    Summable fun rho : Zeros =>
      normalizedProjectiveOffZeroAtom t rho := by
  have ht0 : t ≠ 0 := by linarith
  have hp :
      Summable fun rho : Zeros =>
        literalPairProjectiveDefect
          (quantitativeCanonicalTaper t)
          t (quantitativeSampleRadius t) rho :=
    literalPairProjectiveDefect_summable_full
      (quantitativeCanonicalTaper_contDiff ht)
      (quantitativeCanonicalTaper_compact ht)
      quantitativeCanonicalTaper_even
      t (quantitativeSampleRadius t)
  have hscaled := hp.mul_left t
  refine hscaled.congr ?_
  intro rho
  rw [literalPairProjectiveDefect_eq_one_div_t_mul_normalizedAtom
    ht rho]
  field_simp [ht0]

/-- Full-carrier normalized same-object identity. -/
theorem canonical_projectiveFullZeroSignedPair_eq_normalizedProjectiveTsum
    {t : ℝ} (ht : 18 ≤ t) :
    projectiveFullZeroSignedPair
        (quantitativeCanonicalTaper t)
        t (quantitativeSampleRadius t)
      =
    (1 / (2 * t)) *
      ∑' rho : Zeros,
        normalizedProjectiveOffZeroAtom t rho := by
  have ht0 : t ≠ 0 := by linarith
  rw [projectiveFullZeroSignedPair_eq_half_literalPair_tsum
      (quantitativeCanonicalTaper_contDiff ht)
      (quantitativeCanonicalTaper_compact ht)
      quantitativeCanonicalTaper_even
      t (quantitativeSampleRadius t)]
  have hterm :
      (∑' rho : Zeros,
        literalPairProjectiveDefect
          (quantitativeCanonicalTaper t)
          t (quantitativeSampleRadius t) rho)
        =
      (1 / t) *
        ∑' rho : Zeros,
          normalizedProjectiveOffZeroAtom t rho := by
    calc
      (∑' rho : Zeros,
        literalPairProjectiveDefect
          (quantitativeCanonicalTaper t)
          t (quantitativeSampleRadius t) rho)
        =
      ∑' rho : Zeros,
        (1 / t) * normalizedProjectiveOffZeroAtom t rho := by
          apply tsum_congr
          intro rho
          exact
            literalPairProjectiveDefect_eq_one_div_t_mul_normalizedAtom
              ht rho
      _ =
      (1 / t) *
        ∑' rho : Zeros,
          normalizedProjectiveOffZeroAtom t rho := by
          rw [tsum_mul_left]
  rw [hterm]
  field_simp [ht0]
  ring

end Synthesis
