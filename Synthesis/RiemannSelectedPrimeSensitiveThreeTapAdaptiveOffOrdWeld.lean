import Synthesis.RiemannSelectedPrimeSensitiveThreeTapAdaptiveLocalDebt
import Zeta23Bridge.LiteralWeilOffOrdinateEvenConeReflectionSymmetrization

/-!
# Exact off-ordinate weld for the transformed adaptive carrier

The imported Zeta23 machinery already proves:
* the off-ordinate projective defect is a tsum of per-zero projective defects;
* reflection is an involution on the off-ordinate carrier;
* reflection pairing cancels the odd-height sinh/sin contribution.

This file combines those owners with the exact projective rescaling theorem.
No tail estimate and no RH sign hypothesis is introduced.
-/

noncomputable section
namespace Synthesis

open MeasureTheory Set Filter
open scoped Real BigOperators

open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilProjectiveTaper
open Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition
open Zeta23Bridge.LiteralWeilOffOrdinateProjectiveTail
open Zeta23Bridge.LiteralWeilOffOrdinateReflectionPair
open Zeta23Bridge.LiteralWeilOffOrdinateEvenConeReflectionSymmetrization

def genericProjectiveReflectionPairIntegral
    (g : ℝ → ℝ) (r a delta : ℝ) : ℝ :=
  ∫ u : ℝ,
    genericProjectivePhysicalProfile g r u
      * Real.cosh (a*u) * Real.cos (delta*u)

theorem reflectionPair_projTaper_eq_projectiveProfile
    (g : ℝ → ℝ) (r a delta u : ℝ) :
    reflectionPairWeight (projTaper g r) a delta u
      =
    genericProjectivePhysicalProfile g r u
      * Real.cosh (a*u) * Real.cos (delta*u) := by
  unfold reflectionPairWeight projTaper genericProjectivePhysicalProfile
  ring

theorem projectiveZeroPair_eq_reflectionPairIntegral
    {g : ℝ → ℝ}
    (hg : Continuous g)
    (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u)
    (t r : ℝ)
    (rho : Zeros) :
    2 * reim
          (Zeta23.EF.zeroTerm
            (Zeta23Bridge.LiteralWeilParityBalance.sampleTest
              (projTaper g r) t 0) rho)
      +
    2 * reim
          (Zeta23.EF.zeroTerm
            (Zeta23Bridge.LiteralWeilParityBalance.sampleTest
              (projTaper g r) t 0) (Zeta23.reflectZero rho))
      =
    ((Zeta23.zetaZeroConfig).mult rho : ℝ)
      * genericProjectiveReflectionPairIntegral
          g r (heightOf rho) ((rho : ℂ).im-t) := by
  have hpcont := projTaper_continuous hg r
  have hpcomp := projTaper_hasCompactSupport hgc r
  have hpeven := projTaper_even heven r
  have hpair :=
    zeroConeValue_add_reflect_eq_integral
      hpcont hpcomp hpeven t 0 rho
  unfold zeroConeValue at hpair
  simp only [neg_zero] at hpair
  rw [show
      (∫ u : ℝ,
        reflectionPairWeight (projTaper g r)
          (heightOf rho) ((rho : ℂ).im-t) u
          * Real.cos (0*u))
      =
      genericProjectiveReflectionPairIntegral
        g r (heightOf rho) ((rho : ℂ).im-t) by
      unfold genericProjectiveReflectionPairIntegral
      apply integral_congr_ae
      filter_upwards with u
      rw [reflectionPair_projTaper_eq_projectiveProfile]
      simp]
    at hpair
  simpa using hpair

theorem projectiveZeroTerm_summable
    {g : ℝ → ℝ}
    (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g)
    (t r : ℝ) :
    Summable
      (fun sigma : ((SameOrd t)ᶜ : Set Zeros) =>
        2 * reim
          (Zeta23.EF.zeroTerm
            (Zeta23Bridge.LiteralWeilParityBalance.sampleTest
              (projTaper g r) t 0) (sigma : Zeros))) := by
  have hp : ContDiff ℝ 2 (projTaper g r) :=
    projTaper_contDiff hgs r
  have hpk : HasCompactSupport (projTaper g r) :=
    projTaper_hasCompactSupport hgc r
  have hz :
      Summable
        (fun sigma : ((SameOrd t)ᶜ : Set Zeros) =>
          Zeta23.EF.zeroTerm
            (Zeta23Bridge.LiteralWeilParityBalance.sampleTest
              (projTaper g r) t 0) (sigma : Zeros)) :=
    (Zeta23.EF.zeroTerm_summable
      (Zeta23Bridge.LiteralWeilParityBalance.sampleTest_contDiff hp t 0)
      (Zeta23Bridge.LiteralWeilParityBalance.sampleTest_hasCompactSupport
        hpk t 0)).subtype _
  have hre := (Complex.hasSum_re hz.hasSum).summable
  have him := (Complex.hasSum_im hz.hasSum).summable
  exact (hre.add him).const_mul 2

theorem offOrdProjectiveDefect_eq_half_reflectionPair_tsum
    {g : ℝ → ℝ}
    (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u)
    (t r : ℝ) :
    Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.offOrdProjectiveDefect
        g t r
      =
    (1/2 : ℝ) *
      ∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
        ((Zeta23.zetaZeroConfig).mult (sigma : Zeros) : ℝ)
          * genericProjectiveReflectionPairIntegral
              g r
              (heightOf (sigma : Zeros))
              (((sigma : Zeros) : ℂ).im-t) := by
  let f : ((SameOrd t)ᶜ : Set Zeros) → ℝ :=
    fun sigma =>
      2 * reim
        (Zeta23.EF.zeroTerm
          (Zeta23Bridge.LiteralWeilParityBalance.sampleTest
            (projTaper g r) t 0) (sigma : Zeros))
  have hf : Summable f := by
    dsimp [f]
    exact projectiveZeroTerm_summable hgs hgc t r
  have hoff :=
    Zeta23Bridge.LiteralWeilOffOrdinateProjectiveTail.offOrdProjectiveDefect_eq_tsum
      hgs hgc heven t r
  rw [hoff]
  have hsym :=
    tsum_eq_half_tsum_add_equiv (reflectOffOrdEquiv t) f hf
  rw [hsym]
  congr 1
  apply tsum_congr
  intro sigma
  dsimp [f, reflectOffOrdEquiv]
  simpa using
    projectiveZeroPair_eq_reflectionPairIntegral
      hgs.continuous hgc heven t r (sigma : Zeros)

theorem genericProjectiveReflectionPairIntegral_rescale
    {G : ℝ → ℝ} {r : ℝ}
    (hr : 0 < r)
    (a delta : ℝ) :
    genericProjectiveReflectionPairIntegral
        (projectiveRescaleProfile G r) r a delta
      =
    (1/r^2) *
      ∫ v : ℝ,
        genericProjectivePhysicalProfile G 1 v
          * Real.cosh ((a/r)*v)
          * Real.cos ((delta/r)*v) := by
  let F : ℝ → ℝ := fun v =>
    genericProjectivePhysicalProfile G 1 v
      * Real.cosh ((a/r)*v)
      * Real.cos ((delta/r)*v)
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hpoint :
      (fun u : ℝ =>
        genericProjectivePhysicalProfile
            (projectiveRescaleProfile G r) r u
          * Real.cosh (a*u) * Real.cos (delta*u))
      =
      fun u => (1/r) * F (r*u) := by
    funext u
    rw [genericProjectivePhysicalProfile_rescale hr u]
    dsimp [F]
    have ha : (a/r)*(r*u) = a*u := by field_simp [hr0]
    have hd : (delta/r)*(r*u) = delta*u := by field_simp [hr0]
    rw [ha,hd]
    ring
  unfold genericProjectiveReflectionPairIntegral
  rw [hpoint, integral_const_mul]
  rw [integral_rescale_mul hr]
  field_simp [hr0]
  ring

def QuarticFourSignedPolePair.threeTapEndpointPairTermHalf
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps : ℝ) (rho : Zeros) : ℝ :=
  ((Zeta23.zetaZeroConfig).mult rho : ℝ) / (t/16)^2
    *
  ∫ v : ℝ,
    W.threeTapNormalizedProjectiveHalf eps v
      * Real.cosh ((heightOf rho/(t/16))*v)
      * Real.cos ((((rho : ℂ).im-t)/(t/16))*v)

def QuarticFourSignedPolePair.threeTapEndpointPairTermTwo
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps : ℝ) (rho : Zeros) : ℝ :=
  ((Zeta23.zetaZeroConfig).mult rho : ℝ) / (t/16)^2
    *
  ∫ v : ℝ,
    W.threeTapNormalizedProjectiveTwo eps v
      * Real.cosh ((heightOf rho/(t/16))*v)
      * Real.cos ((((rho : ℂ).im-t)/(t/16))*v)

theorem QuarticFourSignedPolePair.threeTapAdaptivePairTerm_eq_endpoints
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros) :
    W.threeTapAdaptivePairTerm eps rho
      =
    W.poleTwo * W.threeTapEndpointPairTermHalf eps rho
      - W.poleHalf * W.threeTapEndpointPairTermTwo eps rho := by
  unfold QuarticFourSignedPolePair.threeTapAdaptivePairTerm
    QuarticFourSignedPolePair.threeTapNormalizedPairKernel
    QuarticFourSignedPolePair.threeTapEndpointPairTermHalf
    QuarticFourSignedPolePair.threeTapEndpointPairTermTwo
    QuarticFourSignedPolePair.threeTapNormalizedSignedProjectiveProfile
    quarticSignedPoleNormalizedOrdinateOffset
  let f1 : ℝ → ℝ := fun v =>
    W.threeTapNormalizedProjectiveHalf eps v
      * Real.cosh ((heightOf rho/(t/16))*v)
      * Real.cos ((((rho : ℂ).im-t)/(t/16))*v)
  let f2 : ℝ → ℝ := fun v =>
    W.threeTapNormalizedProjectiveTwo eps v
      * Real.cosh ((heightOf rho/(t/16))*v)
      * Real.cos ((((rho : ℂ).im-t)/(t/16))*v)
  have h1 : Integrable f1 := by
    dsimp [f1]
    exact Continuous.integrable_of_hasCompactSupport
      (by fun_prop)
      ((genericProjectivePhysicalProfile_compact
        (detectorThreeTap_compact
          (quarticFourWindowProfile_compact W.Rpos) eps _) 1).mul_right).mul_right
  have h2 : Integrable f2 := by
    dsimp [f2]
    exact Continuous.integrable_of_hasCompactSupport
      (by fun_prop)
      ((genericProjectivePhysicalProfile_compact
        (detectorThreeTap_compact
          (quarticFourWindowProfile_compact W.Rpos) eps _) 1).mul_right).mul_right
  rw [show
      (fun v : ℝ =>
        (W.poleTwo * W.threeTapNormalizedProjectiveHalf eps v
          + (-W.poleHalf) * W.threeTapNormalizedProjectiveTwo eps v)
          * Real.cosh ((heightOf rho/(t/16))*v)
          * Real.cos ((((rho : ℂ).im-t)/(t/16))*v))
      =
      fun v => W.poleTwo * f1 v + (-W.poleHalf) * f2 v by
      funext v
      dsimp [f1,f2]
      ring,
      integral_add (h1.const_mul _) (h2.const_mul _),
      integral_const_mul, integral_const_mul]
  ring

theorem QuarticFourSignedPolePair.threeTap_endpoint_offOrdHalf_eq_tsum
    {t eps : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t) :
    Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.offOrdProjectiveDefect
        (W.threeTapHalf eps) t (t/16)
      =
    (1/2 : ℝ) *
      ∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
        W.threeTapEndpointPairTermHalf eps (sigma : Zeros) := by
  have hr : 0 < t/16 := by linarith
  have hbase :=
    offOrdProjectiveDefect_eq_half_reflectionPair_tsum
      (detectorThreeTap_contDiff
        (quarticFourPhysicalDetector_contDiff W.Rpos) eps (Real.log 2))
      (detectorThreeTap_compact
        (quarticFourPhysicalDetector_compact W.Rpos (by linarith : 0 < t))
        eps (Real.log 2))
      (detectorThreeTap_even
        (quarticFourPhysicalDetector_even W.R (1/2) W.muHalf t)
        eps (Real.log 2))
      t (t/16)
  rw [hbase]
  congr 1
  apply tsum_congr
  intro sigma
  rw [W.threeTapHalf_eq_rescaled_normalized]
  rw [genericProjectiveReflectionPairIntegral_rescale hr]
  unfold QuarticFourSignedPolePair.threeTapEndpointPairTermHalf
    QuarticFourSignedPolePair.threeTapNormalizedProjectiveHalf
  ring

theorem QuarticFourSignedPolePair.threeTap_endpoint_offOrdTwo_eq_tsum
    {t eps : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t) :
    Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.offOrdProjectiveDefect
        (W.threeTapTwo eps) t (t/16)
      =
    (1/2 : ℝ) *
      ∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
        W.threeTapEndpointPairTermTwo eps (sigma : Zeros) := by
  have hr : 0 < t/16 := by linarith
  have hbase :=
    offOrdProjectiveDefect_eq_half_reflectionPair_tsum
      (detectorThreeTap_contDiff
        (quarticFourPhysicalDetector_contDiff W.Rpos) eps (Real.log 2))
      (detectorThreeTap_compact
        (quarticFourPhysicalDetector_compact W.Rpos (by linarith : 0 < t))
        eps (Real.log 2))
      (detectorThreeTap_even
        (quarticFourPhysicalDetector_even W.R (2/3) W.muTwo t)
        eps (Real.log 2))
      t (t/16)
  rw [hbase]
  congr 1
  apply tsum_congr
  intro sigma
  rw [W.threeTapTwo_eq_rescaled_normalized]
  rw [genericProjectiveReflectionPairIntegral_rescale hr]
  unfold QuarticFourSignedPolePair.threeTapEndpointPairTermTwo
    QuarticFourSignedPolePair.threeTapNormalizedProjectiveTwo
  ring

/-- Exact same-object transformed off-ordinate carrier weld, in endpoint form.
This removes the semantic placeholder left by AdaptiveLocalDebt. -/
theorem QuarticFourSignedPolePair.threeTap_offOrd_eq_endpoint_pair_tsums
    {t eps : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t) :
    W.threeTapChannelCombination eps
      Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.offOrdProjectiveDefect
      =
    (1/2 : ℝ) *
      (
        W.poleTwo *
          (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
            W.threeTapEndpointPairTermHalf eps (sigma : Zeros))
        -
        W.poleHalf *
          (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
            W.threeTapEndpointPairTermTwo eps (sigma : Zeros))
      ) := by
  unfold QuarticFourSignedPolePair.threeTapChannelCombination
  rw [W.threeTap_endpoint_offOrdHalf_eq_tsum ht,
      W.threeTap_endpoint_offOrdTwo_eq_tsum ht]
  ring

end Synthesis
