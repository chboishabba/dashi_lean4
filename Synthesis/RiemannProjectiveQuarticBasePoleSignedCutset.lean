import Synthesis.RiemannProjectiveQuarticBasePoleOrthogonalization
import Synthesis.RiemannProjectiveQuarticCompletedResidual
import Synthesis.RiemannCanonicalTargetPairResidual
import Synthesis.RiemannProjectiveQuarticTargetLocalSign

/-!
# Signed base+pole orthogonalized quartic cutset

The positive-cone hypothesis is unnecessary once the signed combination is
treated as one projective physical profile.

For three quartic witnesses, the cross-product coefficients cancel exactly

  sum c_i B_i = 0,   sum c_i P_i = 0,

where B_i is the complete base+Gamma scalar and P_i the literal projective pole
scalar.  The normalized profile combination has zeroth and second moments zero
and fourth moment

  4 * Det(B,P,J4).

If this determinant is nonzero, orient the entire combination so that its
fourth moment is negative.  The generic fourth-order hyperbolic sign theorem
then gives a positive punctured height band for the *combined* observable.

After physical rescaling, once 8/t lies in that band, every same-ordinate zero
has nonnegative combined defect and every off-line one has strictly positive
combined defect.  Thus the reflection target pair again gives

  2 D_comb(rho) <= Cluster_comb,

even though the individual coefficients may have arbitrary signs.

The exact base+Gamma and pole cancellations leave only the signed horizontal
carrier.  Therefore a strict horizontal upper below the doubled combined target
is contradictory, with no positive-cone assumption.
-/

noncomputable section

open MeasureTheory Complex Set
open scoped Real

namespace Synthesis

open Zeta23
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilClusterTwoRadiusProfile
open Zeta23Bridge.LiteralWeilOffOrdinateReflectionPair
open Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector

def quarticBasePoleOrientation
    (W1 W2 W3 : QuarticHighWitness) (t : ℝ) : ℝ :=
  if quarticBasePoleTargetDet W1 W2 W3 t < 0 then 1 else -1

def orientedQuarticBasePoleOrthogonalProfile
    (W1 W2 W3 : QuarticHighWitness) (t : ℝ) : ℝ -> ℝ :=
  fun u =>
    quarticBasePoleOrientation W1 W2 W3 t *
      quarticBasePoleOrthogonalProfile W1 W2 W3 t u

theorem orientedQuarticBasePoleOrthogonalProfile_continuous
    (W1 W2 W3 : QuarticHighWitness) (t : ℝ) :
    Continuous (orientedQuarticBasePoleOrthogonalProfile W1 W2 W3 t) := by
  unfold orientedQuarticBasePoleOrthogonalProfile
  fun_prop

theorem orientedQuarticBasePoleOrthogonalProfile_compact
    (W1 W2 W3 : QuarticHighWitness) (t : ℝ) :
    HasCompactSupport
      (orientedQuarticBasePoleOrthogonalProfile W1 W2 W3 t) := by
  unfold orientedQuarticBasePoleOrthogonalProfile
  exact (quarticBasePoleOrthogonalProfile_compact W1 W2 W3 t).mul_left

theorem orientedQuarticBasePoleOrthogonalProfile_zeroth_zero
    (W1 W2 W3 : QuarticHighWitness) (t : ℝ) :
    profileZerothMoment
      (orientedQuarticBasePoleOrthogonalProfile W1 W2 W3 t) = 0 := by
  unfold orientedQuarticBasePoleOrthogonalProfile profileZerothMoment
  rw [integral_const_mul,
      quarticBasePoleOrthogonalProfile_zeroth_zero]
  ring

theorem orientedQuarticBasePoleOrthogonalProfile_second_zero
    (W1 W2 W3 : QuarticHighWitness) (t : ℝ) :
    profileSecondMoment
      (orientedQuarticBasePoleOrthogonalProfile W1 W2 W3 t) = 0 := by
  unfold orientedQuarticBasePoleOrthogonalProfile profileSecondMoment
  have hpoint :
      (fun u : ℝ =>
        quarticBasePoleOrientation W1 W2 W3 t *
          quarticBasePoleOrthogonalProfile W1 W2 W3 t u * u^2)
        =
      fun u =>
        quarticBasePoleOrientation W1 W2 W3 t *
          (quarticBasePoleOrthogonalProfile W1 W2 W3 t u * u^2) := by
    funext u
    ring
  rw [hpoint, integral_const_mul,
      quarticBasePoleOrthogonalProfile_second_zero]
  ring

theorem orientedQuarticBasePoleOrthogonalProfile_fourth
    (W1 W2 W3 : QuarticHighWitness) (t : ℝ) :
    profileFourthMoment
      (orientedQuarticBasePoleOrthogonalProfile W1 W2 W3 t)
      =
    4 * quarticBasePoleOrientation W1 W2 W3 t *
      quarticBasePoleTargetDet W1 W2 W3 t := by
  unfold orientedQuarticBasePoleOrthogonalProfile profileFourthMoment
  have hpoint :
      (fun u : ℝ =>
        quarticBasePoleOrientation W1 W2 W3 t *
          quarticBasePoleOrthogonalProfile W1 W2 W3 t u * u^4)
        =
      fun u =>
        quarticBasePoleOrientation W1 W2 W3 t *
          (quarticBasePoleOrthogonalProfile W1 W2 W3 t u * u^4) := by
    funext u
    ring
  rw [hpoint, integral_const_mul,
      quarticBasePoleOrthogonalProfile_fourth]
  ring

theorem orientedQuarticBasePoleOrthogonalProfile_fourth_neg
    (W1 W2 W3 : QuarticHighWitness) {t : ℝ}
    (hdet : quarticBasePoleTargetDet W1 W2 W3 t ≠ 0) :
    profileFourthMoment
      (orientedQuarticBasePoleOrthogonalProfile W1 W2 W3 t) < 0 := by
  rw [orientedQuarticBasePoleOrthogonalProfile_fourth]
  unfold quarticBasePoleOrientation
  by_cases hneg : quarticBasePoleTargetDet W1 W2 W3 t < 0
  · simp [hneg]
  · have hpos : 0 < quarticBasePoleTargetDet W1 W2 W3 t :=
      lt_of_le_of_ne (le_of_not_gt hneg) (Ne.symm hdet)
    simp [hneg]
    nlinarith

def quarticBasePoleSignedNormalizedHeightDefect
    (W1 W2 W3 : QuarticHighWitness)
    (t a : ℝ) : ℝ :=
  quarticBasePoleOrientation W1 W2 W3 t *
    (quarticBasePoleCoeff1 W1 W2 W3 t *
        heightDefect
          (quarticThreeWindowProfile W1.R W1.lam) 1 a 0
      +
     quarticBasePoleCoeff2 W1 W2 W3 t *
        heightDefect
          (quarticThreeWindowProfile W2.R W2.lam) 1 a 0
      +
     quarticBasePoleCoeff3 W1 W2 W3 t *
        heightDefect
          (quarticThreeWindowProfile W3.R W3.lam) 1 a 0)

theorem quarticBasePoleSignedNormalizedHeightDefect_eq_cosh
    (W1 W2 W3 : QuarticHighWitness)
    (t a : ℝ) :
    quarticBasePoleSignedNormalizedHeightDefect W1 W2 W3 t a
      =
    -(1/4 : ℝ) *
      compactCoshTransform
        (orientedQuarticBasePoleOrthogonalProfile W1 W2 W3 t) a := by
  have h1 :=
    heightDefect_eq_neg_quarter_projectiveCosh
      (quarticThreeWindowProfile_continuous W1.Rpos)
      (quarticThreeWindowProfile_compact W1.Rpos) 1 a
  have h2 :=
    heightDefect_eq_neg_quarter_projectiveCosh
      (quarticThreeWindowProfile_continuous W2.Rpos)
      (quarticThreeWindowProfile_compact W2.Rpos) 1 a
  have h3 :=
    heightDefect_eq_neg_quarter_projectiveCosh
      (quarticThreeWindowProfile_continuous W3.Rpos)
      (quarticThreeWindowProfile_compact W3.Rpos) 1 a
  unfold quarticBasePoleSignedNormalizedHeightDefect
    orientedQuarticBasePoleOrthogonalProfile
    quarticBasePoleOrthogonalProfile
    compactCoshTransform
  rw [h1,h2,h3]
  have i1 :
      Integrable (fun u : ℝ =>
        quarticWitnessNormalizedProfile W1 u * Real.cosh (a*u)) :=
    ((quarticWitnessNormalizedProfile_continuous W1).mul (by fun_prop))
      |>.integrable_of_hasCompactSupport
        (quarticWitnessNormalizedProfile_compact W1).mul_right
  have i2 :
      Integrable (fun u : ℝ =>
        quarticWitnessNormalizedProfile W2 u * Real.cosh (a*u)) :=
    ((quarticWitnessNormalizedProfile_continuous W2).mul (by fun_prop))
      |>.integrable_of_hasCompactSupport
        (quarticWitnessNormalizedProfile_compact W2).mul_right
  have i3 :
      Integrable (fun u : ℝ =>
        quarticWitnessNormalizedProfile W3 u * Real.cosh (a*u)) :=
    ((quarticWitnessNormalizedProfile_continuous W3).mul (by fun_prop))
      |>.integrable_of_hasCompactSupport
        (quarticWitnessNormalizedProfile_compact W3).mul_right
  rw [show
      (fun u : ℝ =>
        quarticBasePoleOrientation W1 W2 W3 t *
          (quarticBasePoleCoeff1 W1 W2 W3 t *
              quarticWitnessNormalizedProfile W1 u
            + quarticBasePoleCoeff2 W1 W2 W3 t *
              quarticWitnessNormalizedProfile W2 u
            + quarticBasePoleCoeff3 W1 W2 W3 t *
              quarticWitnessNormalizedProfile W3 u)
          * Real.cosh (a*u))
        =
      fun u =>
        quarticBasePoleOrientation W1 W2 W3 t *
          (quarticBasePoleCoeff1 W1 W2 W3 t *
              (quarticWitnessNormalizedProfile W1 u * Real.cosh (a*u))
            + quarticBasePoleCoeff2 W1 W2 W3 t *
              (quarticWitnessNormalizedProfile W2 u * Real.cosh (a*u))
            + quarticBasePoleCoeff3 W1 W2 W3 t *
              (quarticWitnessNormalizedProfile W3 u * Real.cosh (a*u))) by
      funext u
      ring,
      integral_const_mul,
      integral_add ((i1.const_mul _).add (i2.const_mul _))
        (i3.const_mul _),
      integral_add (i1.const_mul _) (i2.const_mul _),
      integral_const_mul,integral_const_mul,integral_const_mul]
  ring

structure QuarticBasePoleSignedBand
    (W1 W2 W3 : QuarticHighWitness) (t : ℝ) where
  eps : ℝ
  epsPos : 0 < eps
  targetPos :
    ∀ a : ℝ, 0 < |a| -> |a| < eps ->
      0 < quarticBasePoleSignedNormalizedHeightDefect
        W1 W2 W3 t a

theorem exists_quarticBasePoleSignedBand
    (W1 W2 W3 : QuarticHighWitness)
    {t : ℝ}
    (hdet : quarticBasePoleTargetDet W1 W2 W3 t ≠ 0) :
    Nonempty (QuarticBasePoleSignedBand W1 W2 W3 t) := by
  let P := orientedQuarticBasePoleOrthogonalProfile W1 W2 W3 t
  have hP : Continuous P :=
    orientedQuarticBasePoleOrthogonalProfile_continuous W1 W2 W3 t
  have hPc : HasCompactSupport P :=
    orientedQuarticBasePoleOrthogonalProfile_compact W1 W2 W3 t
  have hP0 : profileZerothMoment P = 0 :=
    orientedQuarticBasePoleOrthogonalProfile_zeroth_zero W1 W2 W3 t
  have hP2 : profileSecondMoment P = 0 :=
    orientedQuarticBasePoleOrthogonalProfile_second_zero W1 W2 W3 t
  have hP4 : profileFourthMoment P < 0 :=
    orientedQuarticBasePoleOrthogonalProfile_fourth_neg
      W1 W2 W3 hdet
  obtain ⟨eps,heps,hnegR⟩ :=
    exists_profile_cosh_neg_right_of_quartic_moments
      hP hPc hP0 hP2 hP4
  refine ⟨{
    eps := eps
    epsPos := heps
    targetPos := ?_
  }⟩
  intro a ha0 hae
  have hneg : compactCoshTransform P a < 0 := by
    by_cases ha : 0 <= a
    · have habs : |a| = a := abs_of_nonneg ha
      exact hnegR a
        (by simpa [habs] using ha0)
        (by simpa [habs] using hae)
    · have haneg : a < 0 := lt_of_not_ge ha
      have habs : |a| = -a := abs_of_neg haneg
      have hp := hnegR (-a)
        (by linarith)
        (by simpa [habs] using hae)
      have heven :
          compactCoshTransform P (-a)
            = compactCoshTransform P a := by
        unfold compactCoshTransform
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun u => by
          rw [show (-a)*u = -(a*u) by ring, Real.cosh_neg]
      rw [heven] at hp
      exact hp
  rw [quarticBasePoleSignedNormalizedHeightDefect_eq_cosh]
  nlinarith

def quarticBasePoleSignedPhysicalHeightDefect
    (W1 W2 W3 : QuarticHighWitness)
    (t a : ℝ) : ℝ :=
  quarticBasePoleOrientation W1 W2 W3 t *
    (quarticBasePoleCoeff1 W1 W2 W3 t *
        heightDefect
          (quarticPhysicalDetector W1.R W1.lam t) (t/16) a 0
      +
     quarticBasePoleCoeff2 W1 W2 W3 t *
        heightDefect
          (quarticPhysicalDetector W2.R W2.lam t) (t/16) a 0
      +
     quarticBasePoleCoeff3 W1 W2 W3 t *
        heightDefect
          (quarticPhysicalDetector W3.R W3.lam t) (t/16) a 0)

theorem quarticBasePoleSignedPhysicalHeightDefect_scaled
    (W1 W2 W3 : QuarticHighWitness)
    {t : ℝ} (ht : 0 < t)
    (a : ℝ) :
    quarticBasePoleSignedPhysicalHeightDefect W1 W2 W3 t a
      =
    (1/(t/16)^2) *
      quarticBasePoleSignedNormalizedHeightDefect
        W1 W2 W3 t (a/(t/16)) := by
  have hr : 0 < t/16 := by positivity
  unfold quarticBasePoleSignedPhysicalHeightDefect
    quarticBasePoleSignedNormalizedHeightDefect
    quarticPhysicalDetector
  rw [heightDefect_projectiveRescale_zero hr a,
      heightDefect_projectiveRescale_zero hr a,
      heightDefect_projectiveRescale_zero hr a]
  ring

def quarticBasePoleSignedZeroSource
    (W1 W2 W3 : QuarticHighWitness)
    (t : ℝ) (rho : Zeros) : ℝ :=
  ((zetaZeroConfig).mult (rho : ℂ) : ℝ) *
    quarticBasePoleSignedPhysicalHeightDefect
      W1 W2 W3 t (heightOf rho)

theorem quarticBasePoleSignedZeroSource_nonneg
    (W1 W2 W3 : QuarticHighWitness)
    {t : ℝ} (ht : 0 < t)
    (B : QuarticBasePoleSignedBand W1 W2 W3 t)
    (hhigh : 8/t < B.eps)
    (rho : Zeros) :
    0 <= quarticBasePoleSignedZeroSource W1 W2 W3 t rho := by
  unfold quarticBasePoleSignedZeroSource
  by_cases ha : heightOf rho = 0
  · rw [ha]
    unfold quarticBasePoleSignedPhysicalHeightDefect
    simp [heightDefect_self]
  · have hr : 0 < t/16 := by positivity
    have hstrip := zetaZero_height_abs_le_half rho
    have hnorm0 : 0 < |heightOf rho/(t/16)| := by
      rw [abs_pos]
      exact div_ne_zero ha hr.ne'
    have hnorm :
        |heightOf rho/(t/16)| <= 8/t := by
      rw [abs_div, abs_of_pos hr]
      rw [div_le_div_iff₀ hr ht]
      nlinarith
    have hp :=
      B.targetPos (heightOf rho/(t/16))
        hnorm0 (hnorm.trans_lt hhigh)
    rw [quarticBasePoleSignedPhysicalHeightDefect_scaled
      W1 W2 W3 ht]
    have hfac : 0 < 1/(t/16)^2 := by positivity
    exact mul_nonneg (by positivity)
      (mul_pos hfac hp).le

theorem quarticBasePoleSignedZeroSource_pos
    (W1 W2 W3 : QuarticHighWitness)
    {t : ℝ} (ht : 0 < t)
    (B : QuarticBasePoleSignedBand W1 W2 W3 t)
    (hhigh : 8/t < B.eps)
    (rho : Zeros)
    (hoff : heightOf rho ≠ 0) :
    0 < quarticBasePoleSignedZeroSource W1 W2 W3 t rho := by
  have hr : 0 < t/16 := by positivity
  have hstrip := zetaZero_height_abs_le_half rho
  have hnorm0 : 0 < |heightOf rho/(t/16)| := by
    rw [abs_pos]
    exact div_ne_zero hoff hr.ne'
  have hnorm :
      |heightOf rho/(t/16)| <= 8/t := by
    rw [abs_div, abs_of_pos hr]
    rw [div_le_div_iff₀ hr ht]
    nlinarith
  have hp :=
    B.targetPos (heightOf rho/(t/16))
      hnorm0 (hnorm.trans_lt hhigh)
  unfold quarticBasePoleSignedZeroSource
  rw [quarticBasePoleSignedPhysicalHeightDefect_scaled
      W1 W2 W3 ht]
  have hfac : 0 < 1/(t/16)^2 := by positivity
  exact mul_pos (by positivity) (mul_pos hfac hp)

def quarticBasePoleSignedCombinedCluster
    (W1 W2 W3 : QuarticHighWitness) (t : ℝ) : ℝ :=
  quarticBasePoleOrientation W1 W2 W3 t *
    quarticBasePoleCombinedCluster W1 W2 W3 t

def quarticBasePoleSignedCombinedHorizontal
    (W1 W2 W3 : QuarticHighWitness) (t : ℝ) : ℝ :=
  quarticBasePoleOrientation W1 W2 W3 t *
    quarticBasePoleCombinedHorizontal W1 W2 W3 t

theorem quarticBasePoleSignedCluster_eq_horizontal
    (W1 W2 W3 : QuarticHighWitness)
    {t : ℝ} (ht : 100 <= t) :
    quarticBasePoleSignedCombinedCluster W1 W2 W3 t
      =
    quarticBasePoleSignedCombinedHorizontal W1 W2 W3 t := by
  unfold quarticBasePoleSignedCombinedCluster
    quarticBasePoleSignedCombinedHorizontal
  rw [quarticBasePoleCombinedCluster_eq_horizontal W1 W2 W3 ht]

theorem quarticBasePoleSignedSource_eq_linear
    (W1 W2 W3 : QuarticHighWitness)
    (t : ℝ) (rho : Zeros) :
    quarticBasePoleSignedZeroSource W1 W2 W3 t rho
      =
    quarticBasePoleOrientation W1 W2 W3 t *
      (quarticBasePoleCoeff1 W1 W2 W3 t *
          zeroHeightDefect
            (quarticPhysicalDetector W1.R W1.lam t) (t/16) rho
        +
       quarticBasePoleCoeff2 W1 W2 W3 t *
          zeroHeightDefect
            (quarticPhysicalDetector W2.R W2.lam t) (t/16) rho
        +
       quarticBasePoleCoeff3 W1 W2 W3 t *
          zeroHeightDefect
            (quarticPhysicalDetector W3.R W3.lam t) (t/16) rho) := by
  unfold quarticBasePoleSignedZeroSource
    quarticBasePoleSignedPhysicalHeightDefect
    zeroHeightDefect
  ring

theorem quarticBasePoleSignedSource_summable
    (W1 W2 W3 : QuarticHighWitness)
    {t : ℝ} (ht : 0 < t) :
    Summable fun z : SameOrd t =>
      quarticBasePoleSignedZeroSource W1 W2 W3 t (z : Zeros) := by
  have h1 :=
    summable_zeroHeightDefect
      (quarticPhysicalDetector_contDiff W1.Rpos)
      (quarticPhysicalDetector_compact W1.Rpos ht)
      (quarticPhysicalDetector_even W1.R W1.lam t)
      t (t/16)
  have h2 :=
    summable_zeroHeightDefect
      (quarticPhysicalDetector_contDiff W2.Rpos)
      (quarticPhysicalDetector_compact W2.Rpos ht)
      (quarticPhysicalDetector_even W2.R W2.lam t)
      t (t/16)
  have h3 :=
    summable_zeroHeightDefect
      (quarticPhysicalDetector_contDiff W3.Rpos)
      (quarticPhysicalDetector_compact W3.Rpos ht)
      (quarticPhysicalDetector_even W3.R W3.lam t)
      t (t/16)
  have hs :=
    ((h1.mul_left (quarticBasePoleCoeff1 W1 W2 W3 t)).add
      (h2.mul_left (quarticBasePoleCoeff2 W1 W2 W3 t))).add
      (h3.mul_left (quarticBasePoleCoeff3 W1 W2 W3 t))
  have hso := hs.mul_left (quarticBasePoleOrientation W1 W2 W3 t)
  refine hso.congr ?_
  intro z
  rw [quarticBasePoleSignedSource_eq_linear]
  ring

theorem quarticBasePoleSignedCluster_eq_tsum
    (W1 W2 W3 : QuarticHighWitness)
    {t : ℝ} (ht : 0 < t) :
    quarticBasePoleSignedCombinedCluster W1 W2 W3 t
      =
    ∑' z : SameOrd t,
      quarticBasePoleSignedZeroSource W1 W2 W3 t (z : Zeros) := by
  have hc1 :=
    clusterHeightDefect_eq_tsum
      (quarticPhysicalDetector_contDiff W1.Rpos)
      (quarticPhysicalDetector_compact W1.Rpos ht)
      (quarticPhysicalDetector_even W1.R W1.lam t)
      t (t/16)
  have hc2 :=
    clusterHeightDefect_eq_tsum
      (quarticPhysicalDetector_contDiff W2.Rpos)
      (quarticPhysicalDetector_compact W2.Rpos ht)
      (quarticPhysicalDetector_even W2.R W2.lam t)
      t (t/16)
  have hc3 :=
    clusterHeightDefect_eq_tsum
      (quarticPhysicalDetector_contDiff W3.Rpos)
      (quarticPhysicalDetector_compact W3.Rpos ht)
      (quarticPhysicalDetector_even W3.R W3.lam t)
      t (t/16)
  unfold quarticBasePoleSignedCombinedCluster
    quarticBasePoleCombinedCluster
  rw [hc1,hc2,hc3]
  rw [← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left]
  have hs := quarticBasePoleSignedSource_summable W1 W2 W3 ht
  apply tsum_congr
  intro z
  rw [quarticBasePoleSignedSource_eq_linear]
  ring

theorem quarticBasePoleSignedSource_reflect
    (W1 W2 W3 : QuarticHighWitness)
    (t : ℝ) (rho : Zeros) :
    quarticBasePoleSignedZeroSource W1 W2 W3 t (reflectZero rho)
      =
    quarticBasePoleSignedZeroSource W1 W2 W3 t rho := by
  rw [quarticBasePoleSignedSource_eq_linear,
      quarticBasePoleSignedSource_eq_linear]
  unfold zeroHeightDefect
  rw [reflectZero_mult,heightOf_reflectZero,
      heightDefect_neg_height,heightDefect_neg_height,
      heightDefect_neg_height]

theorem quarticBasePoleSigned_targetPair_sum
    (W1 W2 W3 : QuarticHighWitness)
    {t : ℝ}
    {rho : Zeros}
    (him : (rho : ℂ).im = t)
    (hoff : heightOf rho ≠ 0) :
    (∑ z ∈ canonicalTargetPairFinset rho him,
      quarticBasePoleSignedZeroSource
        W1 W2 W3 t (z : Zeros))
      =
    2 * quarticBasePoleSignedZeroSource
      W1 W2 W3 t rho := by
  let z0 : SameOrd t := ⟨rho,him⟩
  let z1 : SameOrd t :=
    ⟨reflectZero rho, by
      rw [im_reflectZero]
      exact him⟩
  have hne : z1 ≠ z0 := by
    intro h
    have hv : (z1 : Zeros) = (z0 : Zeros) :=
      congrArg Subtype.val h
    dsimp [z0,z1] at hv
    exact (reflectZero_ne_of_height_ne_zero hoff) hv
  unfold canonicalTargetPairFinset
  change
    (∑ z ∈ ({z0,z1} : Finset (SameOrd t)),
      quarticBasePoleSignedZeroSource
        W1 W2 W3 t (z : Zeros)) = _
  rw [Finset.sum_insert]
  · rw [Finset.sum_singleton]
    dsimp [z0,z1]
    rw [quarticBasePoleSignedSource_reflect]
    ring
  · simpa [Finset.mem_singleton] using hne

theorem quarticBasePoleSigned_two_target_le_cluster
    (W1 W2 W3 : QuarticHighWitness)
    {t : ℝ} (ht : 0 < t)
    (B : QuarticBasePoleSignedBand W1 W2 W3 t)
    (hhigh : 8/t < B.eps)
    {rho : Zeros}
    (him : (rho : ℂ).im = t)
    (hoff : heightOf rho ≠ 0) :
    2 * quarticBasePoleSignedZeroSource W1 W2 W3 t rho
      <=
    quarticBasePoleSignedCombinedCluster W1 W2 W3 t := by
  have hs := quarticBasePoleSignedSource_summable W1 W2 W3 ht
  have hsplit :=
    hs.sum_add_tsum_compl
      (s:=canonicalTargetPairFinset rho him)
  rw [quarticBasePoleSignedCluster_eq_tsum W1 W2 W3 ht]
  rw [← hsplit,
      quarticBasePoleSigned_targetPair_sum W1 W2 W3 him hoff]
  exact le_add_of_nonneg_right
    (tsum_nonneg fun z =>
      quarticBasePoleSignedZeroSource_nonneg
        W1 W2 W3 ht B hhigh ((z : SameOrd t) : Zeros))

/--
Prize-facing signed base+pole orthogonalized cutset, with no coefficient-sign
hypotheses.
-/
theorem false_of_quarticBasePole_signed_horizontal_strict
    (W1 W2 W3 : QuarticHighWitness)
    {t : ℝ} (ht : 100 <= t)
    (hdet : quarticBasePoleTargetDet W1 W2 W3 t ≠ 0)
    (B : QuarticBasePoleSignedBand W1 W2 W3 t)
    (hhigh : 8/t < B.eps)
    {rho : Zeros}
    (him : (rho : ℂ).im = t)
    (hoff : heightOf rho ≠ 0)
    (hstrict :
      quarticBasePoleSignedCombinedHorizontal W1 W2 W3 t
        <
      2 * quarticBasePoleSignedZeroSource W1 W2 W3 t rho) :
    False := by
  have hlo :=
    quarticBasePoleSigned_two_target_le_cluster
      W1 W2 W3 (by linarith : 0 < t)
      B hhigh him hoff
  rw [quarticBasePoleSignedCluster_eq_horizontal W1 W2 W3 ht] at hlo
  linarith

end Synthesis
