import Synthesis.RiemannCompactCoshQuantitativeQuarticBand
import Synthesis.RiemannCompactCoshSupportMassBound
import Synthesis.RiemannProjectiveQuarticFourWindowSignedPoleCutset

/-!
# Explicit quantitative band for the signed four-window pole-cancelled observable

The original `QuarticFourSignedPolePair` stores an existential punctured
radius `eps`.  For the Clay-facing route that is stronger bookkeeping than
needed and weaker numerically than desired: the consumer only needs a concrete
radius which can be compared with the normalized critical-strip width `8/t`.

For the combined signed profile P we already know

  M0(P) = 0,
  M2(P) = 0,
  M4(P) = -4 * targetStrength.

The generic compact-cosh fourth-order compiler therefore gives the explicit
radius

  min 1 ((4 * targetStrength) /
    (2 * (compactCoshFourthLipschitzConstant P + 1))).

This file installs that radius on the exact signed-pole witness and rebuilds the
target-pair lower bound and contradiction compiler using it directly.  Thus the
old existential `W.eps` is no longer on the preferred terminal path.

No theorem here proves the remaining scalar inequality `8/t < radius`; that
is the quantitative uniformity theorem which must be supplied by actual
analysis.
-/

noncomputable section

open MeasureTheory Complex Set
open scoped Real

namespace Synthesis

open Zeta23
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilClusterTwoRadiusProfile
open Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition
open Zeta23Bridge.LiteralWeilOffOrdinateReflectionPair

def QuarticFourSignedPolePair.quantitativeTargetRadius
    {t : ℝ} (W : QuarticFourSignedPolePair t) : ℝ :=
  quantitativeFourthOrderRadius
    (4 * W.targetStrength)
    (compactCoshFourthLipschitzConstant
      (quarticFourSignedPoleCombinedProfile
        W.R W.muHalf W.muTwo t))

theorem QuarticFourSignedPolePair.quantitativeTargetRadius_pos
    {t : ℝ} (W : QuarticFourSignedPolePair t) :
    0 < W.quantitativeTargetRadius := by
  unfold QuarticFourSignedPolePair.quantitativeTargetRadius
  exact quantitativeFourthOrderRadius_pos
    (by nlinarith [W.targetStrength])
    (compactCoshFourthLipschitzConstant_nonneg _)

/--
The signed combined height defect is positive on the explicit quantitative
fourth-order band.  This is the constructive replacement for
`W.combinedTargetBand`.
-/
theorem QuarticFourSignedPolePair.quantitativeCombinedTargetBand
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (a : ℝ)
    (ha0 : 0 < |a|)
    (ha :
      |a| < W.quantitativeTargetRadius) :
    0 <
      quarticFourSignedPoleCombinedHeightDefect
        W.R W.muHalf W.muTwo t a := by
  let P : ℝ -> ℝ :=
    quarticFourSignedPoleCombinedProfile
      W.R W.muHalf W.muTwo t
  let m : ℝ := 4 * W.targetStrength
  have hm : 0 < m := by
    dsimp [m]
    nlinarith [W.targetStrength]
  have hP : Continuous P := by
    dsimp [P]
    exact quarticFourSignedPoleCombinedProfile_continuous W.Rpos
  have hPc : HasCompactSupport P := by
    dsimp [P]
    exact quarticFourSignedPoleCombinedProfile_compact W.Rpos
  have hM0 : profileZerothMoment P = 0 := by
    dsimp [P]
    exact quarticFourSignedPoleCombinedProfile_zeroth_zero W.Rpos
  have hM2 : profileSecondMoment P = 0 := by
    dsimp [P]
    exact quarticFourSignedPoleCombinedProfile_second_zero
      W.Rpos W.J2Half W.J2Two
  have hM4 : profileFourthMoment P <= -m := by
    dsimp [P, m]
    rw [quarticFourSignedPoleCombinedProfile_fourth W.Rpos]
  have hcosh :=
    compactCosh_neg_of_quartic_margin
      hP hPc hm hM0 hM2 hM4 a ha0
  have hRadius :
      |a| <
        quantitativeFourthOrderRadius m
          (compactCoshFourthLipschitzConstant P) := by
    simpa [QuarticFourSignedPolePair.quantitativeTargetRadius, m, P]
      using ha
  have hneg := hcosh hRadius
  rw [quarticFourSignedPoleCombinedHeightDefect_eq_cosh W.Rpos]
  dsimp [P] at hneg
  nlinarith

theorem QuarticFourSignedPolePair.physicalCombinedHeightDefect_nonneg_quantitative
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (hhigh : 8/t < W.quantitativeTargetRadius)
    (rho : Zeros) :
    0 <= W.physicalCombinedHeightDefect (heightOf rho) := by
  by_cases ha : heightOf rho = 0
  · rw [ha]
    unfold QuarticFourSignedPolePair.physicalCombinedHeightDefect
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
    have hband :=
      W.quantitativeCombinedTargetBand
        (heightOf rho/(t/16)) hnorm0
        (hnorm.trans_lt hhigh)
    rw [W.physicalCombinedHeightDefect_scaled ht]
    have hfac : 0 < 1/(t/16)^2 := by positivity
    exact (mul_pos hfac hband).le

theorem QuarticFourSignedPolePair.physicalCombinedHeightDefect_pos_quantitative
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (hhigh : 8/t < W.quantitativeTargetRadius)
    (rho : Zeros)
    (hoff : heightOf rho ≠ 0) :
    0 < W.physicalCombinedHeightDefect (heightOf rho) := by
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
  have hband :=
    W.quantitativeCombinedTargetBand
      (heightOf rho/(t/16)) hnorm0
      (hnorm.trans_lt hhigh)
  rw [W.physicalCombinedHeightDefect_scaled ht]
  have hfac : 0 < 1/(t/16)^2 := by positivity
  exact mul_pos hfac hband

theorem QuarticFourSignedPolePair.combinedZeroHeightDefect_nonneg_quantitative
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (hhigh : 8/t < W.quantitativeTargetRadius)
    (rho : Zeros) :
    0 <= W.combinedZeroHeightDefect rho := by
  unfold QuarticFourSignedPolePair.combinedZeroHeightDefect
  exact mul_nonneg (by positivity)
    (W.physicalCombinedHeightDefect_nonneg_quantitative
      ht hhigh rho)

theorem QuarticFourSignedPolePair.combinedZeroHeightDefect_pos_quantitative
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (hhigh : 8/t < W.quantitativeTargetRadius)
    (rho : Zeros)
    (hoff : heightOf rho ≠ 0) :
    0 < W.combinedZeroHeightDefect rho := by
  unfold QuarticFourSignedPolePair.combinedZeroHeightDefect
  exact mul_pos (by positivity)
    (W.physicalCombinedHeightDefect_pos_quantitative
      ht hhigh rho hoff)

/--
Quantitative target-pair lower bound with no dependence on the existential
`W.eps` field.
-/
theorem QuarticFourSignedPolePair.two_target_le_combinedCluster_quantitative
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (hhigh : 8/t < W.quantitativeTargetRadius)
    {rho : Zeros}
    (him : (rho : ℂ).im = t)
    (hoff : heightOf rho ≠ 0) :
    2 * W.combinedZeroHeightDefect rho
      <= W.combinedCluster := by
  have hs := W.combinedSource_summable ht
  have hsplit :=
    hs.sum_add_tsum_compl
      (s:=canonicalTargetPairFinset rho him)
  rw [W.combinedCluster_eq_tsum ht]
  rw [← hsplit, W.targetPair_sum_eq_two him hoff]
  exact le_add_of_nonneg_right
    (tsum_nonneg fun z =>
      W.combinedZeroHeightDefect_nonneg_quantitative
        ht hhigh ((z : SameOrd t) : Zeros))

/--
Preferred contradiction compiler: the only band input is now the explicit
scalar inequality against `quantitativeTargetRadius`.
-/
theorem false_of_quarticFourSignedPole_external_strict_quantitative
    {t : ℝ} (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (hhigh : 8/t < W.quantitativeTargetRadius)
    {rho : Zeros}
    (him : (rho : ℂ).im = t)
    (hoff : heightOf rho ≠ 0)
    (hstrict :
      W.poleTwo *
        (offOrdProjectiveDefect
            (quarticFourPhysicalDetector W.R (1/2) W.muHalf t)
            t (t/16)
          +
         gammaProjectiveDefect
            (quarticFourPhysicalDetector W.R (1/2) W.muHalf t)
            t (t/16))
        +
      (-W.poleHalf) *
        (offOrdProjectiveDefect
            (quarticFourPhysicalDetector W.R (2/3) W.muTwo t)
            t (t/16)
          +
         gammaProjectiveDefect
            (quarticFourPhysicalDetector W.R (2/3) W.muTwo t)
            t (t/16))
      <
      2 * W.combinedZeroHeightDefect rho) :
    False := by
  have hlo :=
    W.two_target_le_combinedCluster_quantitative
      (by linarith : 0 < t) hhigh him hoff
  rw [W.combinedCluster_eq_offGamma ht] at hlo
  linarith


/-!
## Existential quantitative-witness cut for G1

The preferred G1 quantifier is existential in the witness:

  for every sufficiently high t, choose one narrow signed-pole witness W_t

with the explicit strength floor and a uniform K bound.

This is strictly weaker, and exactly what the terminal argument consumes.
The old universal-over-all-witnesses predicates are retained below only as
strong donor interfaces; they are not the preferred Goal-1 obligation.
-/

def quarticSignedPoleStrengthFloor : ℝ :=
  7 * Real.pi^4 / 1600

def QuarticFourSignedPolePair.fourthLipschitz
    {t : ℝ} (W : QuarticFourSignedPolePair t) : ℝ :=
  compactCoshFourthLipschitzConstant
    (quarticFourSignedPoleCombinedProfile
      W.R W.muHalf W.muTwo t)

theorem quarticSignedPoleStrengthFloor_pos :
    0 < quarticSignedPoleStrengthFloor := by
  unfold quarticSignedPoleStrengthFloor
  positivity

/--
The strength part of G1 is already paid by the narrow smooth construction.
-/
theorem exists_quarticFourSignedPolePair_strengthFloor
    {t : ℝ} (ht : 200 <= t) :
    ∃ W : QuarticFourSignedPolePair t,
      quarticSignedPoleStrengthFloor <= W.targetStrength := by
  simpa [quarticSignedPoleStrengthFloor] using
    exists_quarticFourSignedPolePair_with_strength_floor ht

/--
Preferred remaining G1 source obligation.

A single constant K0 must work for one floor-certified constructed witness at
each high ordinate.  No bound is requested for arbitrary inhabitants of
`QuarticFourSignedPolePair t`.
-/
def quarticSignedPole_goodWitness_uniform_K
    (T K0 : ℝ) : Prop :=
  ∀ {t : ℝ}, T <= t ->
    ∃ W : QuarticFourSignedPolePair t,
      quarticSignedPoleStrengthFloor <= W.targetStrength
      ∧ W.fourthLipschitz <= K0

/--
Historical stronger donor interface.  This is no longer the preferred G1
quantifier shape.
-/
def quarticSignedPole_targetStrength_uniform_lower
    (T S0 : ℝ) : Prop :=
  ∀ {t : ℝ}, T <= t ->
    ∀ W : QuarticFourSignedPolePair t,
      S0 <= W.targetStrength

/--
Historical stronger donor interface.  The preferred G1 theorem only needs K
on one constructed floor-certified witness per t.
-/
def quarticSignedPole_fourthLipschitz_uniform_upper
    (T K0 : ℝ) : Prop :=
  ∀ {t : ℝ}, T <= t ->
    ∀ W : QuarticFourSignedPolePair t,
      W.fourthLipschitz <= K0

/--
Elementary G1 threshold compiler for one selected witness.

For t>8, if S0 <= S(W), K(W) <= K0, and

  4 (K0+1) / t < S0,

then 8/t lies inside the explicit quantitative target radius.
-/
theorem quarticSignedPole_quantitativeBand_covers_strip
    {t S0 K0 : ℝ}
    (ht8 : 8 < t)
    (W : QuarticFourSignedPolePair t)
    (hS0 : 0 < S0)
    (hK0 : 0 <= K0)
    (hS : S0 <= W.targetStrength)
    (hK : W.fourthLipschitz <= K0)
    (hthreshold : 4 * (K0 + 1) / t < S0) :
    8/t < W.quantitativeTargetRadius := by
  let K := W.fourthLipschitz
  have ht : 0 < t := by linarith
  have hKnonneg : 0 <= K := by
    dsimp [K, QuarticFourSignedPolePair.fourthLipschitz]
    exact compactCoshFourthLipschitzConstant_nonneg _
  have hK1 : 0 < K + 1 := by linarith
  have hmono :
      4 * (K + 1) / t <= 4 * (K0 + 1) / t := by
    exact div_le_div_of_nonneg_right (by nlinarith) ht.le
  have hcore :
      4 * (K + 1) / t < W.targetStrength :=
    lt_of_le_of_lt hmono (hthreshold.trans_le hS)
  have hcross :
      4 * (K + 1) < W.targetStrength * t := by
    rwa [div_lt_iff₀ ht] at hcore
  unfold QuarticFourSignedPolePair.quantitativeTargetRadius
    quantitativeFourthOrderRadius
  apply lt_min
  · rw [div_lt_one ht]
    exact ht8
  · have hden : 0 < 2 * (K + 1) := by positivity
    change
      8 / t <
        (4 * W.targetStrength) / (2 * (K + 1))
    rw [div_lt_div_iff₀ ht hden]
    nlinarith

/--
Preferred existential G1 compiler.

Once `quarticSignedPole_goodWitness_uniform_K T K0` is proved, every
t >= T satisfying the scalar threshold admits a concrete witness whose
explicit quantitative radius covers the whole normalized critical strip.
-/
theorem exists_quarticSignedPolePair_quantitativeBand_covers_strip
    {T t K0 : ℝ}
    (htT : T <= t)
    (ht8 : 8 < t)
    (hK0 : 0 <= K0)
    (hgood : quarticSignedPole_goodWitness_uniform_K T K0)
    (hthreshold :
      4 * (K0 + 1) / t < quarticSignedPoleStrengthFloor) :
    ∃ W : QuarticFourSignedPolePair t,
      quarticSignedPoleStrengthFloor <= W.targetStrength
      ∧ 8/t < W.quantitativeTargetRadius := by
  obtain ⟨W,hS,hK⟩ := hgood htT
  refine ⟨W,hS,?_⟩
  exact quarticSignedPole_quantitativeBand_covers_strip
    ht8 W quarticSignedPoleStrengthFloor_pos hK0 hS hK hthreshold

/--
The remaining G1 debt can be isolated even more narrowly: if a uniform K
theorem can be proved for the witnesses produced by the strength-floor
constructor, it packages directly into the preferred source obligation.
-/
def quarticSignedPole_constructedWitness_uniform_K
    (K0 : ℝ) : Prop :=
  ∀ {t : ℝ}, 200 <= t ->
    ∃ W : QuarticFourSignedPolePair t,
      quarticSignedPoleStrengthFloor <= W.targetStrength
      ∧ W.fourthLipschitz <= K0

theorem quarticSignedPole_constructedWitness_uniform_K_to_goodWitness
    {K0 : ℝ}
    (hK : quarticSignedPole_constructedWitness_uniform_K K0) :
    quarticSignedPole_goodWitness_uniform_K 200 K0 := by
  intro t ht
  exact hK ht

/--
Support/L1 reduction for the remaining K estimate.

Any selected witness whose combined profile is supported in |u| <= L and has
L1 mass at most M automatically satisfies

  K(W) <= M * cosh(L) * L^5.
-/
theorem QuarticFourSignedPolePair.fourthLipschitz_le_of_support_mass
    {t L M : ℝ}
    (W : QuarticFourSignedPolePair t)
    (hL : 0 <= L)
    (hsupp :
      ∀ u : ℝ,
        quarticFourSignedPoleCombinedProfile
          W.R W.muHalf W.muTwo t u ≠ 0 ->
        |u| <= L)
    (hmass :
      Zeta23Bridge.LiteralWeilProjectiveStripConstant.taperMass
        (quarticFourSignedPoleCombinedProfile
          W.R W.muHalf W.muTwo t)
        <= M) :
    W.fourthLipschitz
      <= M * Real.cosh L * L^5 := by
  unfold QuarticFourSignedPolePair.fourthLipschitz
  exact compactCoshFourthLipschitzConstant_le_support_mass
    (quarticFourSignedPoleCombinedProfile_continuous W.Rpos)
    (quarticFourSignedPoleCombinedProfile_compact W.Rpos)
    hL hsupp hmass

end Synthesis
