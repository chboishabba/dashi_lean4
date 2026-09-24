import Synthesis.RiemannCompactCoshQuantitativeQuarticBand
import Synthesis.RiemannCompactCoshSupportMassBound
import Mathlib.Analysis.Complex.ExponentialBounds
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
open Zeta23Bridge.LiteralWeilProjectiveStripConstant

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
    (by nlinarith [W.targetStrength_pos])
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
    nlinarith [W.targetStrength_pos]
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
Basic L1 triangle compiler on continuous compact profiles.
-/
theorem taperMass_add_le
    {P Q : ℝ -> ℝ}
    (hP : Continuous P) (hPc : HasCompactSupport P)
    (hQ : Continuous Q) (hQc : HasCompactSupport Q) :
    taperMass (fun u => P u + Q u)
      <= taperMass P + taperMass Q := by
  unfold taperMass
  have hPi : Integrable (fun u : ℝ => |P u|) :=
    hP.abs.integrable_of_hasCompactSupport hPc.abs
  have hQi : Integrable (fun u : ℝ => |Q u|) :=
    hQ.abs.integrable_of_hasCompactSupport hQc.abs
  have hsum :
      Integrable (fun u : ℝ => |P u + Q u|) :=
    (hP.add hQ).abs.integrable_of_hasCompactSupport (hPc.add hQc).abs
  calc
    (∫ u : ℝ, |P u + Q u|)
      <= ∫ u : ℝ, (|P u| + |Q u|) := by
        apply integral_mono hsum (hPi.add hQi)
        intro u
        exact abs_add _ _
    _ = (∫ u : ℝ, |P u|) + (∫ u : ℝ, |Q u|) := by
      rw [integral_add hPi hQi]

theorem taperMass_sub_le
    {P Q : ℝ -> ℝ}
    (hP : Continuous P) (hPc : HasCompactSupport P)
    (hQ : Continuous Q) (hQc : HasCompactSupport Q) :
    taperMass (fun u => P u - Q u)
      <= taperMass P + taperMass Q := by
  unfold taperMass
  have hPi : Integrable (fun u : ℝ => |P u|) :=
    hP.abs.integrable_of_hasCompactSupport hPc.abs
  have hQi : Integrable (fun u : ℝ => |Q u|) :=
    hQ.abs.integrable_of_hasCompactSupport hQc.abs
  have hsub :
      Integrable (fun u : ℝ => |P u - Q u|) :=
    (hP.sub hQ).abs.integrable_of_hasCompactSupport (hPc.sub hQc).abs
  calc
    (∫ u : ℝ, |P u - Q u|)
      <= ∫ u : ℝ, (|P u| + |Q u|) := by
        apply integral_mono hsub (hPi.add hQi)
        intro u
        exact abs_sub _ _
    _ = (∫ u : ℝ, |P u|) + (∫ u : ℝ, |Q u|) := by
      rw [integral_add hPi hQi]

theorem taperMass_const_mul
    (a : ℝ)
    {P : ℝ -> ℝ}
    (hP : Continuous P) (hPc : HasCompactSupport P) :
    taperMass (fun u => a * P u)
      = |a| * taperMass P := by
  unfold taperMass
  simp_rw [abs_mul]
  rw [integral_const_mul]

/--
Uniform L1 bound for the normalized four-window taper in the design corridor.

The constant is deliberately coarse:
  1 + 1 + 2/3 + 1/10 = 83/30.
-/
theorem quarticFourWindowProfile_taperMass_le_eightyThree_thirtieths
    {R lam mu : ℝ}
    (hR : 0 < R)
    (hlam0 : 0 <= lam)
    (hlam : lam <= 2/3)
    (hmu : |mu| <= 1/10) :
    taperMass (quarticFourWindowProfile R lam mu)
      <= 83/30 := by
  let b0 : ℝ -> ℝ := quantitativeSymBump 0 R
  let b1 : ℝ -> ℝ := quantitativeSymBump (Real.pi/3) R
  let b2 : ℝ -> ℝ := quantitativeSymBump (Real.pi/2) R
  let b3 : ℝ -> ℝ := quantitativeSymBump Real.pi R
  have h0c : Continuous b0 :=
    (quantitativeSymBump_contDiff (c:=0) (R:=R) hR.ne').continuous
  have h1c : Continuous b1 :=
    (quantitativeSymBump_contDiff (c:=Real.pi/3) (R:=R) hR.ne').continuous
  have h2c : Continuous b2 :=
    (quantitativeSymBump_contDiff (c:=Real.pi/2) (R:=R) hR.ne').continuous
  have h3c : Continuous b3 :=
    (quantitativeSymBump_contDiff (c:=Real.pi) (R:=R) hR.ne').continuous
  have h0k : HasCompactSupport b0 :=
    quantitativeSymBump_hasCompactSupport (c:=0) hR
  have h1k : HasCompactSupport b1 :=
    quantitativeSymBump_hasCompactSupport (c:=Real.pi/3) hR
  have h2k : HasCompactSupport b2 :=
    quantitativeSymBump_hasCompactSupport (c:=Real.pi/2) hR
  have h3k : HasCompactSupport b3 :=
    quantitativeSymBump_hasCompactSupport (c:=Real.pi) hR
  have h0m : taperMass b0 <= quarticWindowMass R := by
    simpa [b0, quarticWindowMass] using
      taperMass_quantitativeSymBump_le (c:=0) hR
  have h1m : taperMass b1 <= quarticWindowMass R := by
    simpa [b1, quarticWindowMass] using
      taperMass_quantitativeSymBump_le (c:=Real.pi/3) hR
  have h2m : taperMass b2 <= quarticWindowMass R := by
    simpa [b2, quarticWindowMass] using
      taperMass_quantitativeSymBump_le (c:=Real.pi/2) hR
  have h3m : taperMass b3 <= quarticWindowMass R := by
    simpa [b3, quarticWindowMass] using
      taperMass_quantitativeSymBump_le (c:=Real.pi) hR
  have hmasspos : 0 < quarticWindowMass R := quarticWindowMass_pos hR
  have hraw :
      taperMass (quarticFourWindowRaw R lam mu)
        <= (2 + lam + |mu|) * quarticWindowMass R := by
    -- triangle inequality on the four signed/scaled windows
    have h01 :=
      taperMass_sub_le h0c h0k h1c h1k
    let p01 : ℝ -> ℝ := fun u => b0 u - b1 u
    have hp01c : Continuous p01 := h0c.sub h1c
    have hp01k : HasCompactSupport p01 := h0k.sub h1k
    have h2scaled :
        taperMass (fun u => lam * b2 u)
          = lam * taperMass b2 := by
      rw [taperMass_const_mul lam h2c h2k, abs_of_nonneg hlam0]
    have hmuScaled :
        taperMass (fun u => mu * b3 u)
          = |mu| * taperMass b3 := by
      exact taperMass_const_mul mu h3c h3k
    have h012 :=
      taperMass_add_le hp01c hp01k
        (continuous_const.mul h2c) h2k.mul_left
    let p012 : ℝ -> ℝ :=
      fun u => p01 u + lam * b2 u
    have hp012c : Continuous p012 :=
      hp01c.add (continuous_const.mul h2c)
    have hp012k : HasCompactSupport p012 :=
      hp01k.add h2k.mul_left
    have h0123 :=
      taperMass_add_le hp012c hp012k
        (continuous_const.mul h3c) h3k.mul_left
    unfold quarticFourWindowRaw
    change taperMass
      (fun u => (b0 u - b1 u + lam*b2 u) + mu*b3 u)
      <= _ 
    calc
      taperMass (fun u => (b0 u - b1 u + lam*b2 u) + mu*b3 u)
        <= taperMass (fun u => b0 u - b1 u + lam*b2 u)
          + taperMass (fun u => mu*b3 u) := h0123
      _ <=
        (taperMass b0 + taperMass b1 + lam*taperMass b2)
          + |mu|*taperMass b3 := by
        rw [hmuScaled]
        have h012' :
            taperMass (fun u => b0 u - b1 u + lam*b2 u)
              <= taperMass b0 + taperMass b1 + lam*taperMass b2 := by
          calc
            taperMass (fun u => b0 u - b1 u + lam*b2 u)
              <= taperMass (fun u => b0 u - b1 u)
                + taperMass (fun u => lam*b2 u) := h012
            _ <= (taperMass b0 + taperMass b1)
                + lam*taperMass b2 := by
              rw [h2scaled]
              linarith
        linarith
      _ <= (2 + lam + |mu|) * quarticWindowMass R := by
        have hlamnon : 0 <= lam := hlam0
        have hmunon : 0 <= |mu| := abs_nonneg _
        nlinarith
  have hprofile :
      taperMass (quarticFourWindowProfile R lam mu)
        =
      (quarticWindowMass R)⁻¹
        * taperMass (quarticFourWindowRaw R lam mu) := by
    unfold quarticFourWindowProfile
    rw [taperMass_const_mul
      (quarticWindowMass R)⁻¹
      (quarticFourWindowRaw_continuous hR)
      (quarticFourWindowRaw_compact hR)]
    rw [abs_of_pos (inv_pos.mpr hmasspos)]
  rw [hprofile]
  have hscaled :=
    mul_le_mul_of_nonneg_left hraw (inv_nonneg.mpr hmasspos.le)
  have hcancel :
      (quarticWindowMass R)⁻¹ * quarticWindowMass R = 1 := by
    field_simp [ne_of_gt hmasspos]
  have hcoef : 2 + lam + |mu| <= 83/30 := by
    linarith
  calc
    (quarticWindowMass R)⁻¹
        * taperMass (quarticFourWindowRaw R lam mu)
      <= (quarticWindowMass R)⁻¹
          * ((2 + lam + |mu|) * quarticWindowMass R) := hscaled
    _ = 2 + lam + |mu| := by
      field_simp [ne_of_gt hmasspos]
    _ <= 83/30 := hcoef

theorem QuarticFourSignedPolePair.halfWindow_taperMass_le
    {t : ℝ} (W : QuarticFourSignedPolePair t) :
    taperMass
      (quarticFourWindowProfile W.R (1/2) W.muHalf)
      <= 83/30 := by
  have hmu :
      |W.muHalf| <= 1/10 :=
    (quarticFourAtomicMu_corridor_abs_lt_tenth
      (by norm_num) (by norm_num) W.muHalfNear).le
  exact quarticFourWindowProfile_taperMass_le_eightyThree_thirtieths
    W.Rpos (by norm_num) (by norm_num) hmu

theorem QuarticFourSignedPolePair.twoWindow_taperMass_le
    {t : ℝ} (W : QuarticFourSignedPolePair t) :
    taperMass
      (quarticFourWindowProfile W.R (2/3) W.muTwo)
      <= 83/30 := by
  have hmu :
      |W.muTwo| <= 1/10 :=
    (quarticFourAtomicMu_corridor_abs_lt_tenth
      (by norm_num) (by norm_num) W.muTwoNear).le
  exact quarticFourWindowProfile_taperMass_le_eightyThree_thirtieths
    W.Rpos (by norm_num) (by norm_num) hmu

/--
At zero hyperbolic parameter, every cosine response is bounded by the L1 mass
of the underlying taper.
-/
theorem abs_evenResp_zero_le_taperMass
    {g : ℝ -> ℝ}
    (hg : Continuous g)
    (hgc : HasCompactSupport g)
    (s : ℝ) :
    |Zeta23Bridge.LiteralWeilParityBalance.evenResp g 0 s|
      <= taperMass g := by
  unfold Zeta23Bridge.LiteralWeilParityBalance.evenResp taperMass
  simp only [zero_mul, Real.cosh_zero, one_mul]
  have hi :
      Integrable (fun u : ℝ => g u * Real.cos (s*u)) :=
    (hg.mul (by fun_prop)).integrable_of_hasCompactSupport hgc.mul_right
  have habsi : Integrable (fun u : ℝ => |g u|) :=
    hg.abs.integrable_of_hasCompactSupport hgc.abs
  calc
    |∫ u : ℝ, g u * Real.cos (s*u)|
      <= ∫ u : ℝ, |g u * Real.cos (s*u)| :=
        abs_integral_le_integral_abs
    _ <= ∫ u : ℝ, |g u| := by
      apply integral_mono hi.abs habsi
      intro u
      rw [abs_mul]
      have hc : |Real.cos (s*u)| <= 1 := abs_cos_le_one _
      nlinarith [abs_nonneg (g u)]

/--
Generic L1 compiler for the exact two-radius physical projective profile.

If ||g||_1 <= M, then
  ||4 g B_r||_1 <= 8 M^2.

No positivity of g is needed.
-/
theorem taperMass_genericProjectivePhysicalProfile_le
    {g : ℝ -> ℝ} {r M : ℝ}
    (hg : Continuous g)
    (hgc : HasCompactSupport g)
    (hM : 0 <= M)
    (hmass : taperMass g <= M) :
    taperMass (genericProjectivePhysicalProfile g r)
      <= 8 * M^2 := by
  have hAr :
      |Zeta23Bridge.LiteralWeilParityBalance.evenResp g 0 r|
        <= M :=
    (abs_evenResp_zero_le_taperMass hg hgc r).trans hmass
  have hA2r :
      |Zeta23Bridge.LiteralWeilParityBalance.evenResp g 0 (2*r)|
        <= M :=
    (abs_evenResp_zero_le_taperMass hg hgc (2*r)).trans hmass
  have hgi : Integrable (fun u : ℝ => |g u|) :=
    hg.abs.integrable_of_hasCompactSupport hgc.abs
  have hproj :
      Integrable
        (fun u : ℝ => |genericProjectivePhysicalProfile g r u|) :=
    (genericProjectivePhysicalProfile_continuous hg r).abs
      .integrable_of_hasCompactSupport
        (genericProjectivePhysicalProfile_compact hgc r).abs
  unfold taperMass
  calc
    (∫ u : ℝ, |genericProjectivePhysicalProfile g r u|)
      <= ∫ u : ℝ, (8*M) * |g u| := by
        apply integral_mono hproj (hgi.const_mul (8*M))
        intro u
        unfold genericProjectivePhysicalProfile
          Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector.twoRadiusBracket
        rw [abs_mul, abs_mul]
        have hc1 : |Real.cos (2*r*u)| <= 1 := abs_cos_le_one _
        have hc2 : |Real.cos (r*u)| <= 1 := abs_cos_le_one _
        have hb :
            |Zeta23Bridge.LiteralWeilParityBalance.evenResp g 0 r
                * Real.cos (2*r*u)
              -
              Zeta23Bridge.LiteralWeilParityBalance.evenResp g 0 (2*r)
                * Real.cos (r*u)|
              <= 2*M := by
          calc
            |_ - _|
              <=
            |Zeta23Bridge.LiteralWeilParityBalance.evenResp g 0 r
                * Real.cos (2*r*u)|
              +
            |Zeta23Bridge.LiteralWeilParityBalance.evenResp g 0 (2*r)
                * Real.cos (r*u)| := abs_sub _ _
            _ <= M + M := by
              rw [abs_mul, abs_mul]
              constructor <;> nlinarith [abs_nonneg
                (Zeta23Bridge.LiteralWeilParityBalance.evenResp g 0 r),
                abs_nonneg
                (Zeta23Bridge.LiteralWeilParityBalance.evenResp g 0 (2*r))]
            _ = 2*M := by ring
        norm_num
        nlinarith [abs_nonneg (g u)]
    _ = (8*M) * taperMass g := by
      rw [integral_const_mul]
      rfl
    _ <= (8*M) * M := by
      exact mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = 8*M^2 := by ring

def quarticFourProjectiveMassBound : ℝ :=
  8 * (83/30 : ℝ)^2

theorem QuarticFourSignedPolePair.halfProjective_taperMass_le
    {t : ℝ} (W : QuarticFourSignedPolePair t) :
    taperMass
      (quarticFourNormalizedProjectiveProfile W.R (1/2) W.muHalf)
      <= quarticFourProjectiveMassBound := by
  unfold quarticFourNormalizedProjectiveProfile
    quarticFourProjectiveMassBound
  exact taperMass_genericProjectivePhysicalProfile_le
    (quarticFourWindowProfile_continuous W.Rpos)
    (quarticFourWindowProfile_compact W.Rpos)
    (by norm_num)
    W.halfWindow_taperMass_le

theorem QuarticFourSignedPolePair.twoProjective_taperMass_le
    {t : ℝ} (W : QuarticFourSignedPolePair t) :
    taperMass
      (quarticFourNormalizedProjectiveProfile W.R (2/3) W.muTwo)
      <= quarticFourProjectiveMassBound := by
  unfold quarticFourNormalizedProjectiveProfile
    quarticFourProjectiveMassBound
  exact taperMass_genericProjectivePhysicalProfile_le
    (quarticFourWindowProfile_continuous W.Rpos)
    (quarticFourWindowProfile_compact W.Rpos)
    (by norm_num)
    W.twoWindow_taperMass_le

/--
On the four-window support and for t>=200, the normalized pole weight is
uniformly bounded by cosh(1).  The bound is intentionally very coarse.
-/
theorem quarticFourNormalizedPoleWeight_abs_le_cosh_one
    {R t c u : ℝ}
    (hR : R < 1)
    (ht : 200 <= t)
    (hu : |u| < Real.pi + R) :
    |quarticFourNormalizedPoleWeight t c u|
      <= Real.cosh 1 := by
  have ht0 : 0 < t := by linarith
  have hpi : Real.pi < 4 := Real.pi_lt_four
  have hu5 : |u| < 5 := by linarith
  have hxnon : 0 <= |8*u/t| := abs_nonneg _
  have hx : |8*u/t| <= 1 := by
    rw [abs_div, abs_mul, abs_of_pos ht0, abs_of_nonneg (by norm_num : (0:ℝ) <= 8)]
    rw [div_le_iff₀ ht0]
    nlinarith
  have hcosh :
      Real.cosh (8*u/t) <= Real.cosh 1 := by
    exact (Real.cosh_le_cosh).2 (by simpa using hx)
  have hc1 : |Real.cos (16*u)| <= 1 := abs_cos_le_one _
  have hc2 : |Real.cos (c*u)| <= 1 := abs_cos_le_one _
  unfold quarticFourNormalizedPoleWeight
  rw [abs_mul, abs_mul, abs_of_pos (Real.cosh_pos _)]
  have hcosh0 : 0 <= Real.cosh (8*u/t) := (Real.cosh_pos _).le
  have hone : 0 <= Real.cosh 1 := (Real.cosh_pos 1).le
  nlinarith

/--
Pairing against the on-line cosine weight is controlled by taper mass.
-/
theorem quarticFourWindowPairing_onLine_abs_le_taperMass
    {R lam mu c : ℝ}
    (hR : 0 < R) :
    |quarticFourWindowPairing R lam mu
        (quarticFourNormalizedOnLineWeight c)|
      <= taperMass (quarticFourWindowProfile R lam mu) := by
  have hpair :=
    quarticFourWindowProfile_pairing_eq
      (lam:=lam) (mu:=mu) hR
      (quarticFourNormalizedOnLineWeight_continuous c)
  rw [← hpair]
  have hi :
      Integrable
        (fun u : ℝ =>
          quarticFourWindowProfile R lam mu u
            * quarticFourNormalizedOnLineWeight c u) :=
    ((quarticFourWindowProfile_continuous hR).mul
      (quarticFourNormalizedOnLineWeight_continuous c))
      .integrable_of_hasCompactSupport
        (quarticFourWindowProfile_compact hR).mul_right
  have hm :
      Integrable
        (fun u : ℝ => |quarticFourWindowProfile R lam mu u|) :=
    (quarticFourWindowProfile_continuous hR).abs
      .integrable_of_hasCompactSupport
        (quarticFourWindowProfile_compact hR).abs
  unfold taperMass
  calc
    |∫ u : ℝ,
        quarticFourWindowProfile R lam mu u
          * quarticFourNormalizedOnLineWeight c u|
      <=
    ∫ u : ℝ,
      |quarticFourWindowProfile R lam mu u
        * quarticFourNormalizedOnLineWeight c u| :=
      abs_integral_le_integral_abs
    _ <=
    ∫ u : ℝ, |quarticFourWindowProfile R lam mu u| := by
      apply integral_mono hi.abs hm
      intro u
      unfold quarticFourNormalizedOnLineWeight
      rw [abs_mul]
      have hc : |Real.cos (c*u)| <= 1 := abs_cos_le_one _
      nlinarith [abs_nonneg (quarticFourWindowProfile R lam mu u)]

/--
Pairing against the high-t pole weight is controlled by cosh(1) times taper
mass.
-/
theorem quarticFourWindowPairing_pole_abs_le_cosh_one_mul_taperMass
    {R lam mu t c : ℝ}
    (hR : 0 < R)
    (hRone : R < 1)
    (ht : 200 <= t) :
    |quarticFourWindowPairing R lam mu
        (quarticFourNormalizedPoleWeight t c)|
      <= Real.cosh 1 * taperMass (quarticFourWindowProfile R lam mu) := by
  have hpair :=
    quarticFourWindowProfile_pairing_eq
      (lam:=lam) (mu:=mu) hR
      (quarticFourNormalizedPoleWeight_continuous t c)
  rw [← hpair]
  have hi :
      Integrable
        (fun u : ℝ =>
          quarticFourWindowProfile R lam mu u
            * quarticFourNormalizedPoleWeight t c u) :=
    ((quarticFourWindowProfile_continuous hR).mul
      (quarticFourNormalizedPoleWeight_continuous t c))
      .integrable_of_hasCompactSupport
        (quarticFourWindowProfile_compact hR).mul_right
  have hm :
      Integrable
        (fun u : ℝ =>
          Real.cosh 1 * |quarticFourWindowProfile R lam mu u|) :=
    ((quarticFourWindowProfile_continuous hR).abs
      .integrable_of_hasCompactSupport
        (quarticFourWindowProfile_compact hR).abs).const_mul _
  calc
    |∫ u : ℝ,
        quarticFourWindowProfile R lam mu u
          * quarticFourNormalizedPoleWeight t c u|
      <=
    ∫ u : ℝ,
      |quarticFourWindowProfile R lam mu u
        * quarticFourNormalizedPoleWeight t c u| :=
      abs_integral_le_integral_abs
    _ <=
    ∫ u : ℝ,
      Real.cosh 1 * |quarticFourWindowProfile R lam mu u| := by
      apply integral_mono hi.abs hm
      intro u
      by_cases hz : quarticFourWindowProfile R lam mu u = 0
      · simp [hz, (Real.cosh_pos 1).le]
      · have hs :=
          quarticFourWindowProfile_support_abs_lt hR hz
        have hw :=
          quarticFourNormalizedPoleWeight_abs_le_cosh_one
            hRone ht hs
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left hw (abs_nonneg _)
    _ =
      Real.cosh 1
        * taperMass (quarticFourWindowProfile R lam mu) := by
      rw [integral_const_mul]
      rfl

def quarticFourSmoothPoleBound : ℝ :=
  2 * Real.cosh 1 * (83/30 : ℝ)^2

theorem QuarticFourSignedPolePair.poleHalf_abs_le
    {t : ℝ} (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t) :
    |W.poleHalf| <= quarticFourSmoothPoleBound := by
  have hp1 :=
    quarticFourWindowPairing_pole_abs_le_cosh_one_mul_taperMass
      W.Rpos W.RltOne ht
      (lam:=(1/2 : ℝ)) (mu:=W.muHalf) (c:=1)
  have ho2 :=
    quarticFourWindowPairing_onLine_abs_le_taperMass
      W.Rpos (lam:=(1/2 : ℝ)) (mu:=W.muHalf) (c:=2)
  have hp2 :=
    quarticFourWindowPairing_pole_abs_le_cosh_one_mul_taperMass
      W.Rpos W.RltOne ht
      (lam:=(1/2 : ℝ)) (mu:=W.muHalf) (c:=2)
  have ho1 :=
    quarticFourWindowPairing_onLine_abs_le_taperMass
      W.Rpos (lam:=(1/2 : ℝ)) (mu:=W.muHalf) (c:=1)
  have hm := W.halfWindow_taperMass_le
  unfold QuarticFourSignedPolePair.poleHalf
    quarticFourSmoothFinitePoleResidual
    quarticFourSmoothPoleBound
  calc
    |_ * _ - _ * _|
      <= |_ * _| + |_ * _| := abs_sub _ _
    _ =
      |_ | * |_ | + |_ | * |_ | := by
        rw [abs_mul, abs_mul]
    _ <=
      (Real.cosh 1 * (83/30)) * (83/30)
        + (Real.cosh 1 * (83/30)) * (83/30) := by
      have hC : 0 <= Real.cosh 1 := (Real.cosh_pos 1).le
      nlinarith [taperMass_nonneg
        (quarticFourWindowProfile W.R (1/2) W.muHalf)]
    _ = 2 * Real.cosh 1 * (83/30)^2 := by ring

theorem QuarticFourSignedPolePair.poleTwo_abs_le
    {t : ℝ} (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t) :
    |W.poleTwo| <= quarticFourSmoothPoleBound := by
  have hp1 :=
    quarticFourWindowPairing_pole_abs_le_cosh_one_mul_taperMass
      W.Rpos W.RltOne ht
      (lam:=(2/3 : ℝ)) (mu:=W.muTwo) (c:=1)
  have ho2 :=
    quarticFourWindowPairing_onLine_abs_le_taperMass
      W.Rpos (lam:=(2/3 : ℝ)) (mu:=W.muTwo) (c:=2)
  have hp2 :=
    quarticFourWindowPairing_pole_abs_le_cosh_one_mul_taperMass
      W.Rpos W.RltOne ht
      (lam:=(2/3 : ℝ)) (mu:=W.muTwo) (c:=2)
  have ho1 :=
    quarticFourWindowPairing_onLine_abs_le_taperMass
      W.Rpos (lam:=(2/3 : ℝ)) (mu:=W.muTwo) (c:=1)
  have hm := W.twoWindow_taperMass_le
  unfold QuarticFourSignedPolePair.poleTwo
    quarticFourSmoothFinitePoleResidual
    quarticFourSmoothPoleBound
  calc
    |_ * _ - _ * _|
      <= |_ * _| + |_ * _| := abs_sub _ _
    _ =
      |_ | * |_ | + |_ | * |_ | := by
        rw [abs_mul, abs_mul]
    _ <=
      (Real.cosh 1 * (83/30)) * (83/30)
        + (Real.cosh 1 * (83/30)) * (83/30) := by
      have hC : 0 <= Real.cosh 1 := (Real.cosh_pos 1).le
      nlinarith [taperMass_nonneg
        (quarticFourWindowProfile W.R (2/3) W.muTwo)]
    _ = 2 * Real.cosh 1 * (83/30)^2 := by ring

/--
Combined-profile mass compiler from any coarse uniform bound on the two smooth
pole coordinates.
-/
theorem QuarticFourSignedPolePair.combinedProfile_taperMass_le_of_pole_bound
    {t B : ℝ}
    (W : QuarticFourSignedPolePair t)
    (hB : 0 <= B)
    (hhalf : |W.poleHalf| <= B)
    (htwo : |W.poleTwo| <= B) :
    taperMass
      (quarticFourSignedPoleCombinedProfile
        W.R W.muHalf W.muTwo t)
      <= 2 * B * quarticFourProjectiveMassBound := by
  let P1 :=
    quarticFourNormalizedProjectiveProfile W.R (1/2) W.muHalf
  let P2 :=
    quarticFourNormalizedProjectiveProfile W.R (2/3) W.muTwo
  have hP1c : Continuous P1 :=
    quarticFourNormalizedProjectiveProfile_continuous W.Rpos
  have hP2c : Continuous P2 :=
    quarticFourNormalizedProjectiveProfile_continuous W.Rpos
  have hP1k : HasCompactSupport P1 :=
    quarticFourNormalizedProjectiveProfile_compact W.Rpos
  have hP2k : HasCompactSupport P2 :=
    quarticFourNormalizedProjectiveProfile_compact W.Rpos
  have hlin :=
    taperMass_add_le
      (continuous_const.mul hP1c) hP1k.mul_left
      (continuous_const.mul hP2c) hP2k.mul_left
  have hscale1 :=
    taperMass_const_mul W.poleTwo hP1c hP1k
  have hscale2 :=
    taperMass_const_mul (-W.poleHalf) hP2c hP2k
  unfold quarticFourSignedPoleCombinedProfile profileLinearCombination
  change taperMass
      (fun u => W.poleTwo * P1 u + (-W.poleHalf) * P2 u)
      <= _
  calc
    taperMass
        (fun u => W.poleTwo * P1 u + (-W.poleHalf) * P2 u)
      <= taperMass (fun u => W.poleTwo * P1 u)
        + taperMass (fun u => (-W.poleHalf) * P2 u) := hlin
    _ =
      |W.poleTwo| * taperMass P1
        + |W.poleHalf| * taperMass P2 := by
      rw [hscale1, hscale2, abs_neg]
    _ <=
      B * quarticFourProjectiveMassBound
        + B * quarticFourProjectiveMassBound := by
      have h1 := W.halfProjective_taperMass_le
      have h2 := W.twoProjective_taperMass_le
      nlinarith [taperMass_nonneg P1, taperMass_nonneg P2]
    _ = 2 * B * quarticFourProjectiveMassBound := by ring

/--
The projective physical multiplier does not enlarge the four-window support.
-/
theorem quarticFourNormalizedProjectiveProfile_support_abs_lt
    {R lam mu u : ℝ}
    (hR : 0 < R)
    (hu :
      quarticFourNormalizedProjectiveProfile R lam mu u ≠ 0) :
    |u| < Real.pi + R := by
  have hg :
      quarticFourWindowProfile R lam mu u ≠ 0 := by
    intro hz
    apply hu
    unfold quarticFourNormalizedProjectiveProfile
      genericProjectivePhysicalProfile
    rw [hz]
    ring
  exact quarticFourWindowProfile_support_abs_lt hR hg

/--
Every signed combined profile carried by a witness is supported in
|u| < pi+1.
-/
theorem QuarticFourSignedPolePair.combinedProfile_support_abs_lt_pi_add_one
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    {u : ℝ}
    (hu :
      quarticFourSignedPoleCombinedProfile
        W.R W.muHalf W.muTwo t u ≠ 0) :
    |u| < Real.pi + 1 := by
  have hcomponent :
      quarticFourNormalizedProjectiveProfile
          W.R (1/2) W.muHalf u ≠ 0
      ∨
      quarticFourNormalizedProjectiveProfile
          W.R (2/3) W.muTwo u ≠ 0 := by
    by_contra h
    push_neg at h
    apply hu
    unfold quarticFourSignedPoleCombinedProfile
      profileLinearCombination
    rw [h.1, h.2]
    ring
  cases hcomponent with
  | inl hhalf =>
      have hs :=
        quarticFourNormalizedProjectiveProfile_support_abs_lt
          W.Rpos hhalf
      linarith
  | inr htwo =>
      have hs :=
        quarticFourNormalizedProjectiveProfile_support_abs_lt
          W.Rpos htwo
      linarith

theorem QuarticFourSignedPolePair.combinedProfile_support_abs_le_pi_add_one
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (u : ℝ)
    (hu :
      quarticFourSignedPoleCombinedProfile
        W.R W.muHalf W.muTwo t u ≠ 0) :
    |u| <= Real.pi + 1 :=
  (W.combinedProfile_support_abs_lt_pi_add_one hu).le

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


/--
After the support theorem, the sole remaining input for K is the L1 mass of
the exact signed combined profile.
-/
theorem QuarticFourSignedPolePair.fourthLipschitz_le_of_combined_mass
    {t M : ℝ}
    (W : QuarticFourSignedPolePair t)
    (hmass :
      Zeta23Bridge.LiteralWeilProjectiveStripConstant.taperMass
        (quarticFourSignedPoleCombinedProfile
          W.R W.muHalf W.muTwo t)
        <= M) :
    W.fourthLipschitz
      <= M * Real.cosh (Real.pi + 1) * (Real.pi + 1)^5 := by
  exact W.fourthLipschitz_le_of_support_mass
    (by positivity)
    W.combinedProfile_support_abs_le_pi_add_one
    hmass

/--
Preferred final G1 norm obligation after support and target strength have been
compiled away.
-/
def quarticSignedPole_constructedWitness_uniform_combinedMass
    (M0 : ℝ) : Prop :=
  ∀ {t : ℝ}, 200 <= t ->
    ∃ W : QuarticFourSignedPolePair t,
      quarticSignedPoleStrengthFloor <= W.targetStrength
      ∧
      Zeta23Bridge.LiteralWeilProjectiveStripConstant.taperMass
        (quarticFourSignedPoleCombinedProfile
          W.R W.muHalf W.muTwo t)
        <= M0

theorem quarticSignedPole_uniform_combinedMass_to_uniform_K
    {M0 : ℝ}
    (hmass :
      quarticSignedPole_constructedWitness_uniform_combinedMass M0) :
    quarticSignedPole_constructedWitness_uniform_K
      (M0 * Real.cosh (Real.pi + 1) * (Real.pi + 1)^5) := by
  intro t ht
  obtain ⟨W,hS,hM⟩ := hmass ht
  refine ⟨W,hS,?_⟩
  exact W.fourthLipschitz_le_of_combined_mass hM


/--
Explicit uniform L1 bound for the exact signed combined profile.
-/
def quarticFourCombinedProfileMassBound : ℝ :=
  2 * quarticFourSmoothPoleBound * quarticFourProjectiveMassBound

theorem QuarticFourSignedPolePair.combinedProfile_taperMass_le_explicit
    {t : ℝ} (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t) :
    taperMass
      (quarticFourSignedPoleCombinedProfile
        W.R W.muHalf W.muTwo t)
      <= quarticFourCombinedProfileMassBound := by
  unfold quarticFourCombinedProfileMassBound
  exact W.combinedProfile_taperMass_le_of_pole_bound
    (by
      unfold quarticFourSmoothPoleBound
      positivity)
    (W.poleHalf_abs_le ht)
    (W.poleTwo_abs_le ht)

/--
A completely explicit high-t uniform bound for K(W).
-/
def quarticSignedPoleExplicitK0 : ℝ :=
  quarticFourCombinedProfileMassBound
    * Real.cosh (Real.pi + 1)
    * (Real.pi + 1)^5

theorem quarticSignedPoleExplicitK0_nonneg :
    0 <= quarticSignedPoleExplicitK0 := by
  unfold quarticSignedPoleExplicitK0
    quarticFourCombinedProfileMassBound
    quarticFourSmoothPoleBound
    quarticFourProjectiveMassBound
  positivity

theorem QuarticFourSignedPolePair.fourthLipschitz_le_explicitK0
    {t : ℝ} (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t) :
    W.fourthLipschitz <= quarticSignedPoleExplicitK0 := by
  unfold quarticSignedPoleExplicitK0
  exact W.fourthLipschitz_le_of_combined_mass
    (W.combinedProfile_taperMass_le_explicit ht)

/--
The preferred existential G1 K-source is now compiler-owned from the
floor-certified constructor plus the explicit uniform norm bound.
-/
theorem quarticSignedPole_constructedWitness_uniform_K_explicit :
    quarticSignedPole_constructedWitness_uniform_K
      quarticSignedPoleExplicitK0 := by
  intro t ht
  obtain ⟨W,hS⟩ :=
    exists_quarticFourSignedPolePair_strengthFloor ht
  refine ⟨W,hS,?_⟩
  exact W.fourthLipschitz_le_explicitK0 ht

theorem quarticSignedPole_goodWitness_uniform_K_explicit :
    quarticSignedPole_goodWitness_uniform_K
      200 quarticSignedPoleExplicitK0 :=
  quarticSignedPole_constructedWitness_uniform_K_to_goodWitness
    quarticSignedPole_constructedWitness_uniform_K_explicit

/--
The single scalar threshold left by G1 after all witness/norm bookkeeping.
-/
def quarticSignedPoleQuantitativeThreshold : ℝ :=
  4 * (quarticSignedPoleExplicitK0 + 1)
    / quarticSignedPoleStrengthFloor

theorem quarticSignedPoleQuantitativeThreshold_pos :
    0 < quarticSignedPoleQuantitativeThreshold := by
  unfold quarticSignedPoleQuantitativeThreshold
  have hK := quarticSignedPoleExplicitK0_nonneg
  have hS := quarticSignedPoleStrengthFloor_pos
  positivity

theorem quarticSignedPole_scalar_threshold_of_gt
    {t : ℝ}
    (ht : quarticSignedPoleQuantitativeThreshold < t) :
    4 * (quarticSignedPoleExplicitK0 + 1) / t
      < quarticSignedPoleStrengthFloor := by
  have ht0 : 0 < t :=
    lt_trans quarticSignedPoleQuantitativeThreshold_pos ht
  have hS := quarticSignedPoleStrengthFloor_pos
  unfold quarticSignedPoleQuantitativeThreshold at ht
  rw [div_lt_iff₀ hS] at ht
  rw [div_lt_iff₀ ht0]
  nlinarith

/--
G1 above the explicit quantitative threshold.

At this point no profile-analysis theorem remains as an input.
-/
theorem exists_quarticSignedPolePair_quantitativeBand_of_threshold
    {t : ℝ}
    (ht200 : 200 <= t)
    (htQ : quarticSignedPoleQuantitativeThreshold < t) :
    ∃ W : QuarticFourSignedPolePair t,
      quarticSignedPoleStrengthFloor <= W.targetStrength
      ∧ 8/t < W.quantitativeTargetRadius := by
  have ht8 : 8 < t := by linarith
  exact exists_quarticSignedPolePair_quantitativeBand_covers_strip
    ht200 ht8 quarticSignedPoleExplicitK0_nonneg
    quarticSignedPole_goodWitness_uniform_K_explicit
    (quarticSignedPole_scalar_threshold_of_gt htQ)


/--
The published Platt--Trudgian verified-height ceiling used by the RH low/high
partition.
-/
def quarticPlattTrudgianCutoff : ℝ :=
  3000175332800

theorem quarticPlattTrudgianCutoff_gt_twoHundred :
    200 < quarticPlattTrudgianCutoff := by
  norm_num [quarticPlattTrudgianCutoff]

/--
The final scalar G1 payment.

This is intentionally isolated from the analytic construction.  Once certified,
every Clay-high ordinate automatically lies above the explicit quartic
quantitative threshold.
-/
def quarticSignedPoleThresholdBelowPlattTrudgian : Prop :=
  quarticSignedPoleQuantitativeThreshold
    < quarticPlattTrudgianCutoff

theorem exists_quarticSignedPolePair_quantitativeBand_of_clayHigh
    {t : ℝ}
    (hQTPT : quarticSignedPoleThresholdBelowPlattTrudgian)
    (htPT : quarticPlattTrudgianCutoff < t) :
    ∃ W : QuarticFourSignedPolePair t,
      quarticSignedPoleStrengthFloor <= W.targetStrength
      ∧ 8/t < W.quantitativeTargetRadius := by
  have ht200 : 200 <= t := by
    have h200 := quarticPlattTrudgianCutoff_gt_twoHundred
    linarith
  have htQ : quarticSignedPoleQuantitativeThreshold < t := by
    exact lt_trans hQTPT htPT
  exact exists_quarticSignedPolePair_quantitativeBand_of_threshold
    ht200 htQ


/-!
## Certified scalar closure of G1

The following proof deliberately uses very coarse bounds.  No decimal
approximation to T_Q is part of the theorem.
-/

theorem quarticSignedPole_cosh_one_lt_two :
    Real.cosh 1 < 2 := by
  rw [Real.cosh_eq]
  have hpos := Real.exp_one_lt_three
  have hneg : Real.exp (-1) < 1 := by
    exact Real.exp_lt_one_iff.mpr (by norm_num)
  linarith

theorem quarticSignedPole_exp_five_lt_243 :
    Real.exp 5 < 243 := by
  have hpow :
      Real.exp 1 ^ (5 : ℕ) < (3 : ℝ)^5 :=
    pow_lt_pow_left₀ Real.exp_one_lt_three
      (Real.exp_pos 1).le (by norm_num)
  have heq : Real.exp 5 = Real.exp 1 ^ (5 : ℕ) := by
    rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num,
      Real.exp_nat_mul]
  rw [heq]
  norm_num at hpow ⊢
  exact hpow

theorem quarticSignedPole_cosh_pi_add_one_lt_243 :
    Real.cosh (Real.pi + 1) < 243 := by
  have hx0 : 0 < Real.pi + 1 := by positivity
  have hx5 : Real.pi + 1 < 5 := by
    linarith [Real.pi_lt_four]
  have hpos :
      Real.exp (Real.pi + 1) < Real.exp 5 :=
    Real.exp_strictMono hx5
  have hneg :
      Real.exp (-(Real.pi + 1))
        < Real.exp (Real.pi + 1) := by
    apply Real.exp_strictMono
    linarith
  rw [Real.cosh_eq]
  have h5 := quarticSignedPole_exp_five_lt_243
  linarith

theorem quarticFourProjectiveMassBound_lt_72 :
    quarticFourProjectiveMassBound < 72 := by
  unfold quarticFourProjectiveMassBound
  norm_num

theorem quarticFourSmoothPoleBound_lt_36 :
    quarticFourSmoothPoleBound < 36 := by
  unfold quarticFourSmoothPoleBound
  have hc := quarticSignedPole_cosh_one_lt_two
  norm_num at ⊢
  nlinarith

theorem quarticFourCombinedProfileMassBound_lt_5184 :
    quarticFourCombinedProfileMassBound < 5184 := by
  unfold quarticFourCombinedProfileMassBound
  have hs := quarticFourSmoothPoleBound_lt_36
  have hp := quarticFourProjectiveMassBound_lt_72
  have hs0 : 0 <= quarticFourSmoothPoleBound := by
    unfold quarticFourSmoothPoleBound
    positivity
  have hp0 : 0 <= quarticFourProjectiveMassBound := by
    unfold quarticFourProjectiveMassBound
    positivity
  calc
    2 * quarticFourSmoothPoleBound * quarticFourProjectiveMassBound
      < 2 * 36 * quarticFourProjectiveMassBound := by
        gcongr
    _ < 2 * 36 * 72 := by
        gcongr
    _ = 5184 := by norm_num

theorem quarticSignedPoleExplicitK0_lt_four_billion :
    quarticSignedPoleExplicitK0 < 4000000000 := by
  unfold quarticSignedPoleExplicitK0
  have hm := quarticFourCombinedProfileMassBound_lt_5184
  have hc := quarticSignedPole_cosh_pi_add_one_lt_243
  have hp : (Real.pi + 1)^5 < (5 : ℝ)^5 :=
    pow_lt_pow_left₀
      (by linarith [Real.pi_lt_four])
      (by positivity)
      (by norm_num)
  have hm0 : 0 <= quarticFourCombinedProfileMassBound := by
    unfold quarticFourCombinedProfileMassBound
      quarticFourSmoothPoleBound
      quarticFourProjectiveMassBound
    positivity
  have hc0 : 0 <= Real.cosh (Real.pi + 1) :=
    (Real.cosh_pos _).le
  calc
    quarticFourCombinedProfileMassBound
        * Real.cosh (Real.pi + 1)
        * (Real.pi + 1)^5
      < 5184 * 243 * (5 : ℝ)^5 := by
        gcongr
    _ < 4000000000 := by norm_num

theorem quarticSignedPoleStrengthFloor_gt_one_third :
    (1/3 : ℝ) < quarticSignedPoleStrengthFloor := by
  unfold quarticSignedPoleStrengthFloor
  have hp4 :
      (3 : ℝ)^4 < Real.pi^4 :=
    pow_lt_pow_left₀ Real.pi_gt_three
      (by norm_num) (by norm_num)
  norm_num at hp4 ⊢
  nlinarith

theorem quarticSignedPoleQuantitativeThreshold_lt_fifty_billion :
    quarticSignedPoleQuantitativeThreshold < 50000000000 := by
  unfold quarticSignedPoleQuantitativeThreshold
  rw [div_lt_iff₀ quarticSignedPoleStrengthFloor_pos]
  have hK := quarticSignedPoleExplicitK0_lt_four_billion
  have hS := quarticSignedPoleStrengthFloor_gt_one_third
  nlinarith

theorem quarticSignedPoleThresholdBelowPlattTrudgian_proved :
    quarticSignedPoleThresholdBelowPlattTrudgian := by
  unfold quarticSignedPoleThresholdBelowPlattTrudgian
    quarticPlattTrudgianCutoff
  exact quarticSignedPoleQuantitativeThreshold_lt_fifty_billion.trans
    (by norm_num)

/--
Clay-high quantitative-band witness with no remaining G1 hypothesis.
-/
theorem exists_quarticSignedPolePair_band_of_above_PT
    {t : ℝ}
    (htPT : quarticPlattTrudgianCutoff < t) :
    ∃ W : QuarticFourSignedPolePair t,
      quarticSignedPoleStrengthFloor <= W.targetStrength
      ∧ 8/t < W.quantitativeTargetRadius := by
  exact exists_quarticSignedPolePair_quantitativeBand_of_clayHigh
    quarticSignedPoleThresholdBelowPlattTrudgian_proved htPT

end Synthesis
