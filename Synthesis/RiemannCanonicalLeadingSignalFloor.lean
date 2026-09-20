import Synthesis.RiemannQuantitativeCanonicalTaper
import Synthesis.RiemannSmoothNormalizedWindow
import Zeta23Bridge.LiteralWeilLeadingCoefficientCovariance
import Zeta23Bridge.LiteralWeilWindowRatioSeparation

/-!
# Explicit leading-coefficient floor for the canonical pole-killing taper

The canonical high taper is

  g_t = inner_t + lambda_t * outer_t,

with lambda_t > 0.  Both raw symmetric bumps are C^2 nonnegative modulus-window
tapers, with

  inner: [c_in-R, c_in+R],
  outer: [c_out-R, c_out+R],

and the two windows are strictly separated for t > 0.

For every positive horizontal height a, the cross covariance is bounded below
by the literal window floor, while the two self covariances are nonnegative.
Therefore the same canonical taper that kills the pole channel satisfies

  targetLeadingCoeff(g_t,a)
    >= (3/2) lambda_t
       * (outerLo^2-innerHi^2)
       * coshDiff a innerHi outerLo
       * mass(inner_t) * mass(outer_t)
    > 0.

This is a same-object, radius-free signal lower bound on the actual GateData
taper, not a surrogate window family.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

open Zeta23Bridge.LiteralWeilWindowRatioSeparation
open Zeta23Bridge.LiteralWeilTargetDefectLeadingCoefficient
open Zeta23Bridge.LiteralWeilLeadingCoefficientCovariance
open Zeta23Bridge.CoshWindowSeparation

def canonicalInnerLo (t : ℝ) : ℝ :=
  quantitativeTaperInnerCenter t - quantitativeTaperR t

def canonicalInnerHi (t : ℝ) : ℝ :=
  quantitativeTaperInnerCenter t + quantitativeTaperR t

def canonicalOuterLo (t : ℝ) : ℝ :=
  quantitativeTaperOuterCenter t - quantitativeTaperR t

def canonicalOuterHi (t : ℝ) : ℝ :=
  quantitativeTaperOuterCenter t + quantitativeTaperR t

def canonicalCrossSignalFloor (t a : ℝ) : ℝ :=
  (3 / 2 : ℝ) * quantitativeLambda t
    * ((canonicalOuterLo t) ^ 2 - (canonicalInnerHi t) ^ 2)
    * coshDiff a (canonicalInnerHi t) (canonicalOuterLo t)
    * ((∫ u : ℝ, quantitativeInnerBump t u)
      * ∫ u : ℝ, quantitativeOuterBump t u)

theorem canonical_window_geometry
    {t : ℝ} (ht : 0 < t) :
    0 < canonicalInnerLo t
      ∧ canonicalInnerLo t <= canonicalInnerHi t
      ∧ canonicalInnerHi t < canonicalOuterLo t := by
  unfold canonicalInnerLo canonicalInnerHi canonicalOuterLo
    quantitativeTaperInnerCenter quantitativeTaperOuterCenter quantitativeTaperR
  have hpi := Real.pi_pos
  constructor
  · field_simp [ne_of_gt ht]
    nlinarith
  constructor
  · field_simp [ne_of_gt ht]
    nlinarith
  · field_simp [ne_of_gt ht]
    nlinarith

theorem canonical_inner_windowTaper
    {t : ℝ} (ht : 0 < t) :
    WindowTaper (quantitativeInnerBump t)
      (canonicalInnerLo t) (canonicalInnerHi t) := by
  unfold quantitativeInnerBump
  change WindowTaper
    (smoothWindowRaw (quantitativeTaperInnerCenter t) (quantitativeTaperR t))
    (canonicalInnerLo t) (canonicalInnerHi t)
  have hR : 0 < quantitativeTaperR t := quantitativeTaperR_pos ht
  have hgeom := canonical_window_geometry ht
  unfold canonicalInnerLo canonicalInnerHi
  exact smoothWindowRaw_windowTaper hgeom.1 hR

theorem canonical_outer_windowTaper
    {t : ℝ} (ht : 0 < t) :
    WindowTaper (quantitativeOuterBump t)
      (canonicalOuterLo t) (canonicalOuterHi t) := by
  unfold quantitativeOuterBump
  change WindowTaper
    (smoothWindowRaw (quantitativeTaperOuterCenter t) (quantitativeTaperR t))
    (canonicalOuterLo t) (canonicalOuterHi t)
  have hR : 0 < quantitativeTaperR t := quantitativeTaperR_pos ht
  have hpos : 0 < canonicalOuterLo t := by
    have hgeom := canonical_window_geometry ht
    exact lt_trans hgeom.1 (lt_trans (lt_of_le_of_lt hgeom.2.1 hgeom.2.2) (by
      unfold canonicalOuterLo canonicalInnerHi
        quantitativeTaperOuterCenter quantitativeTaperInnerCenter quantitativeTaperR
      field_simp [ne_of_gt ht]
      nlinarith [Real.pi_pos]))
  unfold canonicalOuterLo canonicalOuterHi
  exact smoothWindowRaw_windowTaper hpos hR

theorem canonicalCrossSignalFloor_pos
    {t a : ℝ} (ht : 18 <= t) (ha : 0 < a) :
    0 < canonicalCrossSignalFloor t a := by
  have ht0 : 0 < t := by linarith
  have hgeom := canonical_window_geometry ht0
  have hinner := canonical_inner_windowTaper ht0
  have houter := canonical_outer_windowTaper ht0
  have houterLo : 0 < canonicalOuterLo t :=
    lt_trans hgeom.1 (lt_trans (lt_of_le_of_lt hgeom.2.1 hgeom.2.2) (le_refl _))
  have harea :
      0 < (canonicalOuterLo t) ^ 2 - (canonicalInnerHi t) ^ 2 := by
    have hinnerHi : 0 < canonicalInnerHi t :=
      lt_of_lt_of_le hgeom.1 hgeom.2.1
    nlinarith [hgeom.2.2]
  have hcosh :
      0 < coshDiff a (canonicalInnerHi t) (canonicalOuterLo t) := by
    have hinnerHi : 0 < canonicalInnerHi t :=
      lt_of_lt_of_le hgeom.1 hgeom.2.1
    exact coshDiff_pos ha hinnerHi hgeom.2.2
  have hmi : 0 < ∫ u : ℝ, quantitativeInnerBump t u := hinner.mass
  have hmo : 0 < ∫ u : ℝ, quantitativeOuterBump t u := houter.mass
  have hlam : 0 < quantitativeLambda t := quantitativeLambda_pos ht
  unfold canonicalCrossSignalFloor
  positivity

theorem canonicalCrossSignalFloor_le_targetLeadingCoeff
    {t a : ℝ} (ht : 18 <= t) (ha : 0 < a) :
    canonicalCrossSignalFloor t a
      <= targetLeadingCoeff (quantitativeCanonicalTaper t) a := by
  have ht0 : 0 < t := by linarith
  have hi := canonical_inner_windowTaper ht0
  have ho := canonical_outer_windowTaper ht0
  have hgeom := canonical_window_geometry ht0

  have hcross :=
    crossIntegral_ge
      hi ho ha
      hgeom.1 hgeom.2.1 hgeom.2.2

  have hcov :
      (3 / 4 : ℝ)
          * (((canonicalOuterLo t) ^ 2 - (canonicalInnerHi t) ^ 2)
            * coshDiff a (canonicalInnerHi t) (canonicalOuterLo t)
            * ((∫ u : ℝ, quantitativeInnerBump t u)
              * ∫ u : ℝ, quantitativeOuterBump t u))
        <= covForm (quantitativeInnerBump t) (quantitativeOuterBump t) a := by
    rw [covForm_eq_crossIntegral'
      hi.cont hi.cpt ho.cont ho.cpt]
    nlinarith [hcross]

  have hselfI :=
    targetLeadingCoeff_nonneg
      hi.cont hi.cpt hi.nonneg a
  have hselfO :=
    targetLeadingCoeff_nonneg
      ho.cont ho.cpt ho.nonneg a
  have hlam0 : 0 <= quantitativeLambda t := (quantitativeLambda_pos ht).le
  have hlam2 : 0 <= quantitativeLambda t ^ 2 := sq_nonneg _

  unfold quantitativeCanonicalTaper
  rw [targetLeadingCoeff_add_smul
    hi.cont hi.cpt ho.cont ho.cpt]
  unfold canonicalCrossSignalFloor
  have hscaled := mul_le_mul_of_nonneg_left hcov
    (mul_nonneg (by norm_num : (0 : ℝ) <= 2) hlam0)
  nlinarith [hscaled, mul_nonneg hlam2 hselfO]

theorem canonical_targetLeadingCoeff_pos
    {t a : ℝ} (ht : 18 <= t) (ha : 0 < a) :
    0 < targetLeadingCoeff (quantitativeCanonicalTaper t) a := by
  exact lt_of_lt_of_le
    (canonicalCrossSignalFloor_pos ht ha)
    (canonicalCrossSignalFloor_le_targetLeadingCoeff ht ha)

end Synthesis
