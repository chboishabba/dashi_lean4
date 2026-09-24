import Zeta23.RvM.Fold
import Zeta23.RvM.GammaSide
import Zeta23.RvM.Backlund
import Zeta23.WeilEF.XiLogDeriv

/-!
# Exact arbitrary-interval RvM decomposition on the literal zeta carrier

The exported Zeta23 `RiemannVonMangoldt.main` field is dyadic because that is
the paper-facing API.  The internal contour proof is stronger: at arbitrary
good heights T1<T2 it identifies the actual zero count with the smooth Gamma
density plus the zeta-log-derivative contour remainder.

This file exposes exactly that stronger theorem on the SAME `Ncount` /
`zetaZeroConfig` used by the normalized RH branch:

  N(T1,T2)
    = integral_[T1,T2] mu
      + (1/pi) Im halfContour(zeta'/zeta).

No new number theory is assumed.  The result is assembled only from the
already-proved Zeta23 Fold, GammaSide, Backlund path regularity, and the exact
completed-zeta log-derivative decomposition.
-/

noncomputable section

open Complex MeasureTheory Set intervalIntegral
open scoped Real

namespace Synthesis

open Zeta23
open Zeta23.RvM

def literalRvMContourRemainder (T1 T2 : ℝ) : ℝ :=
  (1 / Real.pi) *
    (halfContour (logDeriv riemannZeta) T1 T2).im

private theorem gamma_horizontal_intervalIntegrable
    (T : ℝ) :
    IntervalIntegrable
      (fun sigma : ℝ =>
        logDeriv Complex.Gammaℝ (sigma + T * I))
      volume (1 / 2) 2 := by
  have hpath : Continuous
      (fun sigma : ℝ => ((sigma : ℂ) + T * I)) := by
    fun_prop
  have hcontOn : ContinuousOn
      (fun sigma : ℝ =>
        logDeriv Complex.Gammaℝ (sigma + T * I))
      (Set.Icc (1 / 2 : ℝ) 2) := by
    exact
      logDeriv_Gammaℝ_differentiableOn.continuousOn.comp
        hpath.continuousOn
        (by
          intro sigma hsigma
          show 0 < (((sigma : ℂ) + T * I)).re
          simp only [Complex.add_re, Complex.ofReal_re,
            Complex.mul_re, Complex.I_re, Complex.I_im,
            mul_zero, zero_mul, sub_zero]
          linarith [hsigma.1])
  exact hcontOn.intervalIntegrable

private theorem gamma_vertical_intervalIntegrable
    (T1 T2 : ℝ) :
    IntervalIntegrable
      (fun t : ℝ =>
        logDeriv Complex.Gammaℝ (2 + t * I))
      volume T1 T2 := by
  have hpath : Continuous
      (fun t : ℝ => ((2 : ℂ) + t * I)) := by
    fun_prop
  have hcont : Continuous
      (fun t : ℝ =>
        logDeriv Complex.Gammaℝ (2 + t * I)) := by
    exact
      logDeriv_Gammaℝ_differentiableOn.continuousOn.comp_continuous
        hpath
        (by
          intro t
          show 0 < (((2 : ℂ) + t * I)).re
          norm_num)
  exact hcont.intervalIntegrable _ _

private theorem zeta_vertical_intervalIntegrable
    (T1 T2 : ℝ) :
    IntervalIntegrable
      (fun t : ℝ =>
        logDeriv riemannZeta (2 + t * I))
      volume T1 T2 := by
  have hcont : Continuous
      (fun t : ℝ => logDeriv riemannZeta (2 + t * I)) := by
    have hmul :=
      Zeta23.RvM.continuous_logDeriv_riemannZeta_two
    have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
    -- Backlund proves continuity after multiplication by I.  Recover the
    -- unmultipled path by multiplying by -I.
    have hrewrite :
        (fun t : ℝ => logDeriv riemannZeta (2 + t * I))
          =
        fun t : ℝ =>
          (logDeriv riemannZeta (2 + t * I) * I) * (-I) := by
      funext t
      ring
    rw [hrewrite]
    exact hmul.mul continuous_const
  exact hcont.intervalIntegrable _ _

private theorem completed_halfContour_eq_gamma_add_zeta
    {T1 T2 : ℝ}
    (h1 : 1 <= T1) (h12 : T1 < T2)
    (hg1 : GoodHeight T1) (hg2 : GoodHeight T2) :
    halfContour (logDeriv completedRiemannZeta) T1 T2
      =
    halfContour (logDeriv Complex.Gammaℝ) T1 T2
      +
    halfContour (logDeriv riemannZeta) T1 T2 := by
  have hT1ne : T1 ≠ 0 := by linarith
  have hT2ne : T2 ≠ 0 := by linarith
  have hz1 :=
    riemannZeta_ne_zero_on_segment hg1
  have hz2 :=
    riemannZeta_ne_zero_on_segment hg2

  have hbG := gamma_horizontal_intervalIntegrable T1
  have htG := gamma_horizontal_intervalIntegrable T2
  have hvG := gamma_vertical_intervalIntegrable T1 T2
  have hbZ :=
    intervalIntegrable_logDeriv_horizontal hT1ne hz1
      (by constructor <;> norm_num)
      (by constructor <;> norm_num)
  have htZ :=
    intervalIntegrable_logDeriv_horizontal hT2ne hz2
      (by constructor <;> norm_num)
      (by constructor <;> norm_num)
  have hvZ := zeta_vertical_intervalIntegrable T1 T2

  have hadd :=
    halfContour_add
      (logDeriv Complex.Gammaℝ)
      (logDeriv riemannZeta)
      T1 T2 hbG hbZ hvG hvZ htG htZ

  have hbEq :
      (∫ sigma in (1 / 2 : ℝ)..2,
        logDeriv completedRiemannZeta (sigma + T1 * I))
        =
      ∫ sigma in (1 / 2 : ℝ)..2,
        (logDeriv Complex.Gammaℝ (sigma + T1 * I)
          + logDeriv riemannZeta (sigma + T1 * I)) := by
    apply intervalIntegral.integral_congr
    intro sigma hsigma
    have hs : 0 < (((sigma : ℂ) + T1 * I)).re := by
      simp only [Complex.add_re, Complex.ofReal_re,
        Complex.mul_re, Complex.I_re, Complex.I_im,
        mul_zero, zero_mul, sub_zero]
      rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) <= 2)] at hsigma
      linarith [hsigma.1]
    have hs1 : ((sigma : ℂ) + T1 * I) ≠ 1 := by
      intro h
      have him := congrArg Complex.im h
      simp only [Complex.add_im, Complex.ofReal_im,
        Complex.mul_im, Complex.I_re, Complex.I_im,
        mul_one, zero_mul, add_zero, Complex.one_im] at him
      linarith
    exact Zeta23.WeilEF.logDeriv_completedZeta
      _ hs1 (hz1 sigma (by
        rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) <= 2)] at hsigma
        exact hsigma)) hs

  have htEq :
      (∫ sigma in (1 / 2 : ℝ)..2,
        logDeriv completedRiemannZeta (sigma + T2 * I))
        =
      ∫ sigma in (1 / 2 : ℝ)..2,
        (logDeriv Complex.Gammaℝ (sigma + T2 * I)
          + logDeriv riemannZeta (sigma + T2 * I)) := by
    apply intervalIntegral.integral_congr
    intro sigma hsigma
    have hs : 0 < (((sigma : ℂ) + T2 * I)).re := by
      simp only [Complex.add_re, Complex.ofReal_re,
        Complex.mul_re, Complex.I_re, Complex.I_im,
        mul_zero, zero_mul, sub_zero]
      rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) <= 2)] at hsigma
      linarith [hsigma.1]
    have hs1 : ((sigma : ℂ) + T2 * I) ≠ 1 := by
      intro h
      have him := congrArg Complex.im h
      simp only [Complex.add_im, Complex.ofReal_im,
        Complex.mul_im, Complex.I_re, Complex.I_im,
        mul_one, zero_mul, add_zero, Complex.one_im] at him
      linarith
    exact Zeta23.WeilEF.logDeriv_completedZeta
      _ hs1 (hz2 sigma (by
        rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) <= 2)] at hsigma
        exact hsigma)) hs

  have hvEq :
      (∫ t in T1..T2,
        logDeriv completedRiemannZeta (2 + t * I))
        =
      ∫ t in T1..T2,
        (logDeriv Complex.Gammaℝ (2 + t * I)
          + logDeriv riemannZeta (2 + t * I)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have hs : 0 < (((2 : ℂ) + t * I)).re := by norm_num
    have hs1 : ((2 : ℂ) + t * I) ≠ 1 := by
      intro h
      have hre := congrArg Complex.re h
      norm_num at hre
    have hz : riemannZeta (2 + t * I) ≠ 0 :=
      riemannZeta_ne_zero_of_one_le_re (by norm_num)
    exact Zeta23.WeilEF.logDeriv_completedZeta _ hs1 hz hs

  unfold halfContour
  rw [hbEq, hvEq, htEq]
  simpa [halfContour] using hadd

/--
Exact arbitrary-good-height RvM decomposition on the actual zeta zero count.
This is the theorem shape needed before Abel summation.
-/
theorem literal_zeta_count_eq_mu_add_contourRemainder
    {T1 T2 : ℝ}
    (h1 : 1 <= T1) (h12 : T1 < T2)
    (hg1 : GoodHeight T1) (hg2 : GoodHeight T2) :
    (Ncount T1 T2 : ℝ)
      =
    (∫ t in T1..T2, mu t)
      + literalRvMContourRemainder T1 T2 := by
  have hN :=
    Ncount_eq_im_halfContour h1 h12 hg1 hg2
  have hsplit :=
    completed_halfContour_eq_gamma_add_zeta
      h1 h12 hg1 hg2
  rw [hsplit, Complex.add_im] at hN
  have hGamma :=
    gamma_side
      (T1 := T1) (T2 := T2)
      (by linarith) (by linarith)
  unfold literalRvMContourRemainder
  linarith

/--
Consequently the cumulative actual-minus-smooth discrepancy is literally the
zeta log-derivative contour remainder, not a fresh abstract error variable.
-/
theorem literal_zeta_count_sub_mu_eq_contourRemainder
    {T1 T2 : ℝ}
    (h1 : 1 <= T1) (h12 : T1 < T2)
    (hg1 : GoodHeight T1) (hg2 : GoodHeight T2) :
    (Ncount T1 T2 : ℝ) - (∫ t in T1..T2, mu t)
      =
    literalRvMContourRemainder T1 T2 := by
  rw [literal_zeta_count_eq_mu_add_contourRemainder
    h1 h12 hg1 hg2]
  ring

end Synthesis
