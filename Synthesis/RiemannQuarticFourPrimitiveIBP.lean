import Synthesis.RiemannCompactCosineFifthDerivative
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Fourfold integration-by-parts compiler for the RH outer discrepancy

This file is intentionally generic.  Let A be an integrable discrepancy
density on a finite interval and let P1,...,P4 be a primitive ladder

  P1' = A,
  P2' = P1,
  P3' = P2,
  P4' = P3.

For a compact cosine transform C, four integrations by parts give

  ∫ C' A
    = [C' P1]
      - [C'' P2]
      + [C''' P3]
      - [C'''' P4]
      + ∫ C''''' P4.

The theorem is finite-interval and keeps every endpoint term explicit.  It
does not assume anything about zeta-zero discrepancies.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Real

namespace Synthesis

def fourfoldIBPBoundary
    (C1 C2 C3 C4 P1 P2 P3 P4 : ℝ → ℝ)
    (a b : ℝ) : ℝ :=
  (C1 b * P1 b - C1 a * P1 a)
    - (C2 b * P2 b - C2 a * P2 a)
    + (C3 b * P3 b - C3 a * P3 a)
    - (C4 b * P4 b - C4 a * P4 a)

theorem compactCosineD1_continuous
    {P : ℝ → ℝ}
    (hP : Continuous P)
    (hPc : HasCompactSupport P) :
    Continuous (compactCosineD1 P) := by
  apply continuous_iff_continuousAt.2
  intro q
  exact (compactCosineD1_deriv hP hPc q).continuousAt

theorem compactCosineD2_continuous
    {P : ℝ → ℝ}
    (hP : Continuous P)
    (hPc : HasCompactSupport P) :
    Continuous (compactCosineD2 P) := by
  apply continuous_iff_continuousAt.2
  intro q
  exact (compactCosineD2_deriv hP hPc q).continuousAt

theorem compactCosineD3_continuous
    {P : ℝ → ℝ}
    (hP : Continuous P)
    (hPc : HasCompactSupport P) :
    Continuous (compactCosineD3 P) := by
  apply continuous_iff_continuousAt.2
  intro q
  exact (compactCosineD3_deriv hP hPc q).continuousAt

theorem compactCosineD1_fourfold_ibp
    {P A P1 P2 P3 P4 : ℝ → ℝ}
    {a b : ℝ}
    (hP : Continuous P)
    (hPc : HasCompactSupport P)
    (hA : IntervalIntegrable A volume a b)
    (hP1 : Continuous P1)
    (hP2 : Continuous P2)
    (hP3 : Continuous P3)
    (hP4 : Continuous P4)
    (hP1' : ∀ x : ℝ, HasDerivAt P1 (A x) x)
    (hP2' : ∀ x : ℝ, HasDerivAt P2 (P1 x) x)
    (hP3' : ∀ x : ℝ, HasDerivAt P3 (P2 x) x)
    (hP4' : ∀ x : ℝ, HasDerivAt P4 (P3 x) x) :
    (∫ q in a..b, compactCosineD1 P q * A q)
      =
    fourfoldIBPBoundary
      (compactCosineD1 P)
      (compactCosineD2 P)
      (compactCosineD3 P)
      (compactCosineD4 P)
      P1 P2 P3 P4 a b
      +
    ∫ q in a..b, compactCosineD5 P q * P4 q := by
  have hC2 :
      IntervalIntegrable (compactCosineD2 P) volume a b :=
    (compactCosineD2_continuous hP hPc).intervalIntegrable a b
  have hC3 :
      IntervalIntegrable (compactCosineD3 P) volume a b :=
    (compactCosineD3_continuous hP hPc).intervalIntegrable a b
  have hC4 :
      IntervalIntegrable (compactCosineD4 P) volume a b :=
    (compactCosineD4_continuous hP hPc).intervalIntegrable a b
  have hC5 :
      IntervalIntegrable (compactCosineD5 P) volume a b :=
    (compactCosineD5_continuous hP hPc).intervalIntegrable a b
  have hP1i : IntervalIntegrable P1 volume a b :=
    hP1.intervalIntegrable a b
  have hP2i : IntervalIntegrable P2 volume a b :=
    hP2.intervalIntegrable a b
  have hP3i : IntervalIntegrable P3 volume a b :=
    hP3.intervalIntegrable a b
  have hP4i : IntervalIntegrable P4 volume a b :=
    hP4.intervalIntegrable a b

  have h1 :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (u:=compactCosineD1 P) (v:=P1)
      (u':=compactCosineD2 P) (v':=A)
      (fun x hx => compactCosineD1_deriv hP hPc x)
      (fun x hx => hP1' x)
      hC2 hA
  have h2 :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (u:=compactCosineD2 P) (v:=P2)
      (u':=compactCosineD3 P) (v':=P1)
      (fun x hx => compactCosineD2_deriv hP hPc x)
      (fun x hx => hP2' x)
      hC3 hP1i
  have h3 :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (u:=compactCosineD3 P) (v:=P3)
      (u':=compactCosineD4 P) (v':=P2)
      (fun x hx => compactCosineD3_deriv hP hPc x)
      (fun x hx => hP3' x)
      hC4 hP2i
  have h4 :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (u:=compactCosineD4 P) (v:=P4)
      (u':=compactCosineD5 P) (v':=P3)
      (fun x hx => compactCosineD4_deriv hP hPc x)
      (fun x hx => hP4' x)
      hC5 hP3i

  unfold fourfoldIBPBoundary
  linarith


theorem compactCosineD1_contDiff_one
    {P : ℝ → ℝ}
    (hP : Continuous P)
    (hPc : HasCompactSupport P) :
    ContDiff ℝ 1 (compactCosineD1 P) := by
  rw [contDiff_one_iff_deriv]
  constructor
  · intro q
    exact (compactCosineD1_deriv hP hPc q).differentiableAt
  · have hderiv :
        deriv (compactCosineD1 P) = compactCosineD2 P := by
      funext q
      exact (compactCosineD1_deriv hP hPc q).deriv
    rw [hderiv]
    exact compactCosineD2_continuous hP hPc

theorem compactCosineD2_contDiff_one
    {P : ℝ → ℝ}
    (hP : Continuous P)
    (hPc : HasCompactSupport P) :
    ContDiff ℝ 1 (compactCosineD2 P) := by
  rw [contDiff_one_iff_deriv]
  constructor
  · intro q
    exact (compactCosineD2_deriv hP hPc q).differentiableAt
  · have hderiv :
        deriv (compactCosineD2 P) = compactCosineD3 P := by
      funext q
      exact (compactCosineD2_deriv hP hPc q).deriv
    rw [hderiv]
    exact compactCosineD3_continuous hP hPc

theorem compactCosineD3_contDiff_one
    {P : ℝ → ℝ}
    (hP : Continuous P)
    (hPc : HasCompactSupport P) :
    ContDiff ℝ 1 (compactCosineD3 P) := by
  rw [contDiff_one_iff_deriv]
  constructor
  · intro q
    exact (compactCosineD3_deriv hP hPc q).differentiableAt
  · have hderiv :
        deriv (compactCosineD3 P) = compactCosineD4 P := by
      funext q
      exact (compactCosineD3_deriv hP hPc q).deriv
    rw [hderiv]
    exact compactCosineD4_continuous hP hPc

theorem compactCosineD4_contDiff_one
    {P : ℝ → ℝ}
    (hP : Continuous P)
    (hPc : HasCompactSupport P) :
    ContDiff ℝ 1 (compactCosineD4 P) := by
  rw [contDiff_one_iff_deriv]
  constructor
  · intro q
    exact (compactCosineD4_deriv hP hPc q).differentiableAt
  · have hderiv :
        deriv (compactCosineD4 P) = compactCosineD5 P := by
      funext q
      exact (compactCosineD4_deriv hP hPc q).deriv
    rw [hderiv]
    exact compactCosineD5_continuous hP hPc

/--
Absolutely-continuous fourfold integration by parts.

This version is designed for the Riemann--von Mangoldt staircase. The first
primitive P1 need only be absolutely continuous; the input appears through
its actual derivative, so jumps of the original discrepancy cause no false
pointwise differentiability obligation. The higher primitives are likewise
AC, with their derivative identities supplied separately.
-/
theorem compactCosineD1_fourfold_ibp_ac
    {P P1 P2 P3 P4 : ℝ → ℝ}
    {a b : ℝ}
    (hP : Continuous P)
    (hPc : HasCompactSupport P)
    (hP1ac : AbsolutelyContinuousOnInterval P1 a b)
    (hP2ac : AbsolutelyContinuousOnInterval P2 a b)
    (hP3ac : AbsolutelyContinuousOnInterval P3 a b)
    (hP4ac : AbsolutelyContinuousOnInterval P4 a b)
    (hP2' : ∀ x : ℝ, deriv P2 x = P1 x)
    (hP3' : ∀ x : ℝ, deriv P3 x = P2 x)
    (hP4' : ∀ x : ℝ, deriv P4 x = P3 x) :
    (∫ q in a..b, compactCosineD1 P q * deriv P1 q)
      =
    fourfoldIBPBoundary
      (compactCosineD1 P)
      (compactCosineD2 P)
      (compactCosineD3 P)
      (compactCosineD4 P)
      P1 P2 P3 P4 a b
      +
    ∫ q in a..b, compactCosineD5 P q * P4 q := by
  have hC1ac :
      AbsolutelyContinuousOnInterval (compactCosineD1 P) a b :=
    (compactCosineD1_contDiff_one hP hPc).contDiffOn
      .absolutelyContinuousOnInterval
  have hC2ac :
      AbsolutelyContinuousOnInterval (compactCosineD2 P) a b :=
    (compactCosineD2_contDiff_one hP hPc).contDiffOn
      .absolutelyContinuousOnInterval
  have hC3ac :
      AbsolutelyContinuousOnInterval (compactCosineD3 P) a b :=
    (compactCosineD3_contDiff_one hP hPc).contDiffOn
      .absolutelyContinuousOnInterval
  have hC4ac :
      AbsolutelyContinuousOnInterval (compactCosineD4 P) a b :=
    (compactCosineD4_contDiff_one hP hPc).contDiffOn
      .absolutelyContinuousOnInterval

  have h1 := hC1ac.integral_mul_deriv_eq_deriv_mul hP1ac
  have h2 := hC2ac.integral_mul_deriv_eq_deriv_mul hP2ac
  have h3 := hC3ac.integral_mul_deriv_eq_deriv_mul hP3ac
  have h4 := hC4ac.integral_mul_deriv_eq_deriv_mul hP4ac

  have hd1 :
      deriv (compactCosineD1 P) = compactCosineD2 P := by
    funext q
    exact (compactCosineD1_deriv hP hPc q).deriv
  have hd2 :
      deriv (compactCosineD2 P) = compactCosineD3 P := by
    funext q
    exact (compactCosineD2_deriv hP hPc q).deriv
  have hd3 :
      deriv (compactCosineD3 P) = compactCosineD4 P := by
    funext q
    exact (compactCosineD3_deriv hP hPc q).deriv
  have hd4 :
      deriv (compactCosineD4 P) = compactCosineD5 P := by
    funext q
    exact (compactCosineD4_deriv hP hPc q).deriv

  rw [hd1] at h1
  rw [hd2, hP2'] at h2
  rw [hd3, hP3'] at h3
  rw [hd4, hP4'] at h4

  unfold fourfoldIBPBoundary
  linarith

end Synthesis
