import Synthesis.RiemannCompactCosineFifthDerivative
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

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

end Synthesis
