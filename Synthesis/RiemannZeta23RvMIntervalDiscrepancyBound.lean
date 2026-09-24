import Synthesis.RiemannZeta23RvMIntervalDiscrepancy

/-!
# Quantitative arbitrary-interval Zeta23 RvM discrepancy

The exact interval decomposition is

  N(T1,T2) - integral_[T1,T2] mu
    = (1/pi) Im halfContour(zeta'/zeta).

Zeta23 already proves:
* each horizontal endpoint contribution is O(log T) at good heights;
* the vertical Re(s)=2 contribution has imaginary part at most pi.

Combining those gives a theorem-bearing cumulative discrepancy bound on the
actual zeta zero count.  This is exactly the analytic shape consumed by the
normalized Abel compiler after endpoint/grid attachment.
-/

noncomputable section

open Complex MeasureTheory intervalIntegral
open scoped Real

namespace Synthesis

open Zeta23
open Zeta23.RvM

theorem literalRvMContourRemainder_abs_le_of_horizontal
    {C T1 T2 : ℝ}
    (hC : 0 <= C)
    (hH1 :
      |(∫ sigma in (1 / 2 : ℝ)..2,
        logDeriv riemannZeta (sigma + T1 * I)).im|
        <= C * Real.log T1)
    (hH2 :
      |(∫ sigma in (1 / 2 : ℝ)..2,
        logDeriv riemannZeta (sigma + T2 * I)).im|
        <= C * Real.log T2) :
    |literalRvMContourRemainder T1 T2|
      <=
    (C * Real.log T1 + Real.pi + C * Real.log T2) / Real.pi := by
  let A1 : ℂ :=
    ∫ sigma in (1 / 2 : ℝ)..2,
      logDeriv riemannZeta (sigma + T1 * I)
  let B : ℂ :=
    ∫ t in T1..T2,
      logDeriv riemannZeta (2 + t * I)
  let A2 : ℂ :=
    ∫ sigma in (1 / 2 : ℝ)..2,
      logDeriv riemannZeta (sigma + T2 * I)

  have hV :
      |(B * I).im| <= Real.pi := by
    dsimp [B]
    exact vertical_two T1 T2

  have hhalf :
      |(halfContour (logDeriv riemannZeta) T1 T2).im|
        <=
      C * Real.log T1 + Real.pi + C * Real.log T2 := by
    have htri1 :
        |A1.im + (B * I).im - A2.im|
          <=
        |A1.im + (B * I).im| + |A2.im| := by
      simpa [sub_eq_add_neg, abs_neg] using
        (abs_add (A1.im + (B * I).im) (-A2.im))
    have htri2 :
        |A1.im + (B * I).im|
          <= |A1.im| + |(B * I).im| :=
      abs_add _ _
    have hA1 : |A1.im| <= C * Real.log T1 := by
      simpa [A1] using hH1
    have hA2 : |A2.im| <= C * Real.log T2 := by
      simpa [A2] using hH2
    unfold halfContour
    dsimp [A1, B, A2] at htri1 htri2 hA1 hA2 hV ⊢
    simp only [Complex.add_im, Complex.sub_im] at htri1 ⊢
    exact le_trans htri1 (by linarith [htri2, hA1, hA2, hV])

  unfold literalRvMContourRemainder
  rw [abs_mul, abs_of_pos (by positivity : 0 < (1 / Real.pi : ℝ))]
  have hpi : 0 < Real.pi := Real.pi_pos
  rw [one_div, inv_mul_eq_div]
  exact (div_le_div_iff₀ hpi).2 (by
    simpa [mul_assoc] using hhalf)

/--
The actual zeta count has a cumulative arbitrary-interval discrepancy of
O(log T1 + log T2) from the exact smooth density mu, at good heights.
-/
theorem literal_zeta_interval_discrepancy_quantitative :
    ∃ C T0 : ℝ, 0 <= C ∧
      ∀ T1 T2 : ℝ,
        max T0 3 <= T1 ->
        T1 < T2 ->
        GoodHeight T1 ->
        GoodHeight T2 ->
        |(Ncount T1 T2 : ℝ) - (∫ t in T1..T2, mu t)|
          <=
        (C * Real.log T1 + Real.pi + C * Real.log T2) / Real.pi := by
  obtain ⟨C0, T0, hBacklund⟩ := backlund_horizontal
  refine ⟨|C0|, T0, abs_nonneg C0, ?_⟩
  intro T1 T2 hT1 h12 hg1 hg2
  have hT2 : max T0 3 <= T2 := le_trans hT1 h12.le
  have hH1raw := hBacklund T1 hT1 hg1
  have hH2raw := hBacklund T2 hT2 hg2
  have hlog1 : 0 <= Real.log T1 := by
    apply Real.log_nonneg
    have h3 : (3 : ℝ) <= T1 :=
      le_trans (le_max_right T0 3) hT1
    linarith
  have hlog2 : 0 <= Real.log T2 := by
    apply Real.log_nonneg
    have h3 : (3 : ℝ) <= T2 :=
      le_trans (le_max_right T0 3) hT2
    linarith
  have hC : C0 <= |C0| := le_abs_self C0
  have hH1 :
      |(∫ sigma in (1 / 2 : ℝ)..2,
        logDeriv riemannZeta (sigma + T1 * I)).im|
        <= |C0| * Real.log T1 :=
    hH1raw.trans (mul_le_mul_of_nonneg_right hC hlog1)
  have hH2 :
      |(∫ sigma in (1 / 2 : ℝ)..2,
        logDeriv riemannZeta (sigma + T2 * I)).im|
        <= |C0| * Real.log T2 :=
    hH2raw.trans (mul_le_mul_of_nonneg_right hC hlog2)
  rw [literal_zeta_count_sub_mu_eq_contourRemainder
    (by
      have h3 : (3 : ℝ) <= T1 :=
        le_trans (le_max_right T0 3) hT1
      linarith)
    h12 hg1 hg2]
  exact literalRvMContourRemainder_abs_le_of_horizontal
    (C := |C0|) (abs_nonneg C0) hH1 hH2

end Synthesis
