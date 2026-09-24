import Zeta23.RvM.MainTerm
import Synthesis.RiemannRvMMuGammaEvenConeWeld
import Synthesis.RiemannNormalizedCountingAbelCompiler

/-!
# Arbitrary-good-height RvM discrepancy against the exact mu measure

For good heights 1 <= T1 < T2, the upstream contour machinery gives exactly

  N(T1,T2)
    = (1/pi) Im halfContour(logDeriv completedZeta; T1,T2),

the completed-zeta half contour splits into zeta + Gamma_R, and the Gamma_R
piece is exactly

  (1/pi) Im halfContour(logDeriv Gamma_R) = integral_{T1}^{T2} mu.

Therefore

  N(T1,T2) - integral_{T1}^{T2} mu
    = (1/pi) Im halfContour(logDeriv zeta; T1,T2).

Backlund bounds the two horizontal sides by C log(T1), C log(T2), while the
vertical side Re(s)=2 has absolute imaginary part <= pi.

This file packages the resulting arbitrary-window cumulative discrepancy.  It is
the theorem species required by the normalized Abel consumer and is strictly
stronger for that purpose than the already-exported dyadic RvM corollary.
-/

noncomputable section

open MeasureTheory Complex
open scoped Real

namespace Synthesis

open Zeta23
open Zeta23.RvM

def zetaMuWindowDiscrepancy (T1 T2 : ℝ) : ℝ :=
  (zetaZeroConfig.N T1 T2 : ℝ) - ∫ tau in T1..T2, Zeta23.mu tau

theorem zetaMuWindowDiscrepancy_eq_zetaHalfContour
    {T1 T2 : ℝ}
    (h1 : 1 <= T1)
    (h12 : T1 < T2)
    (hg1 : GoodHeight T1)
    (hg2 : GoodHeight T2) :
    zetaMuWindowDiscrepancy T1 T2
      =
    (1 / Real.pi)
      * (halfContour (logDeriv riemannZeta) T1 T2).im := by
  have hN :=
    N_eq_halfContour_completedZeta h1 h12 hg1 hg2
  have hsplit :=
    halfContour_completedZeta_split h1 h12 hg1 hg2
  have hgamma :=
    gamma_side
      (T1 := T1) (T2 := T2)
      (by linarith) (by linarith)
  unfold zetaMuWindowDiscrepancy
  rw [hN, hsplit, Complex.add_im]
  linarith

theorem zetaHalfContour_im_abs_le
    {CB TB T1 T2 : ℝ}
    (hB : ∀ T : ℝ, TB <= T -> GoodHeight T ->
      |(∫ sigma in (1 / 2 : ℝ)..2,
        logDeriv riemannZeta (sigma + T * I)).im|
        <= CB * Real.log T)
    (hTB1 : TB <= T1)
    (hTB2 : TB <= T2)
    (h1 : 1 <= T1)
    (h12 : T1 < T2)
    (hg1 : GoodHeight T1)
    (hg2 : GoodHeight T2) :
    |(halfContour (logDeriv riemannZeta) T1 T2).im|
      <=
    |CB| * Real.log T1
      + Real.pi
      + |CB| * Real.log T2 := by
  have hlog1 : 0 <= Real.log T1 :=
    Real.log_nonneg h1
  have hlog2 : 0 <= Real.log T2 :=
    Real.log_nonneg (by linarith)
  have hb1raw := hB T1 hTB1 hg1
  have hb2raw := hB T2 hTB2 hg2
  have hb1 :
      |(∫ sigma in (1 / 2 : ℝ)..2,
        logDeriv riemannZeta (sigma + T1 * I)).im|
        <= |CB| * Real.log T1 := by
    exact hb1raw.trans
      (mul_le_mul_of_nonneg_right (le_abs_self CB) hlog1)
  have hb2 :
      |(∫ sigma in (1 / 2 : ℝ)..2,
        logDeriv riemannZeta (sigma + T2 * I)).im|
        <= |CB| * Real.log T2 := by
    exact hb2raw.trans
      (mul_le_mul_of_nonneg_right (le_abs_self CB) hlog2)
  have hv := Zeta23.RvM.vertical_two T1 T2
  have hmulI :
      ((∫ tau in T1..T2,
        logDeriv riemannZeta (2 + tau * I)) * I).im
      =
      (∫ tau in T1..T2,
        logDeriv riemannZeta (2 + tau * I) * I).im := by
    exact congrArg Complex.im
      (intervalIntegral.integral_mul_const
        (mu := MeasureTheory.volume) I
        (fun tau : ℝ =>
          logDeriv riemannZeta (2 + tau * I))).symm
  unfold halfContour
  rw [Complex.sub_im, Complex.add_im, hmulI]
  calc
    |(∫ sigma in (1 / 2 : ℝ)..2,
        logDeriv riemannZeta (sigma + T1 * I)).im
      +
      (∫ tau in T1..T2,
        logDeriv riemannZeta (2 + tau * I) * I).im
      -
      (∫ sigma in (1 / 2 : ℝ)..2,
        logDeriv riemannZeta (sigma + T2 * I)).im|
      <=
    |(∫ sigma in (1 / 2 : ℝ)..2,
        logDeriv riemannZeta (sigma + T1 * I)).im|
      +
    |(∫ tau in T1..T2,
        logDeriv riemannZeta (2 + tau * I) * I).im|
      +
    |(∫ sigma in (1 / 2 : ℝ)..2,
        logDeriv riemannZeta (sigma + T2 * I)).im| := by
      exact (abs_sub _ _).trans
        (add_le_add (abs_add_le _ _) le_rfl)
    _ <=
      |CB| * Real.log T1 + Real.pi
        + |CB| * Real.log T2 := by
      linarith

/--
The exact theorem-bearing arbitrary-good-height cumulative discrepancy:

  |N(T1,T2) - integral mu|
    <= (1/pi) * (|CB| log T1 + pi + |CB| log T2).

The constants are inherited from the already-proved Backlund theorem.
-/
theorem exists_zetaMuWindowDiscrepancy_bound :
    ∃ CB TB : ℝ, ∀ T1 T2 : ℝ,
      max TB 1 <= T1 ->
      T1 < T2 ->
      GoodHeight T1 ->
      GoodHeight T2 ->
      |zetaMuWindowDiscrepancy T1 T2|
        <=
      (1 / Real.pi)
        * (|CB| * Real.log T1
          + Real.pi
          + |CB| * Real.log T2) := by
  obtain ⟨CB, TB, hB⟩ := Zeta23.RvM.backlund_horizontal
  refine ⟨CB, TB, ?_⟩
  intro T1 T2 hT1 h12 hg1 hg2
  have h1 : 1 <= T1 := (le_max_right TB 1).trans hT1
  have hTB1 : TB <= T1 := (le_max_left TB 1).trans hT1
  have hTB2 : TB <= T2 := le_trans hTB1 h12.le
  have hEq :=
    zetaMuWindowDiscrepancy_eq_zetaHalfContour
      h1 h12 hg1 hg2
  have hHC :=
    zetaHalfContour_im_abs_le
      hB hTB1 hTB2 h1 h12 hg1 hg2
  rw [hEq, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.pi)]
  exact mul_le_mul_of_nonneg_left hHC (by positivity)

end Synthesis
